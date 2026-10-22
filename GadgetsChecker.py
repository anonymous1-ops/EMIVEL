from contextlib import ExitStack
from collections import Counter
from copy import copy
from fractions import Fraction
from functools import cmp_to_key
from itertools import combinations, product
from math import comb, exp, gcd, log, log2, nextafter, prod
from multiprocessing import Pool, cpu_count
from re import escape, compile
from tempfile import TemporaryFile
import os
import pickle
import time
import psutil
from sympy import symbols, flatten, Add, sympify, Integer, Mul, Symbol
from sympy.logic.boolalg import Xor, Not
from auxiliary import EncodedXor, sympyGF2N, sympyGFp
from GadgetsAnalysis import LeakageAnalyzer
from Parameters import ObservationPlan
import MIA

_worker_instance = None
_worker_start_time = None


class Verifier:

    def __init__(self, gadget, event=None):
        self.gadget = gadget
        self.event = event
        self.MIA = MIA.MIA(self)
        self._phase = "check"
        self._executing_task = False
        self._request_results = None
        self._pending_requests = None
        self._unresolved_cache = {}
        self._resource_process = None
        self._static_cache = None
        self._batch_units = {}
        self._proof_only = False
        self._symbolic_cache = {}
        self._symbolic_serial = 0
        self._substitution_steps = None
        self.MImatrix = {}
        self.leakage = []
        self.observation_cache = {}
        self.exact_zero_cache = {}
        self.mi_text_cache = {}
        self.choice_rpe_cache = {}
        self.rpe_witness_cache = {}
        self.Ci = 0
        self.Ci_list = []
        self.processed_count = 0
        self._check_stop_reason = None
        self._result_counts = {"safe": 0, "insecure": 0, "unknown": 0}
        self._reset_observation()

    def initialize(self):
        model = self.gadget.checkOptions["security"]
        robust = self.gadget.checkOptions["robust"]
        LeakageAnalyzer.validate_options(robust, model=model)
        if model in ("rps_secret", "rps_share", "rpc", "rpe") and (
            getattr(self.gadget, "random_wire_channels", None) is not None
            or (getattr(self.gadget, "random_channel_metadata", None) or {}).get("robust")
            or any(";" in expression for expression in getattr(self.gadget, "expressions", ()))
            or any(instruction.extensions for instruction in getattr(self.gadget, "instructions", ()))
        ):
            raise ValueError("Random probing supports only standard stable-value observations")
        self._reset_observation()
        self.MIA.gadget = self.gadget
        self.gadget.row_mi = {}
        self.gadget.row_verdict = {}
        self.gadget.row_mi_text = {}
        self.gadget.verification_result = None
        self.processed_count = 0
        self.t = self.gadget.checkOptions["threshold"]
        self.model_str = model
        self.randomprobing = False
        self.leakage = []
        if self.model_str in ["rpc", "rpe", "rps_secret", "rps_share"]:
            self.randomprobing = True
        self.tech = ("mi", "static", "both").index(self.gadget.checkOptions["tech."])
        self._unresolved_cache = {}
        self._static_cache = None if self.tech == 0 else {
            "text": {}, "normalized": {}, "counts": {}, "costs": {}, "sources": ({}, {}),
        }
        self._batch_units = {}
        self.__dict__.pop("_affine_prefix_state", None)
        self.__dict__.pop("_symbolic_prefix_state", None)
        self.__dict__.pop("_symbolic_prefix_plans", None)
        self.__dict__.pop("_quadratic_proof_state", None)
        self._symbolic_cache = {}
        self._symbolic_serial = 0
        self._substitution_steps = None
        if self.tech == 0 or self.tech == 2:
            self.MIA.initialize()
        self.HW = "hw_sumed" in robust or "hw_vector" in robust
        self.logic = self.gadget.logic
        if not self.logic:
            from galois import GF

            self.GF_field = GF(self.gadget.field)
        self.abort = {"f": False, "t": True}[self.gadget.checkOptions["abort"]]
        self.detail = {"f": False, "t": True}[self.gadget.checkOptions["detail"]]
        watch = set(map(str, self.gadget.checkOptions.get("watch", ())))
        self._live_detail = (
            not self.randomprobing and self.event is not None and (self.detail or bool(watch))
        )
        self._watch_locations = set()
        if self._live_detail and watch:
            locations = set(getattr(self.gadget, "probe_locations", {}).values())
            matched = set()
            for location in locations:
                row, lhs = location
                matches = watch.intersection((str(row), lhs) if row is not None else (lhs,))
                if matches:
                    self._watch_locations.add(location)
                    matched.update(matches)
            if watch - matched:
                self.event(
                    "warning",
                    {
                        "message": "--watch: no observable position matches these lines or variables: "
                        + ", ".join(sorted(watch - matched))
                    },
                )
        self.toFile = {"f": False, "t": True}[self.gadget.checkOptions["toFile"]]
        self.mcore = self.gadget.checkOptions["mcore"]
        self.max_hours = self.gadget.checkOptions["maxhours"]
        self.max_mem = self.gadget.checkOptions["maxmem"]
        self.secrets = self.gadget.secrets
        self.len_secrets = len(self.secrets)
        self.OutputProbe = self.gadget.observationsOutput
        self.row2Probe = self.gadget.mapRow2Obs
        self.randoms = self.gadget.randoms
        self.compiled_patterns_random = {} if self.tech == 0 else {
            random: compile(f"(?<!\\w){escape(random)}(?!\\w)")
            for random in map(str, self.randoms)
        }
        self.Bits = self.gadget.bits
        self.shareNum = self.gadget.shareNum
        self.checklist = self.gadget.observationsCheck
        self.checksize = self.gadget.checksize
        self.O_inIndex = self.gadget.shareIndex
        if self.randomprobing:
            self.rp_metadata = self.checklist[0]
            self.rp_enumerate_orders = [True] + [
                not isinstance(order, int) for order in self.checklist[1:]
            ]
        sharesIn = self.gadget.secretsInputs
        sharesInBits = self.gadget.secretsInputsBits
        self.bits_sharesNum = self.Bits * self.shareNum
        if model in ("probing_secret", "rps_secret"):
            sharesIn = self.gadget.secrets
            sharesInBits = self.gadget.secretsBits
            self.bits_sharesNum = self.Bits
        self.shares = sharesInBits if self.Bits > 1 else sharesIn
        self.len_shares = len(self.shares)
        self.shares_set = set(self.shares)
        self.len_shares_set = len(self.shares_set)
        self.len_secrets = (
            self.len_shares_set // self.bits_sharesNum
            if self.len_secrets == 0
            else self.len_secrets
        )
        self._empty_rpe_indices = (
            tuple(() for _ in range(self.len_secrets)) if self.randomprobing else ()
        )
        sharesOut = self.gadget.secretsOutputs
        sharesOutBits = self.gadget.secretsOutputsBits
        self.shares_op = sharesOutBits if self.Bits > 1 else sharesOut
        self.len_shares_op = len(self.shares_op)
        self.funcMapping = {id: id // self.bits_sharesNum for id in range(self.len_shares)}
        if not self.funcMapping:
            raise RuntimeError("probably no secret.")
        firstIndex = min(self.O_inIndex)
        self.funcMapping_index = {
            id: id // self.Bits % self.shareNum + firstIndex for id in range(self.len_shares)
        }
        self.funcMapping_index_op = {
            id: id // self.Bits % self.shareNum + firstIndex for id in range(self.len_shares_op)
        }
        if isinstance(self.mcore, int) and self.mcore > cpu_count():
            if self.event is not None:
                self.event(
                    "warning",
                    {
                        "message": "Requested workers exceed the logical CPU count; using %s."
                        % cpu_count()
                    },
                )
            self.mcore = cpu_count()
        self.MImatrix = dict()
        self.observation_cache = dict()
        self.exact_zero_cache = dict()
        self.mi_text_cache = dict()
        self.choice_rpe_cache = dict()
        self.rpe_witness_cache = {}
        if self.randomprobing:
            self._initialize_random_statistics()
        self._share_locations = {
            symbol: (self.funcMapping[position], self.funcMapping_index[position])
            for (symbol, position) in self.shares.items()
        }
        positions = {
            location: 1 << index
            for index, location in enumerate(dict.fromkeys(self._share_locations.values()))
        }
        self._share_bits = {symbol: positions[location] for symbol, location in self._share_locations.items()}
        self._family_bits = tuple(
            sum(bit for (family, _), bit in positions.items() if family == index)
            for index in range(self.len_secrets)
        )
        self._index_bits = {
            index: 1 << position
            for position, index in enumerate(sorted({index for _, index in positions}))
        }

    def __getstate__(self):
        state = self.__dict__.copy()
        state["event"] = None
        state["_request_results"] = None
        state["_pending_requests"] = None
        state["_unresolved_cache"] = {}
        state["_resource_process"] = None
        state["_batch_units"] = {}
        state.pop("_affine_prefix_state", None)
        state.pop("_prefix_witness", None)
        state.pop("_symbolic_prefix_state", None)
        state.pop("_symbolic_prefix_plans", None)
        state.pop("_quadratic_proof_state", None)
        state["_symbolic_cache"] = {}
        state["_symbolic_serial"] = 0
        state["_substitution_steps"] = None
        if state["_static_cache"] is not None:
            state["_static_cache"] = {
                "text": {}, "normalized": {}, "counts": {}, "costs": {}, "sources": ({}, {}),
            }
        state["_watch_locations"] = set()
        circuit = copy(self.gadget)
        circuit.instructions = ()
        circuit.__dict__.pop("expression_info", None)
        circuit.__dict__.pop("probe_locations", None)
        circuit.__dict__.pop("random_wire_locations", None)
        state["gadget"] = circuit
        quantifier = copy(self.MIA)
        quantifier._affine_cache = {}
        quantifier._evaluation_cache = {}
        quantifier._conditioning_cache = None
        quantifier._reuse_evaluation = False
        quantifier.gadget = circuit
        if getattr(quantifier.model, "__self__", None) is self.MIA:
            quantifier.model = quantifier.model.__func__.__get__(quantifier, type(quantifier))
        state["MIA"] = quantifier
        return state

    def run(self):
        self.processed_count = 0
        self._check_stop_reason = None
        self._result_counts = {"safe": 0, "insecure": 0, "unknown": 0}
        start_time = time.time()
        self._batching = False
        self._batch_units = {}
        self._random_wire_groups = ()
        if self.randomprobing:
            self._initialize_random_statistics()
            size = len(self.gadget.observationsIn)
            wires = range(size)
            orders = tuple(
                (order for (order, enabled) in enumerate(self.rp_enumerate_orders) if enabled)
            )
            total = sum((comb(size, order) for order in orders))
            tasks = (
                (order, item, None, None)
                for order in orders
                for item in combinations(wires, order)
            )
        else:
            total = self.checksize
            tasks = ((0, item, None, None) for item in self.checklist)
        if self.randomprobing and not self.abort and not self._live_detail:
            classes = {}
            for position, value in enumerate(self.gadget.observationsIn):
                classes.setdefault(value, []).append(position)
            if len(classes) < size:
                self._random_wire_groups = tuple(tuple(group) for group in classes.values())
                self._batching = True
                tasks = (
                    (order, item, None, None, (selection, weight))
                    for order, item, selection, weight in ObservationPlan(wires, orders).weighted(
                        self._random_wire_groups
                    )
                )
                if self.tech != 0:
                    tasks = (
                        (order, prefix, members, "weighted_family")
                        for order, prefix, members in ObservationPlan(wires, orders).batches(
                            maximum=32, groups=self._random_wire_groups
                        )
                    )
        if (
            self.tech != 0 and not self.abort and not self._watch_locations
            and not self._random_wire_groups
        ):
            plan = ObservationPlan(range(size), orders) if self.randomprobing else self.checklist
            if isinstance(plan, ObservationPlan) and not plan.flatten:
                self._batching = True
                tasks = (
                    (order, prefix, tails, "family")
                    for order, prefix, tails in plan.batches(maximum=24, tail_order=2)
                )
        with ExitStack() as resources:
            pool = None
            if self.mcore > 0:
                initargs = (self, start_time)
                if not self.logic:
                    initargs = (
                        pickle.dumps(self, protocol=pickle.HIGHEST_PROTOCOL),
                        start_time,
                        int(self.gadget.field),
                    )
                pool = resources.enter_context(
                    Pool(
                        processes=self.mcore,
                        initializer=Verifier._init_worker,
                        initargs=initargs,
                    )
                )
            if self.tech == 2 and (not self.abort):
                with TemporaryFile(mode="w+b") as pending:
                    self._phase = "static"
                    pending_count, pending_weight = self._process_observations(
                        tasks, total, start_time, spool=pending, pool=pool
                    )
                    if pending_count and self._check_stop_reason is None:
                        pending.seek(0)
                        self._phase = "mi"
                        tasks = (
                            task
                            for _ in range((pending_count + 127) // 128)
                            for task in pickle.load(pending)
                        )
                        self._process_observations(tasks, pending_weight, start_time, pool=pool)
            else:
                self._phase = "check"
                self._process_observations(tasks, total, start_time, pool=pool)
        self._phase = "check"
        if self.randomprobing:
            return self._random_result()
        complete = self.processed_count == self.checksize
        counts = dict(self._result_counts)
        result = {
            "verdict": (
                "insecure"
                if counts["insecure"]
                else (
                    "incomplete" if not complete else "unknown" if counts["unknown"] else "safe"
                )
            ),
            "complete": complete,
            "processed_count": self.processed_count,
            "checksize": self.checksize,
            "stop_reason": self._check_stop_reason,
            "counts": counts,
            "independence_decision": "static_proof_or_exact_integer_counts_or_finite_field_ranks",
            "mi_numeric": "finite_precision_from_exact_counts_or_finite_field_ranks",
            "mi_normalization": self.MIA.MI_norm,
            "xor_encoding": "bitwise_integer",
            "aggregation": "positive_numeric_mi_only",
            "observations_scope": "retained_since_initialization",
            "observations": [
                {
                    "row": str(row),
                    "mi": value,
                    "mi_text": self.gadget.row_mi_text.get(row),
                    "status": self.gadget.row_verdict.get(row, "unknown"),
                    "exact_zero": (
                        False if self.gadget.row_verdict.get(row) == "insecure" else None
                    ),
                }
                for (row, value) in self.gadget.row_mi.items()
            ],
        }
        if self.model_str == "probing_share":
            result.update(
                security_property="probing_share",
                simulation_share_budget=self.shareNum - 1,
                simulation_input_domain="independent_input_shares",
                mi_quantity="minimum_conditional_mutual_information",
            )
        if (
            complete
            and any((mi > 0 for mi in self.MImatrix))
            and (self.model_str == "probing_secret")
            and (not self.HW)
            and ("transitionxor" not in self.gadget.checkOptions["robust"])
            and (self.tech != 1)
        ):
            self.P = set(self.leakage)
            if self.P:
                result["total_mi"] = self.MIA.compute()
        self.gadget.verification_result = result
        return result

    def _process_observations(self, tasks, total, start_time, pool=None, spool=None):
        pending_count = 0
        pending_weight = 0
        pending_block = []

        def members(packets):
            for packet in packets:
                for result in packet.get("family_results", (packet,)):
                    if (
                        "wire_group_counts" not in result or result.get("verify", True)
                        or not result.get("processed", True) or "deferred" in result
                        or result["batch_count"] == 1
                    ):
                        yield result
                        continue
                    selection = result["wire_group_counts"]
                    group, count = selection[0]
                    stack = [iter(combinations(self._random_wire_groups[group], count))]
                    blocks = []
                    while stack:
                        try:
                            block = next(stack[-1])
                        except StopIteration:
                            stack.pop()
                            if blocks:
                                blocks.pop()
                            continue
                        if len(stack) < len(selection):
                            blocks.append(block)
                            group, count = selection[len(stack)]
                            stack.append(iter(combinations(self._random_wire_groups[group], count)))
                            continue
                        reason = self._limit_reason(start_time)
                        if reason:
                            yield {"processed": False, "abort": None, "stop_reason": reason}
                            return
                        row = tuple(sorted(wire for part in (*blocks, block) for wire in part))
                        sampled = [self.gadget.observationsIn[wire] for wire in row]
                        member = {
                            key: value for key, value in result.items()
                            if key not in ("wire_group_counts", "batch_count")
                        }
                        member["row"] = member["wire_indices"] = row
                        member["requests"] = [
                            {**check, "leakage": sampled + check["leakage"][result["Ci"]:]}
                            if check["failed"] else check
                            for check in result["requests"]
                        ]
                        yield member

        if self.event is not None:
            self.event("progress_start", {"total": total, "phase": self._phase})
        try:
            if pool is not None:
                chunksize = (
                    1 if self.abort or self._random_wire_groups else
                    min(64, max(1, total // (self.mcore * 12800)))
                    if self._batching and self._phase != "mi" else
                    min(5000, max(1, total // (self.mcore * 200)))
                )
                phase = self._phase
                work = ((phase, task) for task in tasks)
                results = pool.imap_unordered(
                    Verifier._check_observation_worker, work, chunksize=chunksize
                )
            elif self._phase == "check" and not self.randomprobing and (
                self.tech == 0 or self.abort or self._watch_locations
                or not isinstance(self.checklist, ObservationPlan) or self.checklist.flatten
            ):
                results = (
                    self.verify_observation(item, start_time)
                    for _, item, _, _ in tasks
                )
            else:
                results = (self._check_task(task, start_time) for task in tasks)
            for result in members(results):
                if "deferred" in result:
                    task = result["deferred"]
                    for key, residual in task[3].items():
                        retained = self._unresolved_cache.get(key)
                        if retained is None:
                            if len(self._unresolved_cache) >= 4096:
                                self._unresolved_cache.clear()
                            self._unresolved_cache[key] = residual
                        else:
                            task[3][key] = retained
                    pending_block.append(task)
                    if len(pending_block) == 128:
                        pickle.dump(tuple(pending_block), spool, protocol=pickle.HIGHEST_PROTOCOL)
                        pending_block.clear()
                    pending_count += 1
                    pending_weight += result.get("batch_count", 1)
                self._record_result(result)
                if self.event is not None and result.get("processed", True):
                    self.event("progress", {"advance": result.get("batch_count", 1)})
                if result["abort"] is None:
                    if pool is not None:
                        pool.terminate()
                    break
            if pending_block:
                pickle.dump(tuple(pending_block), spool, protocol=pickle.HIGHEST_PROTOCOL)
        finally:
            if self.event is not None:
                self.event("progress_end", {})
        return pending_count, pending_weight

    @staticmethod
    def _init_worker(instance, start_time=None, field_order=None):
        if field_order is not None:
            from galois import GF

            GF(field_order)
            instance = pickle.loads(instance)
        global _worker_instance, _worker_start_time
        _worker_instance = instance
        _worker_start_time = start_time

    @staticmethod
    def _check_observation_worker(work):
        phase, task = work
        _worker_instance._phase = phase
        return _worker_instance._check_task(task, _worker_start_time)

    def _check_task(self, task, start_time):
        order, item, completed, pending = task[:4]
        weighting = task[4] if len(task) == 5 else None
        if pending in ("family", "weighted_family"):
            return self._check_family(
                order, item, completed, start_time, weighted=pending == "weighted_family"
            )
        self.Ci = order
        self._request_results = completed if completed is not None else (
            {} if self._phase != "check" or self.model_str in ("rpc", "rpe") else None
        )
        self._pending_requests = pending if pending is not None else (
            {} if self._phase == "static" else None
        )
        self._executing_task = True
        try:
            indexed = self.randomprobing
            probes = (
                tuple(self.gadget.observationsIn[index] for index in item)
                if indexed
                else item
            )
            result = self.verify_observation(probes, start_time)
            if indexed:
                result["wire_indices"] = item
                result["row"] = tuple(item)
            if weighting is not None:
                result["wire_group_counts"], result["batch_count"] = weighting
            if self._phase == "static" and self._pending_requests:
                resolved = {
                    key: value
                    for (key, value) in self._request_results.items()
                    if key not in self._pending_requests
                }
                result["deferred"] = (order, item, resolved, self._pending_requests)
                if weighting is not None:
                    result["deferred"] += (weighting,)
            return result
        finally:
            self._executing_task = False
            self._request_results = None
            self._pending_requests = None

    def _check_family(self, order, prefix, tails, start_time, weighted=False):
        population = self.gadget.observationsIn if self.randomprobing else self.checklist.population
        proofs = {} if self.randomprobing and self.model_str == "rpc" else None

        def member(indices):
            weighting = ()
            if weighted:
                item, selection, weight = tails[indices[0]]
                weighting = ((selection, weight),)
            else:
                item = indices if self.randomprobing else tuple(population[i] for i in indices)
            completed = None
            if proofs:
                sampled = frozenset(population[index] for index in item)
                completed = {}
                for outputs, certificates in proofs.items():
                    channel = sampled | outputs
                    for certified, result in certificates:
                        if channel <= certified:
                            completed["random", self.model_str, self.t, self.tech, channel] = result
                            break
            return self._check_task(
                (order if self.randomprobing else 0, item, completed, None) + weighting,
                start_time,
            )

        if not tails:
            return {"family_results": [member(prefix)]}

        def unit(position):
            if weighted:
                return (
                    (order, order, 0, frozenset()),
                    tuple(population[wire] for wire in tails[position][0]),
                )
            cached = self._batch_units.get(position)
            if cached is None:
                if self.randomprobing:
                    cached = ((1, 1, 0, frozenset()), (population[position],))
                else:
                    self._reset_observation()
                    self.O = (population[position],)
                    self._prepare_observation()
                    cached = (
                        (self.probe_count, self.t_in, self.t_out, frozenset(self.O_outIndex)),
                        tuple(self.P),
                    )
                if len(self._batch_units) >= 8192:
                    self._batch_units.clear()
                self._batch_units[position] = cached
            return cached

        prefix_units = [unit(position) for position in prefix]
        prefix_probes = tuple(value for item in prefix_units for value in item[1])
        blocks = (
            ((1, tuple(range(len(tails)))),) if weighted else
            tails if isinstance(tails[0], tuple) else ((1, tails),)
        )
        partitions = []
        for take, positions in blocks:
            groups = {}
            for position in positions:
                signature, values = unit(position)
                groups.setdefault(signature, []).append((position, values))
            choices = []
            entries = list(groups.items())
            for first, (signature, selected) in enumerate(entries):
                if len(selected) >= take:
                    choices.append(((take, tuple(selected), signature),))
                if take == 2:
                    for other_signature, other in entries[first + 1:]:
                        choices.append((
                            (1, tuple(selected), signature),
                            (1, tuple(other), other_signature),
                        ))
            partitions.append(choices)
        results = []
        for partition in product(*partitions):
            grouped = tuple(block for part in partition for block in part)
            context = (
                *(
                    sum(item[0][i] for item in prefix_units)
                    + sum(take * signature[i] for take, _, signature in grouped)
                    for i in range(3)
                ),
                frozenset().union(
                    *(item[0][3] for item in prefix_units),
                    *(signature[3] for _, _, signature in grouped),
                ),
            )
            stack = [grouped]
            attempts = min(10, max(2, sum(len(items) for _, items, _ in grouped).bit_length()))
            while stack:
                batch = stack.pop()
                count = prod(comb(len(items), take) for take, items, _ in batch)
                reason = self._limit_reason(start_time)
                if reason:
                    results.append({"processed": False, "abort": None, "stop_reason": reason})
                    return {"family_results": results}
                checks = None
                if count > 1 and attempts:
                    attempts -= 1
                    probes = prefix_probes + tuple(
                        value for _, items, _ in batch for _, values in items for value in values
                    )
                    self._reset_observation()
                    self.probe_count, self.t_in, self.t_out, output_indices = context
                    self.O_outIndex = set(output_indices)
                    checks = self._prove_family(probes, proofs)
                    if checks is None and count >= 8 and attempts:
                        accepted = [list(items[:take]) for take, items, _ in batch]
                        additions = [
                            (block, entry)
                            for block, (take, items, _) in enumerate(batch)
                            for entry in items[take:]
                        ]
                        attempts -= 1
                        probes = prefix_probes + tuple(
                            value for items in accepted for _, values in items for value in values
                        )
                        self._reset_observation()
                        self.probe_count, self.t_in, self.t_out, output_indices = context
                        self.O_outIndex = set(output_indices)
                        checks = self._prove_family(probes, proofs)
                        if checks is not None:
                            pending = [additions] if additions else []
                            while pending and attempts:
                                chunk = pending.pop()
                                reason = self._limit_reason(start_time)
                                if reason:
                                    results.append({"processed": False, "abort": None, "stop_reason": reason})
                                    return {"family_results": results}
                                attempts -= 1
                                probes = prefix_probes + tuple(
                                    value for items in accepted for _, values in items for value in values
                                ) + tuple(value for _, (_, values) in chunk for value in values)
                                self._reset_observation()
                                self.probe_count, self.t_in, self.t_out, output_indices = context
                                self.O_outIndex = set(output_indices)
                                extended = self._prove_family(probes, proofs)
                                if extended is not None:
                                    checks = extended
                                    for block, entry in chunk:
                                        accepted[block].append(entry)
                                elif len(chunk) > 1:
                                    middle = len(chunk) // 2
                                    pending.extend((chunk[middle:], chunk[:middle]))
                            safe_blocks = []
                            residuals = []
                            for (take, items, signature), good in zip(batch, accepted):
                                included = {position for position, _ in good}
                                bad = tuple(entry for entry in items if entry[0] not in included)
                                good = tuple(good)
                                safe_blocks.append((take, good, signature))
                                options = []
                                for good_count in range(max(0, take - len(bad)), min(take, len(good)) + 1):
                                    parts = ()
                                    if good_count:
                                        parts += ((good_count, good, signature),)
                                    if take > good_count:
                                        parts += ((take - good_count, bad, signature),)
                                    options.append((good_count == take, parts))
                                residuals.append(options)
                            for parts in product(*residuals):
                                if not all(complete for complete, _ in parts):
                                    stack.append(tuple(block for _, part in parts for block in part))
                            batch = tuple(safe_blocks)
                            count = prod(comb(len(items), take) for take, items, _ in batch)
                if checks is not None:
                    packet = {
                        "processed": True, "abort": False, "verify": True,
                        "status": "safe", "mi": 0, "mi_text": None, "exact_zero": True,
                        "choice_rpe": (), "rpe_input_indices": (), "leakage": [],
                        "Ci": order if self.randomprobing else -1,
                        "batch_count": count, "requests": checks,
                    }
                    if weighted:
                        packet["family_weighted"] = tuple(tails[position] for position, _ in batch[0][1])
                        packet["batch_count"] = sum(item[2] for item in packet["family_weighted"])
                    else:
                        packet["family_prefix"] = prefix
                        packet["family_blocks"] = tuple(
                            (take, tuple(position for position, _ in items)) for take, items, _ in batch
                        )
                    results.append(packet)
                    continue
                for selected in product(*(combinations(items, take) for take, items, _ in batch)):
                    indices = tuple(sorted((*prefix, *(position for items in selected for position, _ in items))))
                    result = member(indices)
                    results.append(result)
                    if result["abort"] is None:
                        return {"family_results": results}
        return {"family_results": results}

    def _prove_family(self, probes, proofs=None):
        def prove(outputs):
            values = tuple(self.OutputProbe[output] for output in outputs)
            self.P = list(dict.fromkeys((*probes, *values)))
            if proofs is not None:
                output_key = frozenset(values)
                original = frozenset(self.P)
                for certified, result in proofs.get(output_key, ()):
                    if original <= certified:
                        return result
            self.P_channel_count = None
            self.choice_rpe = ()
            self._prefix_witness = None
            safe = (
                self._test_security() or self._prove_affine_prefix()
                or self._prove_symbolic_prefix()
            )
            if not safe and len(self.P) <= 8:
                safe = self.simplify()
            if not safe:
                return None
            witness = self._prefix_witness
            if witness is None:
                required = [set() for _ in range(self.len_secrets)]
                for expression in self.P:
                    for symbol in expression.free_symbols & self.shares_set:
                        family, index = self._share_locations[symbol]
                        required[family].add(index)
                witness = tuple(tuple(sorted(indices)) for indices in required)
            result = {
                "mi": 0, "mi_text": None, "exact_zero": True,
                "choice_rpe": (), "rpe_input_indices": witness,
                "unknown": False, "failed": False, "leakage": [],
            }
            if proofs is not None:
                retained = [
                    certificate for certificate in proofs.get(output_key, ())
                    if not certificate[0] <= original
                ]
                proofs[output_key] = [(original, result)] + retained[:7]
            return result

        self._proof_only = True
        try:
            if not self.randomprobing or self.model_str in ("rps_secret", "rps_share"):
                result = prove(())
                return [result] if result is not None else None
            checks = []
            for request in self.rp_requests:
                if self.model_str == "rpc":
                    result = prove(request)
                else:
                    result = None
                    for outputs in request["choices"]:
                        result = prove(outputs)
                        if result is not None:
                            result["output_choice"] = tuple(map(str, outputs))
                            result["event_failures"] = [
                                {"inputs": event, "lower": False, "upper": False}
                                for event in self.rp_events
                            ]
                            break
                if result is None:
                    return None
                checks.append(result)
            return checks
        finally:
            self._proof_only = False

    def _limit_reason(self, start_time):
        if start_time is not None and time.time() - start_time >= self.max_hours * 3600:
            return "Time limit reached"
        process = self._resource_process
        if process is None or process.pid != os.getpid():
            process = self._resource_process = psutil.Process()
        if process.memory_info().rss / 1024**3 > self.max_mem:
            return "Memory limit reached"
        return None

    def verify_observation(self, item, start_time=None):
        if not self._executing_task:
            self._request_results = {} if self.model_str in ("rpc", "rpe") else None
            self._pending_requests = None
            self._phase = "check"
        if self.randomprobing:
            return self._check_random_observation(item, start_time)
        reason = self._limit_reason(start_time)
        if reason:
            return {"processed": False, "abort": None, "verify": False, "stop_reason": reason}
        self._reset_observation()
        self.O = item
        cache = self._prepare_observation()
        row, original_probes = (tuple(self.row), tuple(self.P))
        evaluated = self._evaluate_probes(cache)
        exact_zero = evaluated["exact_zero"]
        reason = self._limit_reason(start_time)
        if self.abort and exact_zero is not True:
            reason = "Stopped at an unverified observation (--abort)"
        result = {
            **evaluated,
            "processed": True,
            "abort": None if reason else False,
            "stop_reason": reason,
            "verify": exact_zero is True,
            "status": (
                "safe"
                if exact_zero is True
                else "insecure" if exact_zero is False else "unknown"
            ),
            "row": row,
            "cache": cache,
            "Ci": -1,
            "leakage": list(original_probes) if exact_zero is not True else [],
        }
        return result

    def _reset_observation(self):
        self.row = -1
        self.mi = None
        self.mi_text = None
        self.O = []
        self.P = []
        self.P_xor_groups = ()
        self.P_channel_count = None
        self.P_raw = []
        self.exact_zero = None
        self.t_in = 0
        self.probe_count = 0
        self.O_inIndex = set()
        self.t_out = 0
        self.O_outIndex = set()
        self.choice_rpe = tuple()

    def _prepare_observation(self):
        row = []
        options = self.gadget.checkOptions["robust"]
        xor_leakage = "transitionxor" in options
        groups = {}
        units = ((unit, None) for unit in self.O)
        if "transitionall" in options:
            units = (
                (endpoint, pair_index)
                for (pair_index, pair) in enumerate(self.O)
                for endpoint in (pair if isinstance(pair, (tuple, list)) else (pair,))
            )
        for unit, pair_index in units:
            members = list(flatten(unit)) if isinstance(unit, (tuple, list)) else [unit]
            if not members:
                raise ValueError("Empty probe group")
            is_output = all((probe in self.OutputProbe for probe in members))
            if self.model_str == "pini" and is_output:
                indices = {
                    self.funcMapping_index_op[self.shares_op[probe]] for probe in members
                }
                if len(indices) != 1:
                    raise ValueError("A PINI output group must contain one share index")
                self.O_outIndex.update(indices)
            elif self.model_str in ("ni", "sni", "pini") and len(members) != 1:
                raise ValueError(
                    "NI/SNI internal probe groups must identify one physical location"
                )
            self.probe_count += 1
            if is_output:
                self.t_out += 1
            else:
                self.t_in += 1
            for probe in members:
                row.append(probe)
                start = len(self.P)
                self.P.extend(self.row2Probe[probe])
                if xor_leakage:
                    group = (
                        ("pair", pair_index) if pair_index is not None else ("probe", len(row))
                    )
                    groups.setdefault(group, []).extend(range(start, len(self.P)))
        if xor_leakage:
            self.P_raw = list(self.P)
            self.P_xor_groups = tuple((tuple(indices) for indices in groups.values()))
            xor = Xor if self.logic else EncodedXor
            self.P = [xor(*(self.P_raw[i] for i in indices)) for indices in self.P_xor_groups]
        self.row = row
        if not self.P:
            raise RuntimeError("Error in O2p.")
        cache = (
            "multiplicity", frozenset(Counter(self.P).items())
        ) if self.HW else ("values", frozenset(self.P))
        if self.model_str in ("ni", "sni", "pini"):
            cache += (
                (
                    self.model_str,
                    self.probe_count,
                    self.t_in,
                    self.t_out,
                    tuple(sorted(map(str, self.O_outIndex))),
                ),
            )
        if "hw_vector" in self.gadget.checkOptions["robust"]:
            cache = ("hw_vector", cache)
        return cache

    def _evaluate_probes(self, cache):
        completed = self._request_results
        if completed is not None and cache in completed:
            result = completed[cache]
        elif cache in self.observation_cache and cache in self.exact_zero_cache:
            result = {
                "mi": self.observation_cache[cache],
                "exact_zero": self.exact_zero_cache[cache],
                "mi_text": self.mi_text_cache.get(cache),
                "choice_rpe": self.choice_rpe_cache.get(cache, ()),
                "rpe_input_indices": self.rpe_witness_cache.get(cache, self._empty_rpe_indices),
            }
        else:
            mi_text = None
            phase = self._phase
            if phase == "mi":
                probes, channel_count, choice, witness = self._pending_requests.pop(cache)
                self.P = list(probes)
                self.P_channel_count = channel_count
                self.choice_rpe = choice
                self.rpe_input_indices = witness
                safe = False
            elif phase == "static" and cache in self._unresolved_cache:
                probes, channel_count, choice, witness = self._unresolved_cache[cache]
                self.P = list(probes)
                self.P_channel_count = channel_count
                self.choice_rpe = choice
                self.rpe_input_indices = witness
                safe = False
            elif self.tech == 0:
                safe = False
            else:
                componentwise_hw = "hw_vector" in self.gadget.checkOptions["robust"]
                self._prefix_witness = None
                safe = (
                    self._test_security() or self._prove_affine_prefix()
                    or self._prove_symbolic_prefix()
                )
                if not safe:
                    safe = self.simplify(preserve_layout=self.HW, componentwise_hw=componentwise_hw)
                if not safe:
                    safe = self._prove_quadratic_masks()
                if self.HW:
                    channel_count = getattr(self, "P_channel_count", None)
                    if channel_count is None:
                        channel_count = len(self.P)
                    parts = []
                    for values in (self.P[:channel_count], self.P[channel_count:]):
                        retained = (
                            expr
                            for expr in values
                            if not expr.is_Integer and expr not in (False, True)
                        )
                        parts.append(
                            list(dict.fromkeys(retained))
                            if componentwise_hw
                            else list(retained)
                        )
                    self.P = parts[0] + parts[1]
                    self.P_channel_count = len(parts[0])
                if self.model_str == "rpe":
                    needed = [set() for _ in range(self.len_secrets)]
                    for value in self.P:
                        for share in value.free_symbols & self.shares_set:
                            position = self.shares[share]
                            needed[self.funcMapping[position]].add(
                                self.funcMapping_index[position]
                            )
                    self.rpe_input_indices = (
                        self._prefix_witness if safe and self._prefix_witness is not None else
                        tuple(tuple(sorted(indices)) for indices in needed)
                    )
            if safe:
                self.choice_rpe = ()
                mi, exact_zero = (0, True)
            elif self.tech == 1 or phase == "static":
                mi, exact_zero = (-1, None)
                if phase == "static":
                    residual = self._unresolved_cache.get(cache)
                    if residual is None:
                        residual = (
                            tuple(self.P),
                            self.P_channel_count,
                            self.choice_rpe,
                            getattr(self, "rpe_input_indices", ()),
                        )
                        if len(self._unresolved_cache) >= 4096:
                            self._unresolved_cache.clear()
                        self._unresolved_cache[cache] = residual
                    self._pending_requests[cache] = residual
            else:
                if self.model_str == "rpe":
                    self.choice_rpe = ()
                mi = self.MIA.compute()
                exact_zero = self.MIA.last_exact_zero
                mi_text = self.MIA.last_mi_text
            if mi is None:
                raise RuntimeError("Error in check: mi = None")
            result = {
                "mi": mi,
                "exact_zero": exact_zero,
                "mi_text": mi_text,
                "choice_rpe": self.choice_rpe,
                "rpe_input_indices": getattr(self, "rpe_input_indices", ()),
            }
            if not (phase == "static" and exact_zero is None):
                self.observation_cache[cache] = mi
                self.exact_zero_cache[cache] = exact_zero
                if mi_text is not None:
                    self.mi_text_cache[cache] = mi_text
                if self.model_str == "rpe":
                    self.choice_rpe_cache[cache] = self.choice_rpe
                    self.rpe_witness_cache[cache] = result["rpe_input_indices"]
        if completed is not None:
            completed[cache] = result
        self.choice_rpe = result["choice_rpe"]
        self.rpe_input_indices = result["rpe_input_indices"]
        self.mi = result["mi"]
        self.exact_zero = result["exact_zero"]
        self.mi_text = result["mi_text"]
        return result

    def _record_result(self, result):
        if result.get("stop_reason"):
            self._check_stop_reason = result["stop_reason"]
            if self.randomprobing:
                self._rp_stop_reason = result["stop_reason"]
        if not result.get("processed", True) or "deferred" in result:
            return
        if self.randomprobing:
            self._aggregate_random_result(result)
        else:
            if "batch_count" in result:
                self._result_counts["safe"] += result["batch_count"]
                self.processed_count += result["batch_count"]
                return
            cache = result["cache"]
            if self.mcore > 0:
                self.observation_cache[cache] = result["mi"]
                self.exact_zero_cache[cache] = result["exact_zero"]
                if result.get("mi_text") is not None:
                    self.mi_text_cache[cache] = result["mi_text"]
            status = result["status"]
            self._result_counts[status] += 1
            if not result["verify"]:
                row = result["row"]
                self.gadget.row_mi[row] = result["mi"]
                self.gadget.row_verdict[row] = status
                self.gadget.row_mi_text[row] = result.get("mi_text")
                self.MImatrix[result["mi"]] = self.MImatrix.get(result["mi"], 0) + 1
                self.leakage.extend(result["leakage"])
        if self._live_detail and (not result["verify"] or self._watch_locations):
            locations = self.gadget.probe_locations
            current = tuple(locations[probe] for probe in result["row"])
            if (self.detail and result["status"] != "safe") or self._watch_locations.intersection(
                current
            ):
                self.event(
                    "detail",
                    {
                        "locations": current,
                        "status": result["status"],
                        "mi": None if self.tech == 1 or result["mi"] < 0 else result["mi"],
                        "mi_text": result.get("mi_text"),
                        "quantity": "MI" if self.model_str == "probing_secret" else "CMI",
                    },
                )
        self.processed_count += result.get("batch_count", 1)

    def _symbolic_info(self, expression):
        info = self._symbolic_cache.get(expression)
        if info is None:
            shares = indices = 0
            sources = expression.free_symbols
            for symbol in sources & self.shares_set:
                shares |= self._share_bits[symbol]
                indices |= self._index_bits[self._share_locations[symbol][1]]
            self._symbolic_serial += 1
            info = (self._symbolic_serial, shares, indices)
            if len(self._symbolic_cache) >= 8192:
                self._symbolic_cache.clear()
            self._symbolic_cache[expression] = info
        return info

    def _test_security(self):
        model = self.model_str
        shares = indices = 0
        for value in self.P:
            info = self._symbolic_info(value)
            shares |= info[1]
            indices |= info[2]
            if shares and model in ("probing_secret", "rps_secret"):
                return False
        if model in ("probing_secret", "rps_secret"):
            return True
        if model == "pini":
            allowed = 0
            for index in self.O_outIndex:
                allowed |= self._index_bits.get(index, 0)
            return (indices & ~allowed).bit_count() <= self.t_in
        budget = (
            self.probe_count if model == "ni" else self.t_in if model == "sni"
            else self.shareNum - 1 if model in ("probing_share", "rps_share") else self.t
        )
        if model == "rpe":
            self.choice_rpe = tuple(
                index for index, family in enumerate(self._family_bits)
                if (shares & family).bit_count() > budget
            )
            return not self.choice_rpe
        return all((shares & family).bit_count() <= budget for family in self._family_bits)

    def _prove_symbolic_prefix(self):
        self._prefix_witness = None
        state = getattr(self, "_symbolic_prefix_state", None)
        if state is None or not self.P or len(self.P) > 64:
            return False
        observations = tuple(self.P)
        first = observations[0]
        if first != state["first"]:
            plans = getattr(self, "_symbolic_prefix_plans", {})
            state = plans.get(first)
            if state is None:
                return False
            plans.pop(first)
            plans[first] = state
            self._symbolic_prefix_state = state
        signature = (None if self.logic else self.GF_field, tuple(self.randoms), frozenset(self.shares_set))
        if state["signature"] != signature:
            return False
        transformed = observations
        try:
            for substitution, cache in zip(state["steps"], state["caches"]):
                if len(cache) >= 256:
                    cache.clear()
                output = []
                for expression in transformed:
                    if expression not in cache:
                        rebuilt = {}
                        pending = [(expression, False)]
                        while pending:
                            node, ready = pending.pop()
                            if node in rebuilt:
                                continue
                            if len(rebuilt) > 512:
                                return False
                            if node in substitution:
                                rebuilt[node] = substitution[node]
                            elif not node.args:
                                rebuilt[node] = node
                            elif not ready:
                                pending.append((node, True))
                                pending.extend((arg, False) for arg in node.args)
                            else:
                                args = tuple(rebuilt[arg] for arg in node.args)
                                rebuilt[node] = (
                                    node if args == node.args else
                                    node.func(*args) if self.logic or node.func is EncodedXor else
                                    node.func(*args, evaluate=False)
                                )
                        value = rebuilt[expression]
                        cache[expression] = (
                            self._normalize_boolean(value, self._static_cache["normalized"])
                            if self.logic else state["evaluator"].evaluate(value)
                        )
                    output.append(cache[expression])
                transformed = tuple(output)
            if transformed == observations:
                return False
            return self._prove_affine_prefix(transformed)
        except (TypeError, ValueError, NotImplementedError):
            return False

    def _prove_affine_prefix(self, probes=None):
        self._prefix_witness = None
        observations = tuple(self.P if probes is None else probes)
        field = None if self.logic else self.GF_field
        signature = (field, tuple(self.randoms))
        state = getattr(self, "_affine_prefix_state", None)
        if state is None or state["signature"] != signature:
            masks = {
                symbols(mask) if isinstance(mask, str) else mask: index
                for index, mask in enumerate(self.randoms)
            }
            state = {
                "signature": signature,
                "masks": masks,
                "cache": {},
                "products": {},
                "inverses": {1: 1},
                "observations": (),
                "blocked": None,
                "pivots": [],
                "residuals": [],
                "checkpoints": [(0, 0)],
                "prefixes": {},
                "prefix_key": None,
            }
            self._affine_prefix_state = state
        masks = state["masks"]
        cache = state["cache"]
        q = 2 if self.logic else int(field.order)
        binary = self.logic or field.characteristic == 2
        if not binary and field.degree != 1:
            return False
        products = state["products"]

        def multiply(left, right):
            if not binary:
                return left * right % q
            if not left or not right:
                return 0
            if left == 1:
                return right
            if right == 1:
                return left
            key = (left, right) if left <= right else (right, left)
            value = products.get(key)
            if value is None:
                value = int(field(left) * field(right))
                if len(products) >= 4096:
                    products.clear()
                products[key] = value
            return value

        rows = []
        blocked = masks.keys() & self.shares_set
        for expression in observations:
            decomposition = cache.get(expression)
            if decomposition is None:
                row = {}
                pending = [(expression, 1)]
                while pending:
                    node, coefficient = pending.pop()
                    if not coefficient:
                        continue
                    if node in (False, True):
                        continue
                    if node.is_Integer:
                        if binary and abs(int(node)) >= q:
                            return False
                        continue
                    if self.logic and node.func is Not:
                        pending.append((node.args[0], coefficient))
                        continue
                    additive = (
                        node.func is Xor
                        if self.logic
                        else node.is_Add or (binary and node.func is EncodedXor)
                    )
                    if additive:
                        pending.extend((term, coefficient) for term in node.args)
                        continue
                    if not self.logic and node.is_Mul:
                        factors = []
                        scale = coefficient
                        for factor in node.args:
                            if factor.is_Integer:
                                value = abs(int(factor)) if binary else int(factor) % q
                                if value >= q:
                                    return False
                                scale = multiply(scale, value)
                            else:
                                factors.append(factor)
                        if len(factors) <= 1:
                            if factors and scale:
                                pending.append((factors[0], scale))
                            continue
                    previous = row.get(node, 0)
                    value = previous ^ coefficient if binary else (previous + coefficient) % q
                    if value:
                        row[node] = value
                    else:
                        row.pop(node, None)
                nonlinear = frozenset(
                    symbol
                    for node in row
                    if node not in masks
                    for symbol in node.free_symbols
                    if symbol in masks
                )
                decomposition = (tuple(row.items()), nonlinear)
                if len(cache) >= 8192:
                    cache.clear()
                cache[expression] = decomposition
            rows.append(decomposition[0])
            blocked.update(decomposition[1])
        blocked = frozenset(blocked)
        old = state["observations"]
        common = 0
        if state["blocked"] == blocked:
            for previous, current in zip(old, observations):
                if previous != current:
                    break
                common += 1
        pivots = state["pivots"]
        residuals = state["residuals"]
        checkpoints = state["checkpoints"]
        key = (blocked, observations[:2]) if observations and len(observations) <= 64 else None
        if key != state["prefix_key"]:
            prefixes = state["prefixes"]
            if state["prefix_key"] is not None:
                prefixes.pop(state["prefix_key"], None)
                if len(prefixes) >= 16:
                    prefixes.pop(next(iter(prefixes)))
                prefixes[state["prefix_key"]] = (
                    old, tuple(pivots), tuple(residuals), tuple(checkpoints),
                )
            previous = prefixes.get(key)
            if previous is not None:
                previous_observations, previous_pivots, previous_residuals, previous_checkpoints = previous
                restored = 0
                for previous_expression, expression in zip(previous_observations, observations):
                    if previous_expression != expression:
                        break
                    restored += 1
                if restored > common:
                    pivot_count, residual_count = previous_checkpoints[restored]
                    pivots[:] = previous_pivots[:pivot_count]
                    residuals[:] = previous_residuals[:residual_count]
                    checkpoints[:] = previous_checkpoints[:restored + 1]
                    common = restored
            state["prefix_key"] = key
        pivot_count, residual_count = checkpoints[common]
        del pivots[pivot_count:]
        del residuals[residual_count:]
        del checkpoints[common + 1:]
        eligible = masks.keys() - blocked
        inverses = state["inverses"]
        for decomposition in rows[common:]:
            row = dict(decomposition)
            for pivot, basis in pivots:
                coefficient = row.get(pivot, 0)
                if not coefficient:
                    continue
                for term, value in basis.items():
                    scaled = multiply(coefficient, value)
                    previous = row.get(term, 0)
                    value = previous ^ scaled if binary else (previous - scaled) % q
                    if value:
                        row[term] = value
                    else:
                        row.pop(term, None)
            available = row.keys() & eligible
            if available:
                pivot = min(available, key=masks.__getitem__)
                coefficient = row[pivot]
                inverse = inverses.get(coefficient)
                if inverse is None:
                    inverse = int(field(coefficient) ** -1) if binary else pow(coefficient, -1, q)
                    inverses[coefficient] = inverse
                if inverse != 1:
                    row = {term: multiply(inverse, value) for term, value in row.items()}
                pivots.append((pivot, row))
            elif row:
                residuals.append(frozenset().union(*(term.free_symbols for term in row)))
            checkpoints.append((len(pivots), len(residuals)))
        state["observations"] = observations
        state["blocked"] = blocked
        support = set().union(*residuals) & self.shares_set
        model = self.model_str
        if model in ("probing_secret", "rps_secret"):
            if support:
                return False
            self._prefix_witness = tuple(() for _ in range(self.len_secrets))
            return True
        if model == "pini":
            needed = {self._share_locations[symbol][1] for symbol in support}
            if len(needed - self.O_outIndex) > self.t_in:
                return False
        budget = (
            self.probe_count
            if model == "ni"
            else self.t_in
            if model == "sni"
            else self.shareNum - 1
            if model in ("probing_share", "rps_share")
            else self.t
        )
        needed = [set() for _ in range(self.len_secrets)]
        for symbol in support:
            family, index = self._share_locations[symbol]
            needed[family].add(index)
            if model != "pini" and len(needed[family]) > budget:
                return False
        self._prefix_witness = tuple(tuple(sorted(indices)) for indices in needed)
        return True

    def _prove_quadratic_masks(self, probes=None):
        from sympy.logic.boolalg import And

        self._prefix_witness = None
        observations = tuple(self.P if probes is None else probes)
        if not observations or len(observations) > 64:
            return False
        field = None if self.logic else self.GF_field
        q = 2 if self.logic else int(field.order)
        binary = self.logic or field.characteristic == 2
        if not binary and field.degree != 1:
            return False
        masks = frozenset(symbols(mask) if isinstance(mask, str) else mask for mask in self.randoms)
        masks -= self.shares_set
        signature = (field, masks)
        state = getattr(self, "_quadratic_proof_state", None)
        if state is None or state["signature"] != signature:
            state = {"signature": signature, "nodes": {}, "products": {}, "residuals": {}}
            self._quadratic_proof_state = state
        previous = state["residuals"].get(observations)
        if previous is not None:
            return self._prove_affine_prefix(previous)
        cache = state["nodes"]
        if len(cache) >= 8192:
            cache.clear()
        products = state["products"]

        def multiply(left, right):
            if not binary:
                return left * right % q
            if left <= 1 or right <= 1:
                return left * right
            key = (left, right) if left <= right else (right, left)
            value = products.get(key)
            if value is None:
                value = int(field(left) * field(right))
                if len(products) >= 4096:
                    products.clear()
                products[key] = value
            return value

        def accumulate(target, source, coefficient=1):
            for monomial, value in source.items():
                value = multiply(value, coefficient)
                old = target.get(monomial, 0)
                value = old ^ value if binary else (old + value) % q
                if value:
                    target[monomial] = value
                else:
                    target.pop(monomial, None)

        def product(left, right):
            result = {}
            if len(left) * len(right) > 256:
                return None
            for first, first_value in left.items():
                for second, second_value in right.items():
                    factors = first + second
                    if q == 2:
                        factors = set(factors)
                    if len(factors) > 2:
                        return None
                    monomial = tuple(sorted(factors, key=str))
                    accumulate(result, {monomial: multiply(first_value, second_value)})
                    if len(result) > 64:
                        return None
            return result

        rows = []
        for expression in observations:
            pending = [(expression, False)]
            while pending:
                node, ready = pending.pop()
                if node in cache:
                    continue
                if node in (False, True):
                    cache[node] = {(): 1} if node == True else {}
                    continue
                if node.is_Integer:
                    value = abs(int(node)) if binary else int(node) % q
                    cache[node] = ({(): value} if value else {}) if value < q else None
                    continue
                if node.is_Symbol:
                    cache[node] = {(node,): 1}
                    continue
                additive = node.func is Xor if self.logic else node.is_Add or (binary and node.func is EncodedXor)
                multiplicative = node.func is And if self.logic else node.is_Mul
                power = not self.logic and node.is_Pow and node.exp in (0, 1, 2)
                if not (additive or multiplicative or power or (self.logic and node.func is Not)):
                    cache[node] = None
                    continue
                children = (node.base,) if power else node.args
                if not ready:
                    pending.append((node, True))
                    pending.extend((child, False) for child in children if child not in cache)
                    continue
                arguments = [cache[child] for child in children]
                if any(argument is None for argument in arguments):
                    cache[node] = None
                    continue
                if additive or node.func is Not:
                    result = {(): 1} if node.func is Not else {}
                    for argument in arguments:
                        accumulate(result, argument)
                else:
                    result = {(): 1}
                    for argument in arguments * int(node.exp) if power else arguments:
                        result = product(result, argument)
                        if result is None:
                            break
                cache[node] = result if result is None or len(result) <= 64 else None
            row = cache.get(expression)
            if row is None:
                return False
            rows.append(row)
        if len(cache) >= 8192:
            cache.clear()
        if sum(map(len, rows)) > 256:
            return False
        used = set()
        changed = False
        score = (
            len({symbol for row in rows for term in row for symbol in term} & self.shares_set),
            sum(map(len, rows)),
            sum(len(term) for row in rows for term in row),
        )
        for _ in range(min(len(masks), 8)):
            candidates = {}
            for row in rows:
                for monomial, coefficient in row.items():
                    if len(monomial) != 2 or monomial[0] == monomial[1]:
                        continue
                    for mask, anchor in (monomial, monomial[::-1]):
                        if mask not in masks or mask in used:
                            continue
                        shift = {}
                        for term, value in row.items():
                            if anchor in term and term.count(anchor) == 1 and mask not in term:
                                shift[tuple(symbol for symbol in term if symbol != anchor)] = value
                        if not shift or not any(set(term) & self.shares_set for term in shift):
                            continue
                        inverse = int(field(coefficient) ** -1) if binary and coefficient != 1 else pow(coefficient, -1, q)
                        scale = inverse if binary else (-inverse) % q
                        shift = {term: multiply(value, scale) for term, value in shift.items()}
                        key = (mask, tuple(sorted(shift.items(), key=str)))
                        candidates[key] = shift
                        if len(candidates) >= 32:
                            break
                    if len(candidates) >= 32:
                        break
                if len(candidates) >= 32:
                    break
            selected = None
            for (mask, _), shift in candidates.items():
                replacement = dict(shift)
                replacement[(mask,)] = 1
                updated = []
                for row in rows:
                    result = {}
                    for term, coefficient in row.items():
                        if mask not in term:
                            accumulate(result, {term: coefficient})
                            continue
                        expansion = {(): coefficient}
                        for symbol in term:
                            expansion = product(expansion, replacement if symbol == mask else {(symbol,): 1})
                            if expansion is None:
                                break
                        if expansion is None:
                            result = None
                            break
                        accumulate(result, expansion)
                    if result is None or len(result) > 64:
                        break
                    updated.append(result)
                if len(updated) != len(rows) or sum(map(len, updated)) > 256:
                    continue
                candidate_score = (
                    len({symbol for row in updated for term in row for symbol in term} & self.shares_set),
                    sum(map(len, updated)),
                    sum(len(term) for row in updated for term in row),
                )
                if candidate_score < score:
                    score = candidate_score
                    selected = mask, updated
            if selected is None:
                break
            mask, rows = selected
            used.add(mask)
            changed = True
        if not changed:
            return False
        residual = []
        for row in rows:
            terms = []
            for monomial, coefficient in row.items():
                if self.logic:
                    term = And(*monomial) if monomial else True
                else:
                    factors = list(monomial)
                    if coefficient != 1 or not factors:
                        factors.insert(0, Integer(coefficient))
                    term = factors[0] if len(factors) == 1 else Mul(*factors, evaluate=False)
                terms.append(term)
            residual.append(Xor(*terms) if self.logic else Add(*terms, evaluate=False) if terms else Integer(0))
        residual = tuple(residual)
        if len(state["residuals"]) >= 1024:
            state["residuals"].clear()
        state["residuals"][observations] = residual
        return self._prove_affine_prefix(residual)

    def simplify(self, preserve_layout=False, componentwise_hw=False):
        if componentwise_hw:
            preserve_layout = True
            slot_zero = sympify(False) if self.logic else Integer(0)
            channel_count = getattr(self, "P_channel_count", None)
            if channel_count is None:
                channel_count = len(self.P)
            if not isinstance(channel_count, int) or not 0 <= channel_count <= len(self.P):
                raise ValueError("Invalid leakage-channel observation count")
        if self._test_security():
            return True

        def compact_tuple():
            if componentwise_hw:
                seen = (set(), set())
                compacted = []
                for index, expr in enumerate(self.P):
                    known = seen[index >= channel_count]
                    if expr.is_Integer or expr in (False, True) or expr in known:
                        compacted.append(slot_zero)
                    else:
                        known.add(expr)
                        compacted.append(expr)
                self.P = compacted
            elif not preserve_layout:
                self.P = list(
                    dict.fromkeys(
                        (
                            expr
                            for expr in self.P
                            if not expr.is_Integer and expr not in (False, True)
                        )
                    )
                )

        original = tuple(self.P)
        compact_tuple()
        if self.tech == 2 and not self._proof_only:
            costs = self._static_cache["costs"]
            source_costs = self._static_cache["sources"]
            if len(costs) >= 8192:
                costs.clear()
                for cache in source_costs:
                    cache.clear()
            best_probes = list(self.P)
            ignore_constants = componentwise_hw or (preserve_layout and self.HW)
            best_cost = self._residual_cost(best_probes, costs, source_costs, ignore_constants)
            previous_probes = tuple(best_probes)

            def remember():
                nonlocal best_probes, best_cost, previous_probes
                current_probes = tuple(self.P)
                if current_probes == previous_probes:
                    return
                previous_probes = current_probes
                cost = self._residual_cost(
                    current_probes, costs, source_costs, ignore_constants
                )
                if cost < best_cost:
                    best_probes, best_cost = (list(current_probes), cost)

        else:
            remember = None

        expression_text = self._static_cache["text"]
        if len(expression_text) >= 8192:
            expression_text.clear()

        def cached_text(expr):
            text = expression_text.get(expr)
            if text is None:
                text = str(expr)
                expression_text[expr] = text
            return text

        verify = self._static_boolean if self.logic else self._static_field
        self._substitution_steps = []
        try:
            safe = verify(preserve_layout, componentwise_hw, remember, cached_text)
            steps = tuple(self._substitution_steps)
        finally:
            self._substitution_steps = None
        if steps and original:
            plans = getattr(self, "_symbolic_prefix_plans", None)
            if plans is None:
                plans = self._symbolic_prefix_plans = {}
            previous = plans.pop(original[0], None)
            signature = (None if self.logic else self.GF_field, tuple(self.randoms), frozenset(self.shares_set))
            if previous is not None and previous["signature"] == signature and previous["steps"] == steps:
                state = previous
            else:
                evaluator = None
                if not self.logic:
                    evaluator = sympyGF2N() if self.GF_field.characteristic == 2 else sympyGFp()
                    evaluator.set_field(self.GF_field)
                state = {
                    "first": original[0], "signature": signature,
                    "steps": steps, "caches": [{} for _ in steps], "evaluator": evaluator,
                }
            if len(plans) >= 8:
                plans.pop(next(iter(plans)))
            plans[original[0]] = self._symbolic_prefix_state = state
        compact_tuple()
        if not safe:
            if remember is not None:
                remember()
                self.P = best_probes
            safe = self._test_security()
        return safe

    def _static_boolean(self, preserve_layout, componentwise_hw, remember, cached_text):
        slot_zero = sympify(False)
        normalized = self._static_cache["normalized"]
        if len(normalized) >= 8192:
            normalized.clear()
        count_cache = self._static_cache["counts"]
        if len(count_cache) >= 8192:
            count_cache.clear()
        self.P = P = [self._normalize_boolean(expr, normalized) for expr in self.P]
        test = self._test_security
        observation_counts = None
        used_masks = set()
        while True:
            if remember is not None:
                remember()
            if test():
                return True
            if observation_counts is None:
                mask_symbols = {
                    str(r): symbols(r) if isinstance(r, str) else r for r in self.randoms
                }
                mask_names = sorted(mask_symbols)
                patterns = self.compiled_patterns_random
                mask_scans = [(r, patterns[r].findall) for r in mask_names]
                mask_counts = dict.fromkeys(mask_names, 0)
                observation_counts = []
                for expr in P:
                    row = count_cache.get(expr)
                    if row is None:
                        s = cached_text(expr)
                        row = {r: count for r, scan in mask_scans if (count := len(scan(s)))}
                        count_cache[expr] = row
                    for r, count in row.items():
                        mask_counts[r] += count
                    observation_counts.append(row)
            deleted = False
            for r in mask_names if not preserve_layout or componentwise_hw else ():
                if mask_counts[r] != 1:
                    continue
                atom = mask_symbols[r]
                for i, row in enumerate(observation_counts):
                    if row is None or not row.get(r, 0):
                        continue
                    masked = P[i]
                    while masked.func in (Xor, Not):
                        if atom in masked.args:
                            masked = atom
                            break
                        for arg in masked.args:
                            if arg.has(atom):
                                masked = arg
                                break
                        else:
                            break
                    if masked == atom:
                        for rr, count in row.items():
                            mask_counts[rr] -= count
                        P[i] = slot_zero if componentwise_hw else None
                        observation_counts[i] = {} if componentwise_hw else None
                        deleted = True
                    break
            if deleted:
                P = [expr for expr in P if expr is not None]
                self.P = P
                observation_counts = [row for row in observation_counts if row is not None]
                continue
            updates = None
            ordered = sorted(((mask_counts[r], r) for r in mask_names if mask_counts[r]))
            for occurrences, r in ordered:
                atom = mask_symbols[r]
                affected = [i for (i, row) in enumerate(observation_counts) if row.get(r, 0)]
                residuals = {}
                if (not preserve_layout or componentwise_hw) and occurrences > 1:
                    for i in affected:
                        if observation_counts[i][r] != 1:
                            break
                        terms, phase, found = (set(), False, False)
                        pending = [P[i]]
                        while pending:
                            term = pending.pop()
                            if term == atom:
                                found = True
                            elif term.func is Xor:
                                pending.extend(term.args)
                            elif term.func is Not:
                                phase = not phase
                                pending.append(term.args[0])
                            elif term == True:
                                phase = not phase
                            elif term == False:
                                continue
                            elif term in terms:
                                terms.remove(term)
                            else:
                                terms.add(term)
                        if not found:
                            break
                        residuals[i] = (terms, phase)
                if len(residuals) == len(affected):
                    anchor_i = affected[0]
                    anchor_terms, anchor_phase = residuals[anchor_i]
                    updates = {anchor_i: None}
                    for i in affected[1:]:
                        terms, phase = residuals[i]
                        difference = Xor(*terms ^ anchor_terms, phase ^ anchor_phase)
                        updates[i] = None if difference in (False, True) else difference
                    break
                if r in used_masks:
                    continue
                candidates = {}
                checked = {}
                for i in affected:
                    pending = [(P[i], 0)]
                    while pending:
                        node, depth = pending.pop()
                        if node.func in (Xor, Not):
                            valid = checked.get(node)
                            if valid is None:
                                masked = node
                                has_residual = False
                                while masked.func in (Xor, Not):
                                    next_masked = None
                                    for arg in masked.args:
                                        if arg.has(atom):
                                            if next_masked is not None:
                                                next_masked = None
                                                break
                                            next_masked = arg
                                        elif masked.func is Xor:
                                            has_residual = True
                                    if next_masked is None:
                                        break
                                    masked = next_masked
                                valid = masked == atom and has_residual
                                checked[node] = valid
                            if valid:
                                entry = candidates.get(node)
                                if entry is not None:
                                    entry[0] += 1
                                    entry[1] = min(entry[1], depth)
                                else:
                                    candidates[node] = [1, depth]
                                if occurrences == 1:
                                    break
                        for arg in reversed(node.args):
                            if arg.has(atom):
                                pending.append((arg, depth + 1))
                if not candidates:
                    continue
                anchor = None
                best = None
                for node, (count, depth) in candidates.items():
                    score = (-count, depth)
                    if best is None or score < best:
                        best, anchor = (score, node)
                terms, phase = (set(), False)
                pending = [anchor]
                while pending:
                    term = pending.pop()
                    if term.func is Xor:
                        pending.extend(term.args)
                    elif term.func is Not:
                        phase = not phase
                        pending.append(term.args[0])
                    elif term == True:
                        phase = not phase
                    elif term == False:
                        continue
                    elif term in terms:
                        terms.remove(term)
                    else:
                        terms.add(term)
                replacement = Xor(*terms, phase)
                sub = {atom: replacement, anchor: atom}
                if self._substitution_steps is not None and len(self._substitution_steps) < 8:
                    self._substitution_steps.append(sub.copy())
                updates = {
                    i: self._normalize_boolean(P[i].xreplace(sub), normalized) for i in affected
                }
                used_masks.add(r)
                break
            if updates is None:
                return False
            deleted = False
            for i, new_expr in updates.items():
                if componentwise_hw and new_expr is None:
                    new_expr = slot_zero
                if new_expr == P[i]:
                    continue
                for rr, count in observation_counts[i].items():
                    mask_counts[rr] -= count
                new_row = None
                if new_expr is not None:
                    new_row = count_cache.get(new_expr)
                    if new_row is None:
                        s = cached_text(new_expr)
                        new_row = {r: count for r, scan in mask_scans if (count := len(scan(s)))}
                        count_cache[new_expr] = new_row
                    for rr, count in new_row.items():
                        mask_counts[rr] += count
                else:
                    deleted = True
                P[i] = new_expr
                observation_counts[i] = new_row
            if deleted:
                P = [expr for expr in P if expr is not None]
                self.P = P
                observation_counts = [row for row in observation_counts if row is not None]

    def _static_field(self, preserve_layout, componentwise_hw, remember, cached_text):
        slot_zero = Integer(0)
        count_cache = self._static_cache["counts"]
        if len(count_cache) >= 8192:
            count_cache.clear()
        P = self.P
        test = self._test_security
        if test():
            return True
        field = self.GF_field
        q = int(field.order)
        binary = field.characteristic == 2 and field.degree > 1
        if not binary and field.degree != 1:
            return False
        constants = {Integer(0): 0, Integer(1): 1}
        seen = set()
        pending = [(expr, True) for expr in P]
        while pending:
            node, leakage = pending.pop()
            if (node, leakage) in seen:
                continue
            seen.add((node, leakage))
            if node.is_Integer:
                value = abs(int(node)) if binary else int(node) % q
                if value >= q:
                    return False
                constants[node] = value
            elif node.is_Symbol:
                continue
            elif node.func is EncodedXor and leakage:
                pending.extend(((arg, True) for arg in node.args))
            elif node.is_Add or node.is_Mul:
                pending.extend(((arg, False) for arg in node.args))
            elif node.is_Pow and node.exp.is_Integer and (node.exp >= 0):
                pending.append((node.base, False))
            else:
                return False
        mask_symbols = {str(r): symbols(r) if isinstance(r, str) else r for r in self.randoms}
        mask_names = sorted(mask_symbols)
        patterns = self.compiled_patterns_random
        mask_scans = [(r, patterns[r].findall) for r in mask_names]
        mask_counts = dict.fromkeys(mask_names, 0)
        observation_counts = [None] * len(P)
        used_masks = set()
        inverses = {1: 1}
        updates = dict(enumerate(P))
        sub = {}
        while True:
            rebuilt = dict(sub)
            deleted = False
            for i, expr in updates.items():
                new_expr = None
                if expr is not None:
                    pending = [(expr, False)]
                    while pending:
                        node, ready = pending.pop()
                        if node in rebuilt:
                            continue
                        if node.is_Integer:
                            value = constants.get(node)
                            if value is None:
                                value = abs(int(node)) if binary else int(node) % q
                                constants[node] = value
                            rebuilt[node] = Integer(value)
                            continue
                        if node.is_Symbol:
                            rebuilt[node] = node
                            continue
                        children = (node.base,) if node.is_Pow else node.args
                        if not ready:
                            pending.append((node, True))
                            pending.extend(
                                (
                                    (child, False)
                                    for child in reversed(children)
                                    if child not in rebuilt
                                )
                            )
                            continue
                        args = [rebuilt[child] for child in children]
                        if node.is_Add or (
                            node.func is EncodedXor and field.characteristic == 2
                        ):
                            terms = {}
                            work = list(args)
                            while work:
                                term = work.pop()
                                if term.is_Add:
                                    work.extend(term.args)
                                    continue
                                if term.is_Integer:
                                    key, coefficient = (Integer(1), int(term))
                                elif term.is_Mul and term.args[0].is_Integer:
                                    coefficient = int(term.args[0])
                                    factors = term.args[1:]
                                    key = (
                                        factors[0]
                                        if len(factors) == 1
                                        else Mul(*factors, evaluate=False)
                                    )
                                else:
                                    key, coefficient = (term, 1)
                                old = terms.get(key, 0)
                                terms[key] = (
                                    old ^ coefficient if binary else (old + coefficient) % q
                                )
                            result = []
                            for term, coefficient in terms.items():
                                if not coefficient:
                                    continue
                                if term == 1:
                                    result.append(Integer(coefficient))
                                elif coefficient == 1:
                                    result.append(term)
                                elif term.is_Mul:
                                    result.append(
                                        Mul(Integer(coefficient), *term.args, evaluate=False)
                                    )
                                else:
                                    result.append(
                                        Mul(Integer(coefficient), term, evaluate=False)
                                    )
                            if len(result) > 1:
                                result.sort(key=cached_text)
                            new = (
                                Integer(0)
                                if not result
                                else (
                                    result[0]
                                    if len(result) == 1
                                    else Add(*result, evaluate=False)
                                )
                            )
                        elif node.is_Mul:
                            coefficient, factors = (1, [])
                            work = list(args)
                            while work:
                                term = work.pop()
                                if term.is_Mul:
                                    work.extend(term.args)
                                elif term.is_Integer:
                                    value = int(term)
                                    coefficient = (
                                        int(field(coefficient) * field(value))
                                        if binary
                                        else coefficient * value % q
                                    )
                                else:
                                    factors.append(term)
                            if len(factors) > 1:
                                factors.sort(key=cached_text)
                            if not coefficient:
                                new = Integer(0)
                            elif not factors:
                                new = Integer(coefficient)
                            elif coefficient == 1:
                                new = (
                                    factors[0]
                                    if len(factors) == 1
                                    else Mul(*factors, evaluate=False)
                                )
                            elif len(factors) == 1 and factors[0].is_Add:
                                scaled = []
                                for term in factors[0].args:
                                    old = (
                                        int(term)
                                        if term.is_Integer
                                        else (
                                            int(term.args[0])
                                            if term.is_Mul and term.args[0].is_Integer
                                            else 1
                                        )
                                    )
                                    value = (
                                        int(field(coefficient) * field(old))
                                        if binary
                                        else coefficient * old % q
                                    )
                                    if term.is_Integer:
                                        scaled.append(Integer(value))
                                    else:
                                        tail = (
                                            term.args[1:]
                                            if term.is_Mul and term.args[0].is_Integer
                                            else term.args if term.is_Mul else (term,)
                                        )
                                        scaled.append(
                                            (
                                                tail[0]
                                                if len(tail) == 1
                                                else Mul(*tail, evaluate=False)
                                            )
                                            if value == 1
                                            else Mul(Integer(value), *tail, evaluate=False)
                                        )
                                if len(scaled) > 1:
                                    scaled.sort(key=cached_text)
                                new = Add(*scaled, evaluate=False)
                            else:
                                new = Mul(Integer(coefficient), *factors, evaluate=False)
                        elif node.func is EncodedXor:
                            new = EncodedXor(*args)
                        else:
                            base, exponent = (args[0], node.exp)
                            if exponent == 0:
                                new = Integer(1)
                            elif exponent == 1:
                                new = base
                            elif base.is_Integer:
                                value = (
                                    int(field(int(base)) ** ((int(exponent) - 1) % (q - 1) + 1))
                                    if binary
                                    else pow(int(base), int(exponent), q)
                                )
                                new = Integer(value)
                            else:
                                new = node.func(base, exponent, evaluate=False)
                        rebuilt[node] = new
                    new_expr = rebuilt[expr]
                    if new_expr.is_Integer and (not preserve_layout):
                        new_expr = None
                old_row = observation_counts[i]
                if old_row is not None and new_expr == P[i]:
                    continue
                if old_row is not None:
                    for r, count in old_row.items():
                        mask_counts[r] -= count
                new_row = None
                if new_expr is not None:
                    new_row = count_cache.get(new_expr)
                    if new_row is None:
                        text = cached_text(new_expr)
                        new_row = {r: count for r, scan in mask_scans if (count := len(scan(text)))}
                        count_cache[new_expr] = new_row
                    for r, count in new_row.items():
                        mask_counts[r] += count
                else:
                    deleted = True
                P[i], observation_counts[i] = (new_expr, new_row)
            if deleted:
                P = [expr for expr in P if expr is not None]
                self.P = P
                observation_counts = [row for row in observation_counts if row is not None]
            sub = {}
            if remember is not None:
                remember()
            if test():
                return True
            deleted = False
            for r in mask_names if not preserve_layout or componentwise_hw else ():
                if mask_counts[r] != 1:
                    continue
                atom = mask_symbols[r]
                for i, row in enumerate(observation_counts):
                    if row is None or not row.get(r, 0):
                        continue
                    masked = P[i]
                    while masked.is_Add or masked.is_Mul:
                        child = None
                        valid = True
                        for arg in masked.args:
                            if arg.has(atom):
                                if child is not None:
                                    valid = False
                                    break
                                child = arg
                            elif masked.is_Mul and (not arg.is_Integer or arg == 0):
                                valid = False
                                break
                        if not valid or child is None:
                            break
                        masked = child
                    if masked == atom:
                        for rr, count in row.items():
                            mask_counts[rr] -= count
                        if componentwise_hw:
                            P[i], observation_counts[i] = (slot_zero, {})
                        else:
                            P[i], observation_counts[i] = (None, None)
                        deleted = True
                    break
            if deleted:
                P = [expr for expr in P if expr is not None]
                self.P = P
                observation_counts = [row for row in observation_counts if row is not None]
                updates = {}
                continue
            updates = None
            ordered = sorted(((mask_counts[r], r) for r in mask_names if mask_counts[r]))
            for occurrences, r in ordered:
                atom = mask_symbols[r]
                affected = [i for (i, row) in enumerate(observation_counts) if row.get(r, 0)]
                parts, candidates = ({}, {})
                for root_pass in (False,) if preserve_layout else (True, False):
                    if not root_pass and r in used_masks:
                        break
                    for i in affected:
                        pending = [(P[i], 0)]
                        while pending:
                            node, depth = pending.pop()
                            if node not in parts:
                                coefficient, residual, valid = (0, {}, True)
                                work = [(node, 1)]
                                while work:
                                    term, scale = work.pop()
                                    if not term.has(atom):
                                        old = residual.get(term, 0)
                                        residual[term] = (
                                            old ^ scale if binary else (old + scale) % q
                                        )
                                    elif term == atom:
                                        coefficient = (
                                            coefficient ^ scale
                                            if binary
                                            else (coefficient + scale) % q
                                        )
                                    elif term.is_Add:
                                        work.extend(((arg, scale) for arg in term.args))
                                    elif term.is_Mul:
                                        child = None
                                        for arg in term.args:
                                            if arg.is_Integer:
                                                scale = (
                                                    int(field(scale) * field(int(arg)))
                                                    if binary
                                                    else scale * int(arg) % q
                                                )
                                            elif child is None:
                                                child = arg
                                            else:
                                                valid = False
                                                break
                                        if not valid or child is None:
                                            valid = False
                                            break
                                        work.append((child, scale))
                                    else:
                                        valid = False
                                        break
                                residual = {
                                    term: scale for (term, scale) in residual.items() if scale
                                }
                                parts[node] = (
                                    (coefficient, residual) if valid and coefficient else None
                                )
                            part = parts[node]
                            if not root_pass and part is not None and part[1]:
                                entry = candidates.get(node)
                                if entry is None:
                                    candidates[node] = [1, depth]
                                else:
                                    entry[0] += 1
                                    entry[1] = min(entry[1], depth)
                                if occurrences == 1:
                                    break
                            if root_pass:
                                break
                            children = (node.base,) if node.is_Pow else node.args
                            pending.extend(
                                (
                                    (arg, depth + 1)
                                    for arg in reversed(children)
                                    if arg.has(atom)
                                )
                            )
                    if root_pass and all((parts[P[i]] is not None for i in affected)):
                        anchor_i = affected[0]
                        a0, e0 = parts[P[anchor_i]]
                        inverse = inverses.get(a0)
                        if inverse is None:
                            inverse = int(field(a0) ** (-1)) if binary else pow(a0, -1, q)
                            inverses[a0] = inverse
                        updates = {anchor_i: None}
                        for i in affected[1:]:
                            ai, ei = parts[P[i]]
                            ratio = (
                                int(field(ai) * field(inverse)) if binary else ai * inverse % q
                            )
                            difference = dict(ei)
                            for term, scale in e0.items():
                                value = (
                                    int(field(ratio) * field(scale))
                                    if binary
                                    else ratio * scale % q
                                )
                                old = difference.get(term, 0)
                                difference[term] = old ^ value if binary else (old - value) % q
                            terms = [
                                (
                                    term
                                    if scale == 1
                                    else Mul(Integer(scale), term, evaluate=False)
                                )
                                for (term, scale) in difference.items()
                                if scale
                            ]
                            updates[i] = Add(*terms, evaluate=False) if terms else Integer(0)
                        break
                if updates is not None:
                    for i, expr in updates.items():
                        if expr is not None and (not expr.free_symbols):
                            updates[i] = None
                    break
                if not candidates:
                    continue
                anchor, best = (None, None)
                for node, (count, depth) in candidates.items():
                    score = (-count, depth)
                    if best is None or score < best:
                        best, anchor = (score, node)
                coefficient, residual = parts[anchor]
                inverse = inverses.get(coefficient)
                if inverse is None:
                    inverse = (
                        int(field(coefficient) ** (-1)) if binary else pow(coefficient, -1, q)
                    )
                    inverses[coefficient] = inverse
                terms = [atom if inverse == 1 else Mul(Integer(inverse), atom, evaluate=False)]
                for term, scale in residual.items():
                    value = (
                        int(field(inverse) * field(scale)) if binary else -inverse * scale % q
                    )
                    if value:
                        terms.append(
                            term if value == 1 else Mul(Integer(value), term, evaluate=False)
                        )
                replacement = Add(*terms, evaluate=False)
                sub = {atom: replacement, anchor: atom}
                if self._substitution_steps is not None and len(self._substitution_steps) < 8:
                    self._substitution_steps.append(sub.copy())
                updates = {i: P[i] for i in affected}
                used_masks.add(r)
                break
            if updates is None:
                return False

    @staticmethod
    def _normalize_boolean(expr, cache):
        pending = [(expr, False)]
        while pending:
            node, ready = pending.pop()
            if node in cache:
                continue
            if not node.args:
                cache[node] = node
                continue
            if not ready:
                pending.append((node, True))
                pending.extend(((arg, False) for arg in node.args if arg not in cache))
                continue
            args = [cache[arg] for arg in node.args]
            if node.func is Xor:
                terms, phase = (set(), False)
                work = list(args)
                while work:
                    term = work.pop()
                    if term.func is Xor:
                        work.extend(term.args)
                    elif term.func is Not:
                        phase = not phase
                        work.append(term.args[0])
                    elif term == True:
                        phase = not phase
                    elif term == False:
                        continue
                    elif term in terms:
                        terms.remove(term)
                    else:
                        terms.add(term)
                if (
                    not phase
                    and len(terms) > 1
                    and (getattr(node, "_argset", None) == terms)
                    and (not any((term.is_Relational for term in terms)))
                ):
                    cache[node] = node
                else:
                    cache[node] = Xor(*terms, phase)
            else:
                cache[node] = node.func(*args)
        return cache[expr]

    @staticmethod
    def _residual_cost(probes, cache, source_cache=None, ignore_constants=False):
        if source_cache is None:
            source_cache = ({}, {})
        root_sources, source_indices = source_cache
        sources = 0
        nodes = slots = 0
        for expr in probes:
            if ignore_constants and (expr.is_Integer or expr in (False, True)):
                continue
            slots += 1
            source_bits = root_sources.get(expr)
            if source_bits is None:
                source_bits = 0
                for symbol in expr.free_symbols:
                    index = source_indices.get(symbol)
                    if index is None:
                        index = len(source_indices)
                        source_indices[symbol] = index
                    source_bits |= 1 << index
                root_sources[expr] = source_bits
            sources |= source_bits
            cached_nodes = cache.get(expr)
            if cached_nodes is not None:
                nodes += cached_nodes
                continue
            pending = [(expr, False)]
            while pending:
                node, ready = pending.pop()
                if node in cache:
                    continue
                if ready or not node.args:
                    cache[node] = 1 + sum((cache[arg] for arg in node.args))
                else:
                    pending.append((node, True))
                    pending.extend(((arg, False) for arg in node.args if arg not in cache))
            nodes += cache[expr]
        return (sources.bit_count(), nodes, slots)

    def _initialize_random_statistics(self):
        wires = len(self.gadget.observationsIn)
        totals = [comb(wires, order) for order in range(wires + 1)]

        def counts():
            return {"lower": [0] * (wires + 1), "upper": list(totals)}

        stats = {
            "model": self.model_str,
            "wires": wires,
            "threshold": self.t,
            "technique": self.gadget.checkOptions["tech."],
            "field": self.gadget.field,
            "bits": self.Bits,
            "share_count": self.shareNum,
            "processed_by_order": [0] * (wires + 1),
            "requests": [],
            **counts(),
        }
        if self.model_str == "rps_share":
            stats.update(
                security_property="rps_share",
                simulation_share_budget=self.shareNum - 1,
                simulation_input_domain="independent_input_shares",
                mi_quantity="minimum_conditional_mutual_information",
            )
        stats.update(
            robust=list(self.gadget.checkOptions["robust"]),
            sampling_unit="physical_wire",
            transition_history="none",
            requested_outputs="joint_stable_noiseless",
            channel_order="sample_positions_joint_values",
            wire_locations=tuple(self.gadget.random_wire_locations),
            wire_values=tuple(map(str, self.gadget.observationsIn)),
            check_options=dict(self.gadget.checkOptions),
        )
        self.rp_events = (
            [
                event
                for size in range(1, self.len_secrets + 1)
                for event in combinations(range(self.len_secrets), size)
            ]
            if self.model_str == "rpe"
            else []
        )
        if self.model_str == "rpc":
            self.rp_requests = self.rp_metadata["rpc"]
            stats["requests"] = [
                {"request": tuple(map(str, request)), **counts()}
                for request in self.rp_requests
            ]
        elif self.model_str == "rpe":
            self.rp_requests = self.rp_metadata["rpe_requests"]
            stats["requests"] = [
                {
                    "request": item["request"],
                    "expanded_outputs": item["expanded_outputs"],
                    "events": [{"inputs": event, **counts()} for event in self.rp_events],
                }
                for item in self.rp_requests
            ]
            self.Ci_list = {
                kind: {event: list(totals) for event in self.rp_events}
                for kind in ("rpe1", "rpe2")
            }
        else:
            self.rp_requests = []
        if self.model_str != "rpe":
            self.Ci_list = stats["upper"]
        self.rp_statistics = stats
        self.gadget.rp_statistics = stats
        self._rp_stop_reason = None

    def _evaluate_random_request(self, item, requested_outputs=()):
        outputs = [self.OutputProbe[wire] for wire in requested_outputs]
        original_probes = list(item) + outputs
        self.P = list(original_probes)
        self.P_channel_count = None
        self.P_xor_groups = ()
        self.choice_rpe = tuple()
        self.rpe_input_indices = self._empty_rpe_indices
        channel_key = frozenset(self.P)
        cache = ("random", self.model_str, self.t, self.tech, channel_key)
        evaluated = self._evaluate_probes(cache)
        mi, exact_zero = (evaluated["mi"], evaluated["exact_zero"])
        mi_text = evaluated["mi_text"]
        failed = bool(self.choice_rpe) if self.model_str == "rpe" else exact_zero is not True
        return {
            "cache": cache,
            "mi": mi,
            "choice_rpe": self.choice_rpe,
            "mi_text": mi_text,
            "rpe_input_indices": self.rpe_input_indices,
            "unknown": exact_zero is None,
            "exact_zero": exact_zero,
            "failed": failed,
            "leakage": original_probes if failed else [],
        }

    def _check_random_observation(self, item, start_time):
        reason = self._limit_reason(start_time)
        if reason:
            return {"processed": False, "abort": None, "stop_reason": reason}
        self._reset_observation()
        self.O = item
        checks = []
        if self.model_str in ("rps_secret", "rps_share"):
            checks.append(self._evaluate_random_request(item))
        elif self.model_str == "rpc":
            for request in self.rp_requests:
                checks.append(self._evaluate_random_request(item, request))
        else:
            for request in self.rp_requests:
                best = None
                best_rank = None
                certain_events = set(self.rp_events)
                possible_events = set(self.rp_events)
                for output_choice in request["choices"]:
                    candidate = self._evaluate_random_request(item, output_choice)
                    if candidate["unknown"]:
                        certain_events.clear()
                    else:
                        failed_inputs = set(candidate["choice_rpe"])
                        events = {
                            event for event in self.rp_events if failed_inputs.issuperset(event)
                        }
                        certain_events.intersection_update(events)
                        possible_events.intersection_update(events)
                    rank = (
                        len(candidate["choice_rpe"]),
                        candidate["choice_rpe"],
                        tuple(map(str, output_choice)),
                    )
                    if best_rank is None or rank < best_rank:
                        best, best_rank = (candidate, rank)
                        best["output_choice"] = tuple(map(str, output_choice))
                if best is None:
                    raise RuntimeError("RPE output request has no admissible choice")
                best["event_failures"] = [
                    {
                        "inputs": event,
                        "lower": event in certain_events,
                        "upper": event in possible_events,
                    }
                    for event in self.rp_events
                ]
                checks.append(best)
        failed = any((check["failed"] for check in checks))
        reason = self._limit_reason(start_time)
        if self.abort and failed:
            reason = "Stopped at an unverified observation (--abort)"
        return {
            "processed": True,
            "abort": None if reason else False,
            "stop_reason": reason,
            "verify": not failed,
            "Ci": self.Ci,
            "row": tuple(map(str, item)),
            "mi": (
                -1
                if any((check["unknown"] for check in checks))
                else max((check["mi"] for check in checks), default=0)
            ),
            "requests": checks,
        }

    def _aggregate_random_result(self, result):
        order = result["Ci"]
        stats = self.rp_statistics
        weight = result.get("batch_count", 1)

        def record(counts, lower, upper):
            counts["lower"][order] += weight * int(lower)
            counts["upper"][order] += weight * (int(upper) - 1)

        checks = result["requests"]
        stats["processed_by_order"][order] += weight
        record(
            stats,
            any((check["failed"] and (not check["unknown"]) for check in checks)),
            any((check["failed"] for check in checks)),
        )
        for index, check in enumerate(checks):
            if self.mcore > 0 and "batch_count" not in result:
                cache = check["cache"]
                self.observation_cache[cache] = check["mi"]
                self.exact_zero_cache[cache] = check["exact_zero"]
                if check.get("mi_text") is not None:
                    self.mi_text_cache[cache] = check["mi_text"]
                if self.model_str == "rpe":
                    self.choice_rpe_cache[cache] = check["choice_rpe"]
                    self.rpe_witness_cache[cache] = check["rpe_input_indices"]
            if check["failed"]:
                self.leakage.extend(check["leakage"])
                self.gadget.row_verdict[order, result["row"], index] = (
                    "unknown" if check["unknown"] else "insecure"
                )
                self.gadget.row_mi[order, result["row"], index] = check["mi"]
                self.gadget.row_mi_text[order, result["row"], index] = check.get("mi_text")
            if self.model_str == "rpc":
                record(
                    stats["requests"][index],
                    check["failed"] and (not check["unknown"]),
                    check["failed"],
                )
            elif self.model_str == "rpe":
                for event_index, event in enumerate(stats["requests"][index]["events"]):
                    decision = check["event_failures"][event_index]
                    record(event, decision["lower"], decision["upper"])
        if self.model_str == "rpe":
            for kind in ("rpe1", "rpe2"):
                selected = [
                    check
                    for (index, check) in enumerate(checks)
                    if bool(stats["requests"][index]["expanded_outputs"]) == (kind == "rpe2")
                ]
                for event, counts in self.Ci_list[kind].items():
                    occurs = any(
                        (set(event).issubset(check["choice_rpe"]) for check in selected)
                    )
                    counts[order] += weight * (int(occurs) - 1)

    def _random_result(self):
        size = len(self.gadget.observationsIn)
        stopped = self._rp_stop_reason
        stats = self.rp_statistics
        stats["complete"] = all(
            (
                count == comb(size, order)
                for (order, count) in enumerate(stats["processed_by_order"])
            )
        )
        stats["enumeration_complete"] = stats["complete"]
        stats["stop_reason"] = stopped
        if self.model_str == "rpc":
            for bound in ("lower", "upper"):
                stats[bound][:] = [
                    max(values)
                    for values in zip(*(request[bound] for request in stats["requests"]))
                ]
            stats["coefficient_aggregation"] = "maximum_per_output_request"
        elif self.model_str == "rpe":
            aggregate = {}
            for request in stats["requests"]:
                pattern = tuple(request["expanded_outputs"])
                for event in request["events"]:
                    key = (pattern, tuple(event["inputs"]))
                    if key not in aggregate:
                        aggregate[key] = {
                            "expanded_outputs": pattern,
                            "inputs": key[1],
                            "lower": list(event["lower"]),
                            "upper": list(event["upper"]),
                        }
                    else:
                        for bound in ("lower", "upper"):
                            aggregate[key][bound] = list(
                                map(max, zip(aggregate[key][bound], event[bound]))
                            )
            stats["coefficient_events"] = list(aggregate.values())
            stats["coefficient_aggregation"] = "maximum_per_fixed_output_request"
            for kind in ("rpe1", "rpe2"):
                for inputs, counts in self.Ci_list[kind].items():
                    selected = [
                        event["upper"]
                        for event in aggregate.values()
                        if event["inputs"] == inputs
                        and bool(event["expanded_outputs"]) == (kind == "rpe2")
                    ]
                    if selected:
                        counts[:] = list(map(max, zip(*selected)))

        bounds_cache = {}

        def summarize(counts, degree=1):
            key = (tuple(counts["upper"]), tuple(counts["lower"]), degree)
            bound = bounds_cache.get(key)
            if bound is None:
                bound = self.probability_bounds(key[0], key[1], k=degree)
                bounds_cache[key] = bound
            counts["bounds"] = {
                key: str(bound[key]) for key in ("lower", "upper", "union_upper")
            }
            counts["bounds"]["exact"] = bound["complete"]
            counts["bounds"]["threshold"] = bound["threshold"]
            return bound

        if self.model_str == "rps_secret":
            summary = summarize(stats)
            summary.update(
                self.probability_envelope([{**stats, "label": "RPS_secret"}], basis="power")
            )
        elif self.model_str == "rps_share":
            summarize(stats)
            summary = self.probability_envelope([{**stats, "label": "RPS_share"}])
        elif self.model_str == "rpc":
            for request in stats["requests"]:
                summarize(request)
            summary = self.probability_envelope([{**stats, "label": "RPC"}])
        else:
            for request in stats["requests"]:
                for event in request["events"]:
                    summarize(event, len(event["inputs"]))
            summary = self.probability_envelope(
                [
                    {
                        **event,
                        "degree": len(event["inputs"]),
                        "label": {
                            "expanded_outputs": event["expanded_outputs"],
                            "inputs": event["inputs"],
                        },
                    }
                    for event in stats["coefficient_events"]
                ]
            )
        stats["threshold_bounds"] = {
            key: summary[key]
            for key in (
                "p_min",
                "p_max",
                "log2_p_min",
                "log2_p_max",
                "threshold_scope",
                "basis",
            )
        }
        stats["reported_function"] = {"kind": "coefficient_failure_bound", **summary}
        self.random_summary = summary
        self.gadget.rp_statistics = stats
        return stats

    @staticmethod
    def _counts(values, limits):
        values = tuple(values)
        if len(values) != len(limits):
            raise ValueError("Expected one coefficient for every subset size, including zero")
        if any(
            (
                int(value) != value or value < 0 or value > limits[index]
                for (index, value) in enumerate(values)
            )
        ):
            raise ValueError("Failure counts must lie between zero and the number of subsets")
        return tuple(map(int, values))

    @staticmethod
    def _polynomial_text(power):
        terms = []
        for degree in range(len(power) - 1, -1, -1):
            coefficient = power[degree]
            if not coefficient:
                continue
            magnitude = abs(coefficient)
            variable = "" if degree == 0 else "p" if degree == 1 else f"p**{degree}"
            body = (
                str(magnitude)
                if not variable
                else variable if magnitude == 1 else f"{magnitude}*{variable}"
            )
            terms.append(("-" if coefficient < 0 else "+", body))
        if not terms:
            return "0"
        sign, body = terms[0]
        return (
            ("-" if sign == "-" else "")
            + body
            + "".join((f" {sign} {body}" for (sign, body) in terms[1:]))
        )

    @staticmethod
    def contraction_threshold(coefficients, k=1, *, return_bounds=False):
        coefficients = tuple(coefficients)
        if not isinstance(k, int) or k < 1:
            raise ValueError("k must be a positive integer")
        if any((int(value) != value or value < 0 for value in coefficients)):
            raise ValueError("Expected nonnegative integer coefficients")
        if any(coefficients[:k]):
            return (0.0, 0.0, None, None) if return_bounds else 0.0
        constant = coefficients[k] if k < len(coefficients) else 0
        if constant >= 1:
            return (0.0, 0.0, None, None) if return_bounds else 0.0
        terms = [
            (index - k, log(int(count)))
            for index, count in enumerate(coefficients)
            if count and index > k
        ]
        if not terms or sum(coefficients) <= 1:
            return (1.0, 1.0, 0.0, 0.0) if return_bounds else 1.0

        def below(log_p):
            total = float(constant)
            for degree, log_count in terms:
                term = log_count + degree * log_p
                if term >= 0:
                    return False
                total += exp(term)
                if total >= 1:
                    return False
            return True

        lower = -1.0
        while not below(lower):
            lower = max(-745.0, lower * 2) if lower > -745.0 else lower * 2
        upper = 0.0
        for _ in range(80):
            middle = (lower + upper) / 2
            if below(middle):
                lower = middle
            else:
                upper = middle

        def exact_below(value):
            numerator, denominator = value.as_integer_ratio()
            total, scale = 0, 1
            for coefficient in reversed(coefficients[k:]):
                total = total * numerator + int(coefficient) * scale
                scale *= denominator
            return total < scale // denominator

        threshold = nextafter(exp(lower), 0.0)
        while threshold > 0 and not exact_below(threshold):
            threshold = nextafter(threshold, 0.0)
        logarithm = log2(threshold) if threshold > 0 else lower / log(2)
        upper_threshold = exp(upper)
        upper_threshold = min(1.0, nextafter(upper_threshold, float("inf")))
        while upper_threshold < 1 and exact_below(upper_threshold):
            upper_threshold = nextafter(upper_threshold, float("inf"))
        upper_logarithm = log2(upper_threshold)
        return (
            (threshold, upper_threshold, logarithm, upper_logarithm)
            if return_bounds
            else threshold
        )

    @staticmethod
    def probability_bounds(upper_coefficients, lower_coefficients=None, *, k=1):
        upper_coefficients = tuple(upper_coefficients)
        if not upper_coefficients:
            raise ValueError("At least the zero-order coefficient is required")
        size = len(upper_coefficients) - 1
        limits = [1]
        for index in range(size):
            limits.append(limits[-1] * (size - index) // (index + 1))
        upper = Verifier._counts(upper_coefficients, limits)
        lower = Verifier._counts(
            (0,) * (size + 1) if lower_coefficients is None else lower_coefficients, limits
        )
        if any((lo > hi for (lo, hi) in zip(lower, upper))):
            raise ValueError("Lower failure counts exceed the upper counts")
        p = Symbol("p")
        weighted = []
        for values in (lower, upper):
            nonzero = [(index, count) for index, count in enumerate(values) if count]
            deficits = [
                (index, limits[index] - count)
                for index, count in enumerate(values)
                if count != limits[index]
            ]
            weighted.append(
                Integer(1)
                - Add(
                    *(
                        Integer(count) * p**index * (1 - p) ** (size - index)
                        for index, count in deficits
                    )
                )
                if len(deficits) < len(nonzero)
                else Add(
                    *(
                        Integer(count) * p**index * (1 - p) ** (size - index)
                        for index, count in nonzero
                    )
                )
            )

        union = (
            (1 + p) ** size - Add(*(Integer(count) * p**index for (index, count) in deficits))
            if len(deficits) < len(nonzero)
            else Add(*(Integer(count) * p**index for (index, count) in nonzero))
        )
        return {
            "wires": size,
            "lower_coefficients": lower,
            "upper_coefficients": upper,
            "lower": weighted[0],
            "upper": weighted[1],
            "union_upper": union,
            "complete": lower == upper,
            "threshold": Verifier.contraction_threshold(upper, k),
            "root_degree": k,
        }

    @staticmethod
    def certified_probability_summary(coefficients, *, k=1, basis="bernoulli"):
        from sympy import Poly

        counts = tuple(coefficients)
        size = len(counts) - 1
        if not isinstance(k, int) or k < 1:
            raise ValueError("k must be a positive integer")
        if size < 0:
            raise ValueError("At least one coefficient is required")
        Verifier._counts(counts, [comb(size, i) for i in range(size + 1)])
        if basis not in ("power", "bernoulli"):
            raise ValueError("Expected power or bernoulli probability basis")
        if basis == "power":
            power = list(counts)
        else:
            power = []
            for i, count in enumerate(counts):
                power.append(
                    count - sum(value * comb(size - j, i - j) for j, value in enumerate(power))
                )
            while len(power) > 1 and power[-1] == 0:
                power.pop()
        result = {
            "upper_coefficients": counts,
            "root_degree": k,
            "probability_expression": Verifier._polynomial_text(power),
            "series_coefficients": power,
            "threshold": 0.0,
            "log2_threshold": None,
            "threshold_upper": 0.0,
            "log2_threshold_upper": None,
            "basis": basis,
            "threshold_interval": None,
            "threshold_method": "exact_integer_root_isolation",
        }
        if basis == "power":
            threshold, upper_threshold, logarithm, upper_logarithm = (
                Verifier.contraction_threshold(counts, k, return_bounds=True)
            )
            result.update(
                threshold=threshold,
                log2_threshold=logarithm,
                threshold_upper=upper_threshold,
                log2_threshold_upper=upper_logarithm,
                threshold_method="log_domain_bisection",
            )
            return result
        if not any(counts):
            result.update(
                threshold=1.0,
                log2_threshold=0.0,
                threshold_upper=1.0,
                log2_threshold_upper=0.0,
                threshold_interval=["1", "1"],
            )
            return result
        if size < k:
            return result
        difference = [
            value - (comb(size - k, i - k) if i >= k else 0) for (i, value) in enumerate(counts)
        ]
        signs = [1 if value > 0 else -1 for value in difference if value]
        if not signs or signs[0] > 0:
            return result
        if all((sign < 0 for sign in signs)):
            result.update(
                threshold=nextafter(1.0, 0.0) if counts[-1] == 1 else 1.0,
                log2_threshold=log2(nextafter(1.0, 0.0)) if counts[-1] == 1 else 0.0,
                threshold_upper=1.0,
                log2_threshold_upper=0.0,
                threshold_interval=["1", "1"],
            )
            return result
        changes = sum((left != right for (left, right) in zip(signs, signs[1:])))
        if changes == 1:
            low, high = (Fraction(0), Fraction(1))

            def value_at(p):
                a, b = (p.numerator, p.denominator)
                return sum(
                    (
                        value * a**i * (b - a) ** (size - i)
                        for (i, value) in enumerate(difference)
                        if value
                    )
                )

            while True:
                middle = (low + high) / 2
                if value_at(middle) < 0:
                    low = middle
                else:
                    high = middle
                if low and high - low <= low / 10**16:
                    break
        else:
            p = Symbol("p")
            polynomial = Poly(
                Add(*(Integer(value) * p**i for (i, value) in enumerate(power))) - p**k, p
            )
            polynomial = polynomial.exquo(
                Poly(p ** min((m[0][0] for m in polynomial.terms())), p)
            )
            polynomial = polynomial.sqf_part()
            if polynomial.eval(1) == 0:
                polynomial = polynomial.exquo(Poly(p - 1, p))
            intervals = polynomial.intervals(inf=0, sup=1)
            if not intervals:
                result.update(
                    threshold=nextafter(1.0, 0.0) if counts[-1] == 1 else 1.0,
                    log2_threshold=log2(nextafter(1.0, 0.0)) if counts[-1] == 1 else 0.0,
                    threshold_upper=1.0,
                    log2_threshold_upper=0.0,
                    threshold_interval=["1", "1"],
                )
                return result
            (left, right), _ = intervals[0]
            while left == 0 and right != left:
                left, right = polynomial.refine_root(left, right, eps=right / 2)
            if left != right:
                left, right = polynomial.refine_root(left, right, eps=left / 10**16)
            low, high = (
                Fraction(int(left.p), int(left.q)),
                Fraction(int(right.p), int(right.q)),
            )
        threshold = float(low)
        if threshold > 0:
            threshold = nextafter(threshold, 0.0)
        logarithm = (
            log2(threshold) if threshold > 0 else log2(low.numerator) - log2(low.denominator)
        )
        upper_threshold = float(high)
        if upper_threshold > 0:
            upper_threshold = min(1.0, nextafter(upper_threshold, float("inf")))
        upper_logarithm = (
            log2(upper_threshold)
            if upper_threshold > 0
            else log2(high.numerator) - log2(high.denominator)
        )
        result.update(
            threshold=threshold,
            log2_threshold=logarithm,
            threshold_upper=upper_threshold,
            log2_threshold_upper=upper_logarithm,
            threshold_interval=[str(low), str(high)],
        )
        return result

    @staticmethod
    def _near_zero_compare(left, right):
        a, b = (left["root_degree"], right["root_degree"])
        common = a * b // gcd(a, b)
        powers = []
        for branch, degree in ((left, a), (right, b)):
            values = branch["series_coefficients"]
            exponent = common // degree
            if exponent == 1:
                powers.append(values)
                continue
            result = [1]
            for _ in range(exponent):
                product = [0] * (len(result) + len(values) - 1)
                for i, coefficient in enumerate(result):
                    if coefficient:
                        for j, value in enumerate(values):
                            if value:
                                product[i + j] += coefficient * value
                result = product
            powers.append(result)
        lp, rp = powers
        for i in range(max(len(lp), len(rp))):
            difference = (lp[i] if i < len(lp) else 0) - (rp[i] if i < len(rp) else 0)
            if difference:
                return 1 if difference > 0 else -1
        return 0

    @staticmethod
    def probability_envelope(components, *, basis="bernoulli"):
        branches = []
        cache = {}
        for item in components:
            counts, degree = tuple(item["upper"]), item.get("degree", 1)
            lower = tuple(item.get("lower", (0,) * len(counts)))
            if len(lower) != len(counts) or any(lo > hi for lo, hi in zip(lower, counts)):
                raise ValueError("Lower failure counts exceed the upper counts")
            for values in (counts, lower):
                key = values, degree, basis
                if key not in cache:
                    cache[key] = Verifier.certified_probability_summary(
                        values, k=degree, basis=basis
                    )
            branch = dict(cache[counts, degree, basis])
            lower_summary = cache[lower, degree, basis]
            branch.update(
                label=item.get("label"),
                lower_coefficients=lower,
                p_min=branch["threshold"],
                p_max=lower_summary["threshold_upper"],
                log2_p_min=branch["log2_threshold"],
                log2_p_max=lower_summary["log2_threshold_upper"],
                p_max_interval=lower_summary["threshold_interval"],
            )
            polynomial = branch["probability_expression"]
            branch["base_probability_expression"] = polynomial
            branch["probability_expression"] = (
                polynomial if degree == 1 else "(" + polynomial + ")**(1/" + str(degree) + ")"
            )
            branches.append(branch)
        if not branches:
            raise ValueError("At least one probability component is required")
        active = []
        seen = set()
        for branch in branches:
            branch["active"] = not any(
                other is not branch
                and other["root_degree"] == branch["root_degree"]
                and len(other["upper_coefficients"]) == len(branch["upper_coefficients"])
                and all(
                    a >= b
                    for a, b in zip(other["upper_coefficients"], branch["upper_coefficients"])
                )
                and any(
                    a > b
                    for a, b in zip(other["upper_coefficients"], branch["upper_coefficients"])
                )
                for other in branches
            )
            key = branch["upper_coefficients"], branch["root_degree"]
            if branch["active"] and key not in seen:
                seen.add(key)
                active.append(branch)
        tight = min(
            branches,
            key=lambda branch: (
                branch["log2_p_min"] if branch["log2_p_min"] is not None else -float("inf")
            ),
        )
        optimistic = min(
            branches,
            key=lambda branch: (
                branch["log2_p_max"] if branch["log2_p_max"] is not None else -float("inf")
            ),
        )
        interval = None
        if all(branch["threshold_interval"] is not None for branch in branches):
            interval = [
                str(min(Fraction(branch["threshold_interval"][side]) for branch in branches))
                for side in (0, 1)
            ]
        local = max(active, key=cmp_to_key(Verifier._near_zero_compare))
        expressions = [branch["probability_expression"] for branch in active]
        return {
            "components": branches,
            "active_components": [branch["label"] for branch in branches if branch["active"]],
            "probability_expression": (
                expressions[0]
                if len(expressions) == 1
                else "Max(" + ", ".join(expressions) + ")"
            ),
            "threshold": tight["p_min"],
            "p_min": tight["p_min"],
            "p_max": optimistic["p_max"],
            "log2_p_min": tight["log2_p_min"],
            "log2_p_max": optimistic["log2_p_max"],
            "threshold_interval": interval,
            "threshold_method": (
                "minimum_of_component_thresholds"
                if basis == "power"
                else "minimum_of_exact_component_root_intervals"
            ),
            "threshold_scope": "coefficient_uncertainty_for_reported_function",
            "series_component": local,
            "basis": basis,
        }
