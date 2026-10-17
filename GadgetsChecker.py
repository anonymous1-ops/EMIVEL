from contextlib import ExitStack
from copy import copy
from fractions import Fraction
from functools import cmp_to_key
from itertools import combinations
from math import comb, exp, gcd, log, log2, nextafter
from multiprocessing import Pool, cpu_count
from re import escape, compile
from tempfile import TemporaryFile
import os
import pickle
import time
import psutil
from sympy import symbols, flatten, Add, sympify, Integer, Mul, Symbol
from sympy.logic.boolalg import Xor, Not
from auxiliary import EncodedXor
from GadgetsAnalysis import LeakageAnalyzer
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
        self._request_results = {}
        self._pending_requests = {}
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
        self._live_detail = self.event is not None and (self.detail or bool(watch))
        self._watch_locations = set()
        if self._live_detail and watch:
            locations = set(getattr(self.gadget, "probe_locations", {}).values())
            if self.randomprobing:
                locations.update(getattr(self.gadget, "random_wire_locations", ()))
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
        self.compiled_patterns_random = {
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

    def __getstate__(self):
        state = self.__dict__.copy()
        state["event"] = None
        state["_request_results"] = {}
        state["_pending_requests"] = {}
        state["_watch_locations"] = set()
        circuit = copy(self.gadget)
        circuit.instructions = ()
        circuit.__dict__.pop("expression_info", None)
        circuit.__dict__.pop("probe_locations", None)
        circuit.__dict__.pop("random_wire_locations", None)
        state["gadget"] = circuit
        quantifier = copy(self.MIA)
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
                    pending_count = self._process_observations(
                        tasks, total, start_time, spool=pending, pool=pool
                    )
                    if pending_count and self._check_stop_reason is None:
                        pending.seek(0)
                        self._phase = "mi"
                        tasks = (pickle.load(pending) for _ in range(pending_count))
                        self._process_observations(tasks, pending_count, start_time, pool=pool)
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
            "independence_decision": "static_proof_or_exact_integer_counts",
            "mi_numeric": "floating_point_from_exhaustive_counts",
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
        if self.event is not None:
            self.event("progress_start", {"total": total, "phase": self._phase})
        try:
            if pool is not None:
                chunksize = 1 if self.abort else min(5000, max(1, total // (self.mcore * 200)))
                phase = self._phase
                work = ((phase, task) for task in tasks)
                results = pool.imap_unordered(
                    Verifier._check_observation_worker, work, chunksize=chunksize
                )
            else:
                results = (self._check_task(task, start_time) for task in tasks)
            for result in results:
                if "deferred" in result:
                    pickle.dump(result["deferred"], spool, protocol=pickle.HIGHEST_PROTOCOL)
                    pending_count += 1
                self._record_result(result)
                if self.event is not None and result.get("processed", True):
                    self.event("progress", {"advance": 1})
                if result["abort"] is None:
                    if pool is not None:
                        pool.terminate()
                    break
        finally:
            if self.event is not None:
                self.event("progress_end", {})
        return pending_count

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
        order, item, completed, pending = task
        self.Ci = order
        self._request_results = completed or {}
        self._pending_requests = pending or {}
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
            if self._phase == "static" and self._pending_requests:
                resolved = {
                    key: value
                    for (key, value) in self._request_results.items()
                    if key not in self._pending_requests
                }
                result["deferred"] = (order, item, resolved, self._pending_requests)
            return result
        finally:
            self._executing_task = False
            self._request_results = {}
            self._pending_requests = {}

    def _limit_reason(self, start_time):
        if start_time is not None and time.time() - start_time >= self.max_hours * 3600:
            return "Time limit reached"
        if psutil.Process(os.getpid()).memory_info().rss / 1024**3 > self.max_mem:
            return "Memory limit reached"
        return None

    def verify_observation(self, item, start_time=None):
        if not self._executing_task:
            self._request_results = {}
            self._pending_requests = {}
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
        probes = self.P if self.HW else set(self.P)
        cache = tuple(sorted(map(str, probes)))
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
        if cache in completed:
            result = completed[cache]
        elif cache in self.observation_cache and cache in self.exact_zero_cache:
            result = {
                "mi": self.observation_cache[cache],
                "exact_zero": self.exact_zero_cache[cache],
                "mi_text": self.mi_text_cache.get(cache),
                "choice_rpe": self.choice_rpe_cache.get(cache, ()),
                "rpe_input_indices": self.rpe_witness_cache.get(cache, ()),
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
            elif self.tech == 0:
                safe = False
            else:
                componentwise_hw = "hw_vector" in self.gadget.checkOptions["robust"]
                safe = self.simplify(preserve_layout=self.HW, componentwise_hw=componentwise_hw)
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
                    self.rpe_input_indices = tuple(
                        (tuple(sorted(indices)) for indices in needed)
                    )
            if safe:
                mi, exact_zero = (0, True)
            elif self.tech == 1 or phase == "static":
                mi, exact_zero = (-1, None)
                if phase == "static":
                    self._pending_requests[cache] = (
                        tuple(self.P),
                        self.P_channel_count,
                        self.choice_rpe,
                        getattr(self, "rpe_input_indices", ()),
                    )
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
                self.mi_text_cache[cache] = mi_text
                self.choice_rpe_cache[cache] = self.choice_rpe
                self.rpe_witness_cache[cache] = result["rpe_input_indices"]
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
            cache = result["cache"]
            self.observation_cache[cache] = result["mi"]
            self.exact_zero_cache[cache] = result["exact_zero"]
            self.mi_text_cache[cache] = result.get("mi_text")
            self.choice_rpe_cache[cache] = result["choice_rpe"]
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
            if self.randomprobing:
                sampled = tuple(
                    self.gadget.random_wire_locations[index] for index in result["wire_indices"]
                )
                checks = enumerate(result["requests"], 1)
            else:
                sampled = tuple(locations[probe] for probe in result["row"])
                checks = ((None, result),)
            for request, check in checks:
                current = sampled
                if self.randomprobing:
                    outputs = (
                        self.rp_requests[request - 1]
                        if self.model_str == "rpc"
                        else check.get("output_choice", ())
                    )
                    current += tuple(locations[symbols(str(output))] for output in outputs)
                    status = (
                        "unknown"
                        if check["unknown"]
                        else "insecure" if check["failed"] else "safe"
                    )
                else:
                    status = check["status"]
                if (self.detail and status != "safe") or self._watch_locations.intersection(
                    current
                ):
                    self.event(
                        "detail",
                        {
                            "locations": current,
                            "status": status,
                            "mi": None if self.tech == 1 or check["mi"] < 0 else check["mi"],
                            "mi_text": check.get("mi_text"),
                            "quantity": "MI" if self.model_str in ("probing_secret", "rps_secret") else "CMI",
                            "request": request,
                            "wire_indices": result.get("wire_indices"),
                        },
                    )
        self.processed_count += 1

    def _test_security(self):
        model = self.model_str
        if model in ("probing_secret", "rps_secret"):
            return all((not value.free_symbols & self.shares_set for value in self.P))
        if model == "pini":
            needed = set()
            for value in self.P:
                needed.update(
                    (
                        self._share_locations[symbol][1]
                        for symbol in value.free_symbols & self.shares_set
                    )
                )
                if len(needed - self.O_outIndex) > self.t_in:
                    return False
            return True
        budget = (
            self.probe_count
            if model == "ni"
            else (
                self.t_in
                if model == "sni"
                else self.shareNum - 1 if model in ("probing_share", "rps_share") else self.t
            )
        )
        needed = [set() for _ in range(self.len_secrets)]
        for value in self.P:
            for symbol in value.free_symbols & self.shares_set:
                family, index = self._share_locations[symbol]
                needed[family].add(index)
                if model != "rpe" and len(needed[family]) > budget:
                    return False
        if model == "rpe":
            self.choice_rpe = tuple(
                (i for (i, indices) in enumerate(needed) if len(indices) > budget)
            )
            return not self.choice_rpe
        return True

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

        compact_tuple()
        if self.tech == 2:
            costs = {}
            source_costs = ({}, {})
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

        expression_text = {}

        def cached_text(expr):
            text = expression_text.get(expr)
            if text is None:
                text = str(expr)
                expression_text[expr] = text
            return text

        verify = self._static_boolean if self.logic else self._static_field
        safe = verify(preserve_layout, componentwise_hw, remember, cached_text)
        compact_tuple()
        if not safe:
            if remember is not None:
                remember()
                self.P = best_probes
            safe = self._test_security()
        return safe

    def _static_boolean(self, preserve_layout, componentwise_hw, remember, cached_text):
        slot_zero = sympify(False)
        normalized = {}
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
                    s = cached_text(expr)
                    row = {}
                    for r, scan in mask_scans:
                        count = len(scan(s))
                        if count:
                            row[r] = count
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
                    s = cached_text(new_expr)
                    new_row = {}
                    for rr, scan in mask_scans:
                        count = len(scan(s))
                        if count:
                            new_row[rr] = count
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
                    text = cached_text(new_expr)
                    new_row = {}
                    for r, scan in mask_scans:
                        count = len(scan(text))
                        if count:
                            new_row[r] = count
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
        self.P_raw = list(original_probes)
        self.choice_rpe = tuple()
        self.rpe_input_indices = tuple((() for _ in range(self.len_secrets)))
        channel_key = tuple(sorted(map(str, set(self.P))))
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
            "leakage": list(original_probes) if failed else [],
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

        def record(counts, lower, upper):
            counts["lower"][order] += int(lower)
            counts["upper"][order] += int(upper) - 1

        checks = result["requests"]
        stats["processed_by_order"][order] += 1
        record(
            stats,
            any((check["failed"] and (not check["unknown"]) for check in checks)),
            any((check["failed"] for check in checks)),
        )
        for index, check in enumerate(checks):
            self.observation_cache[check["cache"]] = check["mi"]
            self.exact_zero_cache[check["cache"]] = check["exact_zero"]
            self.mi_text_cache[check["cache"]] = check.get("mi_text")
            self.choice_rpe_cache[check["cache"]] = check["choice_rpe"]
            self.rpe_witness_cache[check["cache"]] = check["rpe_input_indices"]
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
                    counts[order] += int(occurs) - 1

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

        def summarize(counts, degree=1):
            bound = self.probability_bounds(counts["upper"], counts["lower"], k=degree)
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
