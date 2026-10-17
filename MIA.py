from collections import Counter
from decimal import Decimal, localcontext, MAX_EMAX, MIN_EMIN
from itertools import combinations, product
from math import log2, prod
import re

from galois import GF
import numpy as np
from sympy import Symbol, flatten
from sympy.logic.boolalg import Not, Xor

from auxiliary import EncodedXor


class MIA:

    def __init__(self, checker):
        self.gadget = checker.gadget
        self.Cgadget = checker
        self.MI_norm = 1
        self.model = None
        self.last_exact_zero = True
        self.last_mi_text = None
        self.probes = ()
        self.freeSymbolsInp = set()
        self.mayLeak = set()
        self.condition = set()
        self._rpe_affine_cache = {}

    def initialize(self):
        self.last_exact_zero = True
        self.last_mi_text = None
        self._rpe_affine_cache = {}
        self.Bits = self.gadget.bits
        self.Arithmetic = {
            "field": 2 if self.gadget.logic else self.gadget.field,
            "GF_field": None,
            "logic": self.gadget.logic,
        }

        self.Arithmetic["GF_field"] = GF(self.Arithmetic["field"])

        robust = self.gadget.checkOptions["robust"]
        self.HW = "hw_sumed" in robust or "hw_vector" in robust
        self.sharesNum = self.gadget.shareNum
        self.secrets = self.gadget.secrets
        self.len_secrets = len(self.secrets)
        self.randoms = self.gadget.randoms

        self.model_str = self.gadget.checkOptions["security"]
        if self.model_str not in ("probing_secret", "rps_secret") and not self.len_secrets:

            inputs = (
                self.gadget.secretsInputsBits if self.Bits > 1 else self.gadget.secretsInputs
            )
            width = self.Bits * self.sharesNum
            if not width or not inputs or len(inputs) % width:
                raise ValueError(
                    "Share simulation requires complete declared input-share families"
                )
            self.len_secrets = len(inputs) // width
        self.MI_norm = 1
        secret_entropy = log2(float(self.Arithmetic["field"])) * self.len_secrets * self.Bits
        if self.model_str == "probing_secret":
            self.MI_norm = secret_entropy
        elif self.model_str in ["pini", "sni", "ni", "probing_share"]:
            self.MI_norm = secret_entropy * self.sharesNum

        self.shares = (
            self.gadget.secretsInputsBits if self.Bits > 1 else self.gadget.secretsInputs
        )
        self.shares_set = set(self.shares)
        self.funcMapping = {
            id: id // (self.Bits * self.sharesNum) for id in range(len(self.shares))
        }
        firstIndex = min(self.gadget.shareIndex)
        self.funcMapping_index = {
            id: ((id // self.Bits) % self.sharesNum) + firstIndex
            for id in range(len(self.shares))
        }
        if self.model_str in ("probing_secret", "rps_secret"):
            self.shares = self.gadget.secretsBits if self.Bits > 1 else self.gadget.secrets
            self.shares_set = set(self.shares)

        self.model = {
            "probing_secret": self.probing,
            "rps_secret": self.probing,
            "pini": self.pini,
            "ni": self.share_simulation,
            "sni": self.share_simulation,
            "rpc": self.share_simulation,
            "probing_share": self.share_simulation,
            "rps_share": self.share_simulation,
            "rpe": self.rpe,
        }[self.model_str]

    def compute(self):
        self.last_exact_zero = True
        self.last_mi_text = None
        value = self.model()
        if isinstance(value, Decimal):
            self.last_mi_text = str(value)
        return float(value)

    def prepare_observation(self):
        self.last_exact_zero = True
        self.probes = list(self.Cgadget.P) if self.HW else set(self.Cgadget.P)
        self.freeSymbolsInp = set().union(*(probe.free_symbols for probe in self.probes))
        self.mayLeak = set()
        self.condition = set()
        return self.freeSymbolsInp & self.shares_set

    def probing(self):
        sharesInp = self.prepare_observation()
        if not sharesInp:
            return 0
        self.mayLeak = sharesInp
        return self.conditional_mi()

    def share_simulation(self, share_budget=None):
        sharesInp = self.prepare_observation()
        if not sharesInp:
            return 0

        if share_budget is not None:
            t = share_budget
        elif self.model_str in ("probing_share", "rps_share"):
            t = self.sharesNum - 1
        elif self.model_str == "sni":
            t = self.Cgadget.t_in
        elif self.model_str == "ni":
            t = getattr(self.Cgadget, "probe_count", None)
            if t is None:
                if hasattr(self.Cgadget, "t_in") and hasattr(self.Cgadget, "t_out"):
                    t = self.Cgadget.t_in + self.Cgadget.t_out
                else:
                    t = self.Cgadget.t
        else:
            t = self.Cgadget.t

        families = [set() for _ in range(self.len_secrets)]
        family_indices = [set() for _ in range(self.len_secrets)]
        for share in sharesInp:
            family = self.funcMapping[self.shares[share]]
            families[family].add(share)
            family_indices[family].add(self.funcMapping_index[self.shares[share]])
        if all(len(indices) <= t for indices in family_indices):
            return 0

        choices = []
        for family, shares in enumerate(families):
            shares_index_map = {
                share: self.funcMapping_index[self.shares[share]] for share in shares
            }
            indices = family_indices[family]
            if not indices:
                continue
            if len(indices) <= t:
                choices.append([list(shares)])
                continue
            selections = []
            for selected in combinations(indices, min(len(indices), t)):
                valid_indices = set(selected)
                selections.append(
                    [
                        share
                        for share, index in shares_index_map.items()
                        if index in valid_indices
                    ]
                )
            choices.append(selections)

        best_mi = None
        for selected in product(*choices):
            self.condition = set(flatten(selected))
            self.mayLeak = sharesInp - self.condition
            if not self.mayLeak:
                return 0
            mi = self.conditional_mi()
            if self.last_exact_zero:
                return 0
            if best_mi is None or mi < best_mi:
                best_mi = mi

        if best_mi is None:
            self.mayLeak = sharesInp
            self.condition = []
            return self.conditional_mi()
        return best_mi

    def pini(self):

        sharesInp = self.prepare_observation()
        safeIndex = set(self.Cgadget.O_outIndex)
        t = self.Cgadget.t_in
        if not sharesInp:
            return 0
        shares_index_map = {s: self.funcMapping_index[self.shares[s]] for s in sharesInp}
        PINI_Index = set(shares_index_map.values())

        if PINI_Index <= safeIndex:
            return 0

        if len(PINI_Index - safeIndex) <= t:
            return 0
        conditions = []
        index_IcutO = list(PINI_Index - safeIndex)

        for index in combinations(index_IcutO, min(len(index_IcutO), t)):
            IplusO = set(index) | safeIndex
            noLeak = [s for s, idx in shares_index_map.items() if idx in IplusO]
            if noLeak:
                conditions.append(set(noLeak))

        if not conditions:

            self.mayLeak = sharesInp
            self.condition = []
            return self.conditional_mi()

        best_mi = None
        for nL in conditions:

            self.mayLeak = sharesInp - nL
            self.condition = nL

            if not self.mayLeak:
                return 0

            mi = self.conditional_mi()

            if self.last_exact_zero:
                return 0

            if best_mi is None or mi < best_mi:
                best_mi = mi

        return 0 if best_mi is None else best_mi

    def rpe(self):

        sharesInp = self.prepare_observation()
        self.Cgadget.choice_rpe = tuple()
        self.Cgadget.rpe_input_indices = tuple(() for _ in range(self.len_secrets))
        t = self.Cgadget.t
        if not sharesInp:
            return 0

        families = [{} for _ in range(self.len_secrets)]
        for share in sharesInp:
            family = self.funcMapping[self.shares[share]]
            index = self.funcMapping_index[self.shares[share]]
            families[family].setdefault(index, set()).add(share)

        affine = self._rpe_affine_space()
        conditional_mi = (
            self.conditional_mi if affine is None else lambda: self._affine_rpe_cmi(affine)
        )
        if affine is not None:
            _, bits, needed = affine
            required = [set() for _ in range(self.len_secrets)]
            for share in sharesInp:
                if bits[share] & needed:
                    position = self.shares[share]
                    required[self.funcMapping[position]].add(self.funcMapping_index[position])
            if all(len(indices) <= t for indices in required):
                self.Cgadget.rpe_input_indices = tuple(
                    tuple(sorted(indices)) for indices in required
                )
                self.last_exact_zero = True
                return 0.0

        failures = []
        witnesses = []
        best_allowed = set()
        for family, groups in enumerate(families):
            indices = tuple(sorted(groups))
            family_shares = set().union(*groups.values()) if groups else set()
            if len(indices) <= t:
                best_allowed.update(family_shares)
                witnesses.append(indices)
                continue
            others = sharesInp - family_shares
            best_mi = float("inf")
            found_exact = False
            best_indices = tuple()
            best_shares = set()
            for selected in combinations(indices, t):
                selected_shares = set().union(*(groups[index] for index in selected))
                self.condition = others | selected_shares
                self.mayLeak = family_shares - selected_shares
                mi = conditional_mi()
                if mi < best_mi:
                    best_mi, best_indices, best_shares = mi, selected, selected_shares
                if self.last_exact_zero:
                    found_exact = True
                    best_mi, best_indices, best_shares = 0.0, selected, selected_shares
                    break
            best_allowed.update(best_shares)
            if not found_exact:
                failures.append(family)

                witnesses.append(indices)
            else:
                witnesses.append(best_indices)

        self.Cgadget.choice_rpe = tuple(failures)
        self.Cgadget.rpe_input_indices = tuple(witnesses)
        if not failures:
            self.last_exact_zero = True
            return 0

        self.condition = best_allowed
        self.mayLeak = sharesInp - best_allowed
        return conditional_mi()

    @staticmethod
    def _gf2_rank(rows):
        basis = {}
        for row in rows:
            while row:
                pivot = row.bit_length() - 1
                if pivot not in basis:
                    basis[pivot] = row
                    break
                row ^= basis[pivot]
        return len(basis)

    def _rpe_affine_space(self):

        if not self.Arithmetic["logic"] or (
            self.HW and "hw_vector" not in self.gadget.checkOptions["robust"]
        ):
            return None
        randoms = set(self.randoms)
        if randoms & self.shares_set or self.freeSymbolsInp - self.shares_set - randoms:
            return None
        inputs = tuple(self.shares)
        sources = inputs + tuple(sorted(randoms, key=str))
        signature = sources
        cache = getattr(self, "_rpe_affine_cache", {})
        if cache.get("sources") != signature:
            cache = {
                "sources": signature,
                "bits": {symbol: 1 << i for i, symbol in enumerate(sources)},
                "rows": {},
            }
            self._rpe_affine_cache = cache
        bits, rows_cache = cache["bits"], cache["rows"]

        def parse(expr):
            if expr in rows_cache:
                return rows_cache[expr]
            if isinstance(expr, Symbol):
                value = bits.get(expr)
            elif expr in (False, True, 0, 1):
                value = 0
            elif expr.func is Not:
                value = parse(expr.args[0])
            elif expr.func is Xor:
                value = 0
                for argument in expr.args:
                    part = parse(argument)
                    if part is None:
                        value = None
                        break
                    value ^= part
            else:
                value = None
            rows_cache[expr] = value
            return value

        rows = tuple(parse(probe) for probe in self.probes)
        if any(row is None for row in rows):
            return None

        basis, needed = {}, 0
        for row in rows:
            while row >> len(inputs):
                pivot = row.bit_length() - 1
                if pivot not in basis:
                    basis[pivot] = row
                    break
                row ^= basis[pivot]
            else:
                needed |= row
        return rows, bits, needed

    def _affine_rpe_cmi(self, space):
        rows, bits, _ = space
        conditioned = 0
        for symbol in self.condition:
            conditioned |= bits[symbol]
        remaining = conditioned
        for symbol in self.mayLeak:
            remaining |= bits[symbol]

        value = self._gf2_rank(row & ~conditioned for row in rows) - self._gf2_rank(
            row & ~remaining for row in rows
        )
        self.last_exact_zero = value == 0
        return value / self.MI_norm

    def reduce_observations(self, x, y, z):

        xz_vars = set(x + z)
        vars_list = [expr.free_symbols for expr in y]

        var_index = {}
        for i, vs in enumerate(vars_list):
            for v in vs:
                var_index.setdefault(v, set()).add(i)

        related = set()
        stack = []

        freeSymbolsInp = set()
        y_filtered = []

        for i, vs in enumerate(vars_list):
            if vs & xz_vars:
                related.add(i)
                stack.append(i)

        expanded_variables = set()
        while stack:
            i = stack.pop()
            expr = y[i]
            y_filtered.append(expr)
            freeSymbolsInp.update(vars_list[i])

            for var in vars_list[i]:
                if var in expanded_variables:
                    continue
                expanded_variables.add(var)
                for j in var_index[var]:
                    if j not in related:
                        related.add(j)
                        stack.append(j)

        self.freeSymbolsInp = freeSymbolsInp
        return y_filtered

    def _channel_probe_count(self):

        count = getattr(self.Cgadget, "P_channel_count", None)
        if count is None:
            return len(self.probes)
        if not isinstance(count, int) or not 0 <= count <= len(self.probes):
            raise ValueError("Invalid leakage-channel observation count")
        return count

    def conditional_mi(self, batch_bits=None):
        self.last_exact_zero = True
        if self.Arithmetic["logic"]:
            return self._boolean_cmi(batch_bits=batch_bits)
        return self._field_cmi(batch_bits=batch_bits)

    def _boolean_cmi(self, batch_bits=None, hw=None):
        hw = self.HW if hw is None else hw
        summed_hw = hw and "hw_vector" not in self.gadget.checkOptions["robust"]
        if not self.probes:
            self.last_exact_zero = True
            return 0.0

        y, x, z = list(self.probes), list(self.mayLeak), list(self.condition)
        if not summed_hw:
            y = self.reduce_observations(x, y, z)
        if not y:
            self.last_exact_zero = True
            return 0.0
        lenx, lenz = len(x), len(z)
        xyz = x + y + z
        entropy_xz = len(set(x) | set(z))

        sources = tuple(set(self.freeSymbolsInp) | set(x) | set(z))
        source_count = len(sources)
        if source_count > 36:
            raise ValueError(
                f"Too many source variables for exact Boolean enumeration: {source_count}"
            )
        if batch_bits is None:
            batch_bits = 20 if source_count <= 28 else (24 if source_count <= 32 else 26)
        if not isinstance(batch_bits, int) or batch_bits < 0:
            raise ValueError("batch_bits must be a nonnegative integer")

        symbol_positions = {symbol: index for index, symbol in enumerate(sources)}
        public = set(sources) - self.shares_set - set(self.randoms)
        radices = [1 if symbol in public else 2 for symbol in sources]
        offsets = [int(symbol in public) for symbol in sources]
        total_states = self._state_count(radices)

        compiled = []
        for expression in xyz:
            replacements = {
                str(symbol): f"v[:,{symbol_positions[symbol]}]"
                for symbol in expression.free_symbols
                if symbol in symbol_positions
            }
            code = str(expression)
            if replacements:
                pattern = r"\b(?:" + "|".join(map(re.escape, replacements)) + r")\b"
                code = re.sub(pattern, lambda match: replacements[match.group()], code)
            compiled.append(
                eval(
                    "lambda v: np.broadcast_to("
                    f"np.asarray(({code}), dtype=np.uint8) & 1, (v.shape[0],))"
                )
            )

        channel_count = self._channel_probe_count() if summed_hw else 0
        hw_bits = max(1, channel_count.bit_length()) if summed_hw else 0
        packed_width = len(xyz) - channel_count + hw_bits if summed_hw else len(xyz)
        multiple_chunks = packed_width > 64
        weights = []
        bit_shifts = np.arange(hw_bits, dtype=np.uint64)
        for target_count in (lenx, 0):
            width = packed_width - lenx + target_count
            if multiple_chunks:
                weights.append(
                    tuple(
                        np.uint64(1) << np.arange(min(64, width - start), dtype=np.uint64)
                        for start in range(0, width, 64)
                    )
                )
            else:
                column_count = width - hw_bits + 1 if summed_hw else width
                shifts = np.arange(column_count, dtype=np.uint64)
                if summed_hw:
                    shifts[target_count + 1 :] += hw_bits - 1
                weights.append((np.uint64(1) << shifts,))

        def pack(values, powers, hw_column):
            values = values.astype(np.uint64, copy=False)
            if not multiple_chunks:
                return values.dot(powers[0]).tolist()
            if summed_hw:
                bits = (values[:, hw_column, None] >> bit_shifts) & 1
                values = np.concatenate(
                    [values[:, :hw_column], bits, values[:, hw_column + 1 :]], axis=1
                )
            packed = np.empty((len(values), len(powers)), dtype=np.uint64)
            for chunk, (start, power) in enumerate(zip(range(0, values.shape[1], 64), powers)):
                packed[:, chunk] = values[:, start : start + len(power)].dot(power)
            return [tuple(row) for row in packed]

        counts_xyz, counts_yz = Counter(), Counter()
        batch_size = 1 << batch_bits
        for start in range(0, total_states, batch_size):
            end = min(start + batch_size, total_states)
            indices = np.arange(start, end, dtype=np.uint64)
            values = np.empty((end - start, source_count), dtype=np.uint8)
            for column, (radix, offset) in enumerate(zip(radices, offsets)):
                values[:, column] = indices % radix + offset
                indices //= radix
            observations = np.column_stack([function(values) for function in compiled])
            if summed_hw:
                observations = np.concatenate(
                    [
                        observations[:, :lenx],
                        observations[:, lenx : lenx + channel_count].sum(
                            axis=1, dtype=np.uint64, keepdims=True
                        ),
                        observations[:, lenx + channel_count :],
                    ],
                    axis=1,
                )
            counts_xyz.update(pack(observations, weights[0], lenx))
            counts_yz.update(pack(observations[:, lenx:], weights[1], 0))
            del indices, values, observations

        p_xyz = np.array(list(counts_xyz.values()), dtype=float) / total_states
        p_yz = np.array(list(counts_yz.values()), dtype=float) / total_states
        entropy_xyz = -np.sum(p_xyz * np.log2(p_xyz))
        entropy_yz = -np.sum(p_yz * np.log2(p_yz))
        mi = entropy_xz + entropy_yz - entropy_xyz - lenz
        return self._finish_cmi(counts_xyz, counts_yz, x, z, mi, 2, packed=True)

    def _field_cmi(self, batch_bits=None, hw=None):
        hw = self.HW if hw is None else hw
        if self.Arithmetic["logic"]:
            return self._boolean_cmi(batch_bits=batch_bits, hw=hw)
        if not self.probes:
            self.last_exact_zero = True
            return 0.0

        field = self.Arithmetic["field"]
        field_type = self.Arithmetic["GF_field"]
        y, x, z = list(self.probes), list(self.mayLeak), list(self.condition)
        if not hw:
            y = self.reduce_observations(x, y, z)
        if not y:
            self.last_exact_zero = True
            return 0.0
        lenx, lenz = len(x), len(z)
        xyz = x + y + z
        entropy_xz = len(set(x) | set(z)) * log2(field)
        entropy_z = lenz * log2(field)

        sources = tuple(set(self.freeSymbolsInp) | set(x) | set(z))
        source_count = len(sources)
        max_sources = int(64 / np.log2(field))
        if source_count > max_sources:
            raise ValueError(
                f"Too many source variables for exact finite-field enumeration: {source_count}"
            )
        if batch_bits is None:
            if source_count <= max_sources - 8 and max_sources > 8:
                batch_bits = 20
            elif source_count <= max_sources - 4 and max_sources > 4:
                batch_bits = 24
            else:
                batch_bits = 26
        if not isinstance(batch_bits, int) or batch_bits < 0:
            raise ValueError("batch_bits must be a nonnegative integer")

        public = set(sources) - self.shares_set - set(self.randoms)
        offsets = [int(symbol in public) for symbol in sources]
        radices = [field - offset for offset in offsets]
        total_states = self._state_count(radices)
        compiled = self._compile_field_expressions(xyz, sources, field_type)
        if hw:
            channel_count = self._channel_probe_count()
            vector_hw = "hw_vector" in self.gadget.checkOptions["robust"]
            byte_hw = np.array([value.bit_count() for value in range(256)], dtype=np.uint8)

        counts_xyz, counts_yz = Counter(), Counter()
        batch_size = 1 << batch_bits
        for start in range(0, total_states, batch_size):
            end = min(start + batch_size, total_states)
            indices = np.arange(start, end, dtype=np.uint64)
            values = np.empty((end - start, source_count), dtype=int)
            for column, (radix, offset) in enumerate(zip(radices, offsets)):
                values[:, column] = indices % radix + offset
                indices //= radix
            values = field_type(values)
            observations = np.column_stack(
                [np.asarray(function(values), dtype=np.int64) for function in compiled]
            )
            if hw:
                encoded = np.ascontiguousarray(
                    observations[:, lenx : lenx + channel_count], dtype=np.uint64
                )
                bytes_view = encoded.view(np.uint8).reshape(len(encoded), channel_count, 8)
                channel_hw = byte_hw[bytes_view].sum(axis=2, dtype=np.int64)
                if not vector_hw:
                    channel_hw = channel_hw.sum(axis=1, dtype=np.int64, keepdims=True)
                observations = np.concatenate(
                    [
                        observations[:, :lenx],
                        channel_hw,
                        observations[:, lenx + channel_count :],
                    ],
                    axis=1,
                )
                del encoded, bytes_view, channel_hw
            counts_xyz.update([tuple(int(value) for value in row) for row in observations])
            counts_yz.update(
                [tuple(int(value) for value in row) for row in observations[:, lenx:]]
            )
            del indices, values, observations

        total = sum(counts_xyz.values())
        p_xyz = np.array(list(counts_xyz.values()), dtype=float) / total
        p_yz = np.array(list(counts_yz.values()), dtype=float) / total
        entropy_xyz = -np.sum(p_xyz * np.log2(p_xyz))
        entropy_yz = -np.sum(p_yz * np.log2(p_yz))
        mi = entropy_xz + entropy_yz - entropy_xyz - entropy_z
        return self._finish_cmi(counts_xyz, counts_yz, x, z, mi, field)

    @staticmethod
    def _compile_field_expressions(exprs, vars_list, GF_field):

        symbol_to_idx = {s: i for i, s in enumerate(vars_list)}
        is_binary_ext = GF_field.characteristic == 2 and GF_field.degree > 1

        def evaluate_expr_gfp(vals, expr):
            if expr.is_Rational:
                p_val, q_val = expr.as_numer_denom()
                scalar = GF_field(int(p_val) % GF_field.order) / GF_field(
                    int(q_val) % GF_field.order
                )
                return GF_field(np.full(vals.shape[0], int(scalar)))

            elif expr.is_Number:
                raise TypeError("Finite-field constants must be integers or rationals")

            elif expr.is_Symbol:
                return vals[:, symbol_to_idx[expr]]

            elif expr.is_Add:
                args = [evaluate_expr_gfp(vals, arg) for arg in expr.args]
                result = args[0]
                for r in args[1:]:
                    result = result + r
                return result

            elif expr.is_Mul:
                args = [evaluate_expr_gfp(vals, arg) for arg in expr.args]
                result = args[0]
                for r in args[1:]:
                    result = result * r
                return result

            elif expr.is_Pow:
                base, exp = expr.args
                base_res = evaluate_expr_gfp(vals, base)
                if not exp.is_Integer:
                    raise TypeError("Noninteger exponents are not supported")
                exp_int = int(exp)
                if exp_int < 0:
                    if (base_res == 0).any():
                        raise ZeroDivisionError(
                            "Cannot raise zero field elements to a negative power"
                        )
                    exp_int %= GF_field.order - 1
                elif exp_int:
                    exp_int = 1 + (exp_int - 1) % (GF_field.order - 1)
                return base_res**exp_int

            else:
                raise TypeError(f"Unsupported sympy expression type: {type(expr)} - {expr}")

        def evaluate_expr_gf2n(vals, expr):
            if expr.is_Rational:
                p, q = expr.as_numer_denom()
                p_val, q_val = abs(int(p)), int(q)

                scalar_result = GF_field(p_val) * (GF_field(q_val) ** (-1))
                return GF_field(np.full(vals.shape[0], int(scalar_result)))

            elif expr.is_Number:

                raise TypeError("Finite-field constants must be integers or rationals")

            elif expr.is_Symbol:
                return vals[:, symbol_to_idx[expr]]

            elif expr.is_Add:
                args_results = [evaluate_expr_gf2n(vals, arg) for arg in expr.args]

                result = args_results[0]
                for i in range(1, len(args_results)):
                    result = result + args_results[i]
                return result

            elif expr.is_Mul:
                args_results = [evaluate_expr_gf2n(vals, arg) for arg in expr.args]

                result = args_results[0]
                for i in range(1, len(args_results)):
                    result = result * args_results[i]
                return result

            elif expr.is_Pow:
                base, exp = expr.args
                base_result = evaluate_expr_gf2n(vals, base)
                if not exp.is_Integer:
                    raise TypeError("Noninteger exponents are not supported")
                exp_int = int(exp)
                if exp_int < 0:
                    if (base_result == 0).any():
                        raise ZeroDivisionError(
                            "Cannot raise zero field elements to a negative power"
                        )
                    exp_int %= GF_field.order - 1
                elif exp_int:
                    exp_int = 1 + (exp_int - 1) % (GF_field.order - 1)
                return base_result**exp_int

            else:
                raise TypeError(f"Unsupported sympy expression type: {type(expr)} - {expr}")

        field_evaluator = evaluate_expr_gf2n if is_binary_ext else evaluate_expr_gfp

        def evaluate_leakage(vals, expr):
            if isinstance(expr, EncodedXor):
                result = np.zeros(vals.shape[0], dtype=np.int64)
                for operand in expr.args:
                    result ^= np.asarray(evaluate_leakage(vals, operand), dtype=np.int64)
                return result
            return field_evaluator(vals, expr)

        return [lambda vals, e=expr: evaluate_leakage(vals, e) for expr in exprs]

    @staticmethod
    def _state_count(lengths):

        count = prod(lengths)
        if count > np.iinfo(np.int64).max:
            raise ValueError(f"Too many states for exact MI enumeration: {count}")
        return count

    def _finish_cmi(self, counts_xyz, counts_yz, x, z, numerical_mi, field, packed=False):

        multiplicity = int(field) ** len(set(x) - set(z))
        if not packed:
            project = lambda key: key[len(x) :]
        elif isinstance(next(iter(counts_yz), 0), tuple):
            chunks = len(next(iter(counts_yz)))
            mask = (1 << 64) - 1

            def project(key):
                value = sum(int(chunk) << (64 * i) for i, chunk in enumerate(key)) >> len(x)
                return tuple((value >> (64 * i)) & mask for i in range(chunks))

        else:
            project = lambda key: int(key) >> len(x)
        self.last_exact_zero = all(
            int(count) * multiplicity == int(counts_yz[project(key)])
            for key, count in counts_xyz.items()
        )
        if self.last_exact_zero:
            return 0.0
        value = max(0.0, float(numerical_mi / self.MI_norm))
        if value > 1e-9:
            return value

        with localcontext() as context:
            context.prec = 80
            context.Emax, context.Emin = MAX_EMAX, MIN_EMIN
            total = Decimal(sum(map(int, counts_xyz.values())))
            log_two = Decimal(2).ln()
            norm = Decimal(str(self.MI_norm))
            if self.model_str in ("probing_secret", "ni", "sni", "pini", "probing_share"):
                factor = self.len_secrets * self.Bits
                if self.model_str != "probing_secret":
                    factor *= self.sharesNum
                norm = Decimal(int(field)).ln() / log_two * factor
            value = (
                sum(
                    (
                        Decimal(int(count))
                        / total
                        * (
                            Decimal(int(count) * multiplicity)
                            / Decimal(int(counts_yz[project(key)]))
                        ).ln()
                        for key, count in counts_xyz.items()
                    ),
                    Decimal(0),
                )
                / log_two
                / norm
            )
            return max(Decimal(0), +value)
