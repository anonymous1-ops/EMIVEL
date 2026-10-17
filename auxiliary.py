from copyreg import pickle as register_pickle
from functools import cmp_to_key, partial
from numbers import Integral
from sympy import Basic, Function, Integer, Rational, S
from sympy import Add as SympyAdd, Mul as SympyMul, Pow as SympyPow
from galois import GF, FieldArray


for _operation in (SympyAdd, SympyMul, SympyPow):
    register_pickle(
        _operation,
        lambda expression: (partial(type(expression), evaluate=False), expression.args),
    )


class EncodedXor(Function):

    @classmethod
    def eval(cls, *args):
        pending = list(args)
        odd_operands = set()
        while pending:
            operand = pending.pop()
            if isinstance(operand, cls):
                pending.extend(operand.args)
            elif operand == S.Zero:
                continue
            elif operand in odd_operands:
                odd_operands.remove(operand)
            else:
                odd_operands.add(operand)

        if not odd_operands:
            return S.Zero
        if len(odd_operands) == 1:
            return next(iter(odd_operands))

        canonical = tuple(sorted(odd_operands, key=cmp_to_key(Basic.compare)))
        if canonical != args:
            return cls(*canonical, evaluate=False)


class _FiniteField:
    field = None
    binary = False

    def set_field(self, field=None):
        field = GF(8 if self.binary else 7) if field is None else field
        if not isinstance(field, type) or not issubclass(field, FieldArray):
            raise TypeError("Expected a galois finite-field class")
        if (self.binary and field.characteristic != 2) or (
            not self.binary and field.degree != 1
        ):
            raise ValueError("The finite field does not match this evaluator")
        self.field = field
        self.order = int(field.order)

    def __getstate__(self):
        field = self.field
        state = self.__dict__.copy()
        state.pop("field", None)
        state["_field_definition"] = None if field is None else (
            int(field.order), int(field.irreducible_poly) if field.degree > 1 else None,
            int(field.primitive_element)
        )
        return state

    def __setstate__(self, state):
        definition = state.pop("_field_definition")
        self.__dict__.update(state)
        if definition is not None:
            order, polynomial, primitive = definition
            self.set_field(GF(
                order, irreducible_poly=polynomial, primitive_element=primitive
            ))

    def _constant(self, value):
        value = int(value)
        if not self.binary:
            return value % self.order
        value = abs(value)
        if value >= self.order:
            raise ValueError("Encoded field element is outside the field")
        return value

    def _multiply(self, left, right):
        if not self.binary:
            return left * right % self.order
        if not left or not right:
            return 0
        if left == 1:
            return right
        if right == 1:
            return left
        return int(self.field(left) * self.field(right))

    def _power(self, base, exponent):
        if exponent < 0 and not base:
            raise ValueError("Zero has no multiplicative inverse")
        if exponent == 0:
            return 1
        if exponent == 1 or base in (0, 1):
            return base
        if self.binary:
            return int(self.field(base) ** (exponent % (self.order - 1)))
        return pow(base, exponent, self.order)

    @staticmethod
    def _compare(left, right):
        pending = [(left, right)]
        while pending:
            left, right = pending.pop()
            if left is right:
                continue
            if isinstance(left, Basic) and isinstance(right, Basic):
                left_type, right_type = type(left), type(right)
                difference = (left_type > right_type) - (left_type < right_type)
                if difference:
                    return difference
                left_items = left._hashable_content()
                right_items = right._hashable_content()
                difference = (
                    (len(left_items) > len(right_items))
                    - (len(left_items) < len(right_items))
                )
                if difference:
                    return difference
                pending.extend(reversed(tuple(zip(left_items, right_items))))
            else:
                difference = (left > right) - (left < right)
                if difference:
                    return difference
        return 0

    @staticmethod
    def _operands(expression):
        operation = type(expression)
        pending = [(expression, False)]
        seen = set()
        order = []
        while pending:
            current, ready = pending.pop()
            key = id(current)
            if ready:
                order.append(current)
            elif key not in seen:
                seen.add(key)
                pending.append((current, True))
                pending.extend(
                    (arg, False) for arg in reversed(current.args)
                    if type(arg) is operation
                )
        weights = {id(expression): 1}
        operands = {}
        for current in reversed(order):
            count = weights[id(current)]
            for arg in current.args:
                key = id(arg)
                if type(arg) is operation:
                    weights[key] = weights.get(key, 0) + count
                elif key in operands:
                    operands[key][1] += count
                else:
                    operands[key] = [arg, count]
        return tuple(operands.values())

    def evaluate(self, *expressions):
        if self.field is None:
            raise ValueError("Set the finite field before evaluation")
        if len(expressions) == 1 and isinstance(expressions[0], (list, tuple)):
            expressions = expressions[0]
        expressions = [
            Integer(expr) if isinstance(expr, Integral) else expr
            for expr in expressions
        ]
        memo = {}
        products = {}
        powers = {}
        results = []
        compare = cmp_to_key(self._compare)
        for expression in expressions:
            pending = [(expression, None)]
            while pending:
                current, operands = pending.pop()
                key = id(current)
                if key in memo:
                    continue
                if not isinstance(current, Basic):
                    raise TypeError("Expected an integer or SymPy expression")
                if operands is None:
                    if current.is_Integer:
                        memo[key] = Integer(self._constant(current))
                        continue
                    if isinstance(current, Rational):
                        numerator = self._constant(current.p)
                        denominator = self._constant(current.q)
                        memo[key] = Integer(self._multiply(
                            numerator, self._power(denominator, -1)
                        ))
                        continue
                    if current.is_Symbol:
                        memo[key] = current
                        continue
                    if isinstance(current, EncodedXor):
                        memo[key] = current
                        continue
                    if isinstance(current, (SympyAdd, SympyMul)):
                        operands = self._operands(current)
                    elif isinstance(current, SympyPow):
                        if not current.exp.is_Integer:
                            raise TypeError("Finite-field powers require integer exponents")
                        operands = ((current.base, 1),)
                    else:
                        raise TypeError("Unsupported finite-field expression operation")
                    pending.append((current, operands))
                    pending.extend(
                        (arg, None) for arg, _ in reversed(operands)
                        if id(arg) not in memo
                    )
                    continue
                if isinstance(current, SympyPow):
                    base = memo[id(current.base)]
                    exponent = int(current.exp)
                    if base.is_Integer:
                        power_key = (int(base), exponent)
                        if power_key not in powers:
                            powers[power_key] = Integer(self._power(*power_key))
                        result = powers[power_key]
                    elif exponent == 0:
                        result = S.One
                    elif exponent == 1:
                        result = base
                    else:
                        result = SympyPow(base, current.exp, evaluate=False)
                else:
                    additive = isinstance(current, SympyAdd)
                    terms = {}
                    coefficient = 1
                    work = [
                        (memo[id(arg)], count) for arg, count in reversed(operands)
                    ]
                    while work:
                        value, count = work.pop()
                        if type(value) is type(current):
                            work.extend(
                                (arg, count * multiplicity)
                                for arg, multiplicity in reversed(self._operands(value))
                            )
                            continue
                        if additive:
                            factor = 1
                            factors = ()
                            if value.is_Integer:
                                factor = int(value)
                            elif isinstance(value, SympyMul):
                                if value.args[0].is_Integer:
                                    factor = int(value.args[0])
                                    factors = value.args[1:]
                                else:
                                    factors = value.args
                            else:
                                factors = (value,)
                            previous = terms.get(factors, 0)
                            terms[factors] = (
                                previous ^ (factor if count & 1 else 0)
                                if self.binary else
                                (previous + factor * count) % self.order
                            )
                        elif value.is_Integer:
                            factor = int(value)
                            if count != 1:
                                power_key = (factor, count)
                                if power_key not in powers:
                                    powers[power_key] = Integer(self._power(*power_key))
                                factor = int(powers[power_key])
                            product_key = (
                                min(coefficient, factor), max(coefficient, factor)
                            )
                            if product_key not in products:
                                products[product_key] = self._multiply(*product_key)
                            coefficient = products[product_key]
                        else:
                            terms[value] = terms.get(value, 0) + count
                    if additive:
                        arguments = []
                        for factors, factor in terms.items():
                            if not factor:
                                continue
                            if not factors:
                                term = Integer(factor)
                            elif factor == 1:
                                term = (
                                    factors[0] if len(factors) == 1 else
                                    SympyMul(*factors, evaluate=False)
                                )
                            else:
                                term = SympyMul(Integer(factor), *factors, evaluate=False)
                            arguments.append(term)
                        result = (
                            SympyAdd(*arguments, evaluate=False) if len(arguments) > 1
                            else arguments[0] if arguments else S.Zero
                        )
                    elif not coefficient:
                        result = S.Zero
                    else:
                        arguments = [
                            value if count == 1 else
                            SympyPow(value, Integer(count), evaluate=False)
                            for value, count in terms.items()
                        ]
                        arguments.sort(key=compare)
                        if coefficient != 1:
                            arguments.insert(0, Integer(coefficient))
                        result = (
                            SympyMul(*arguments, evaluate=False) if len(arguments) > 1
                            else arguments[0] if arguments else S.One
                        )
                memo[key] = result
            results.append(memo[id(expression)])
        return results[0] if len(results) == 1 else results


class sympyGF2N(_FiniteField):
    binary = True


class sympyGFp(_FiniteField):
    pass
