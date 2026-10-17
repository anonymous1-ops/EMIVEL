from collections.abc import Sequence
from dataclasses import dataclass, field
from itertools import chain, combinations
from math import comb, isqrt, prod
from operator import index


@dataclass(frozen=True, slots=True)
class Instruction:
    index: int
    lhs: str
    rhs: str
    expression: str
    stage: str
    source_line: object
    tree: object = field(repr=False, compare=False)
    dependencies: frozenset
    operand_names: tuple
    previous_write: object
    barrier: bool = False
    extensions: tuple = ()
    syntax: tuple = field(default=(), repr=False, compare=False)
    nodes: tuple = field(default=(), repr=False, compare=False)
    operand_versions: tuple = ()


@dataclass(frozen=True, slots=True)
class TransitionPositions(Sequence):
    body: tuple
    stable: tuple = ()
    include_singletons: bool = False

    def __post_init__(self):
        object.__setattr__(self, "body", tuple(self.body))
        object.__setattr__(self, "stable", tuple(self.stable))

    def __len__(self):
        n = len(self.body)
        return comb(n, 2) + len(self.stable) + (n if self.include_singletons or n < 2 else 0)

    def __iter__(self):
        yield from combinations(self.body, 2)
        yield from self.stable
        if self.include_singletons or len(self.body) < 2:
            yield from ((probe,) if isinstance(probe, tuple) else probe for probe in self.body)

    def __getitem__(self, position):
        if isinstance(position, slice):
            return tuple(self[i] for i in range(*position.indices(len(self))))
        position = index(position)
        if position < 0:
            position += len(self)
        if position < 0 or position >= len(self):
            raise IndexError("transition position out of range")
        n = len(self.body)
        pairs = comb(n, 2)
        if position < pairs:
            low = (2 * n - 1 - isqrt((2 * n - 1) ** 2 - 8 * position)) // 2
            if low * (2 * n - low - 1) // 2 > position:
                low -= 1
            offset = low * (2 * n - low - 1) // 2
            return self.body[low], self.body[low + 1 + position - offset]
        position -= pairs
        if position < len(self.stable):
            return self.stable[position]
        probe = self.body[position - len(self.stable)]
        return (probe,) if isinstance(probe, tuple) else probe


@dataclass(frozen=True, slots=True)
class ObservationPlan(Sequence):
    population: object
    orders: tuple
    flatten: bool = False

    def __post_init__(self):
        if not isinstance(self.population, (tuple, range, TransitionPositions)):
            object.__setattr__(self, "population", tuple(self.population))
        object.__setattr__(self, "orders", tuple(index(order) for order in self.orders))
        if any(order < 0 for order in self.orders):
            raise ValueError("observation orders must be nonnegative")

    @property
    def count(self):
        n = len(self.population)
        return sum(comb(n, order) for order in self.orders if order <= n)

    def __len__(self):
        return self.count

    def __bool__(self):
        return self.count > 0

    def __iter__(self):
        n = len(self.population)
        for order in self.orders:
            if order > n:
                continue
            if not isinstance(self.population, TransitionPositions):
                if self.flatten:
                    for selection in combinations(self.population, order):
                        yield tuple(value for block in selection for value in block)
                else:
                    yield from combinations(self.population, order)
                continue
            indices = list(range(order))
            selected = [self.population[i] for i in indices]
            while True:
                yield (
                    tuple(value for block in selected for value in block)
                    if self.flatten
                    else tuple(selected)
                )
                for position in range(order - 1, -1, -1):
                    if indices[position] != n - order + position:
                        break
                else:
                    break
                indices[position] += 1
                selected[position] = self.population[indices[position]]
                for later in range(position + 1, order):
                    indices[later] = indices[later - 1] + 1
                    selected[later] = self.population[indices[later]]

    def __getitem__(self, position):
        if isinstance(position, slice):
            return tuple(self[i] for i in range(*position.indices(self.count)))
        position = index(position)
        if position < 0:
            position += self.count
        if position < 0 or position >= self.count:
            raise IndexError("observation index out of range")
        n = len(self.population)
        for order in self.orders:
            size = comb(n, order) if order <= n else 0
            if position < size:
                break
            position -= size
        indices = []
        start = 0
        for remaining in range(order, 0, -1):
            base = comb(n - start, remaining)
            low, high = start, n - remaining
            while low < high:
                middle = (low + high) // 2
                through_middle = base - comb(n - middle - 1, remaining)
                if position < through_middle:
                    high = middle
                else:
                    low = middle + 1
            position -= base - comb(n - low, remaining)
            indices.append(low)
            start = low + 1
        selection = tuple(self.population[i] for i in indices)
        return (
            tuple(value for block in selection for value in block)
            if self.flatten
            else selection
        )


@dataclass(frozen=True, slots=True)
class OutputChoices(Sequence):
    groups: tuple
    bits: int
    indices_per_group: tuple

    def __post_init__(self):
        object.__setattr__(self, "groups", tuple(tuple(group) for group in self.groups))
        object.__setattr__(self, "indices_per_group", tuple(self.indices_per_group))
        if self.bits < 1 or len(self.groups) != len(self.indices_per_group):
            raise ValueError("invalid output group layout")

    @property
    def count(self):
        return prod(
            options.count if isinstance(options, ObservationPlan) else len(options)
            for options in self.indices_per_group
        )

    def __len__(self):
        return self.count

    def __bool__(self):
        return self.count > 0

    def __iter__(self):
        iterators = [iter(options) for options in self.indices_per_group]
        selected = []
        for iterator in iterators:
            try:
                selected.append(next(iterator))
            except StopIteration:
                return
        while True:
            yield tuple(
                group[index * self.bits + bit]
                for group, indices in zip(self.groups, selected)
                for index in indices
                for bit in range(self.bits)
            )
            for position in range(len(iterators) - 1, -1, -1):
                try:
                    selected[position] = next(iterators[position])
                    break
                except StopIteration:
                    iterators[position] = iter(self.indices_per_group[position])
                    selected[position] = next(iterators[position])
            else:
                break

    def __getitem__(self, position):
        if isinstance(position, slice):
            return tuple(self[i] for i in range(*position.indices(self.count)))
        position = index(position)
        if position < 0:
            position += self.count
        if position < 0 or position >= self.count:
            raise IndexError("output choice out of range")
        selected = []
        for options in reversed(self.indices_per_group):
            size = options.count if isinstance(options, ObservationPlan) else len(options)
            position, digit = divmod(position, size)
            selected.append(options[digit])
        return tuple(
            group[index * self.bits + bit]
            for group, indices in zip(self.groups, reversed(selected))
            for index in indices
            for bit in range(self.bits)
        )


@dataclass(frozen=True, slots=True)
class OutputRequests(Sequence):
    groups: tuple
    bits: int
    share_count: int
    threshold: int
    low_indices: object = field(init=False, repr=False)
    high_indices: object = field(init=False, repr=False)

    def __post_init__(self):
        object.__setattr__(self, "groups", tuple(tuple(group) for group in self.groups))
        if self.bits < 1 or self.share_count < 1:
            raise ValueError("invalid output group layout")
        object.__setattr__(
            self, "low_indices", ObservationPlan(range(self.share_count), (self.threshold,))
        )
        object.__setattr__(
            self,
            "high_indices",
            ObservationPlan(range(self.share_count), (self.share_count - 1,)),
        )

    @property
    def count(self):
        return (self.low_indices.count + 1) ** len(self.groups)

    def __len__(self):
        return self.count

    def __bool__(self):
        return True

    def _request(self, selected):
        return {
            "request": tuple(selected),
            "choices": OutputChoices(
                self.groups,
                self.bits,
                tuple(
                    self.high_indices if indices is None else (indices,) for indices in selected
                ),
            ),
            "expanded_outputs": tuple(
                i for i, indices in enumerate(selected) if indices is None
            ),
        }

    def __iter__(self):
        iterators = [chain(self.low_indices, (None,)) for _ in self.groups]
        selected = [next(iterator) for iterator in iterators]
        while True:
            yield self._request(selected)
            for position in range(len(iterators) - 1, -1, -1):
                try:
                    selected[position] = next(iterators[position])
                    break
                except StopIteration:
                    iterators[position] = chain(self.low_indices, (None,))
                    selected[position] = next(iterators[position])
            else:
                break

    def __getitem__(self, position):
        if isinstance(position, slice):
            return tuple(self[i] for i in range(*position.indices(self.count)))
        position = index(position)
        if position < 0:
            position += self.count
        if position < 0 or position >= self.count:
            raise IndexError("output request out of range")
        low_count = self.low_indices.count
        selected = []
        for _ in self.groups:
            position, digit = divmod(position, low_count + 1)
            selected.append(self.low_indices[digit] if digit < low_count else None)
        return self._request(tuple(reversed(selected)))


class CircuitIR:

    def __init__(
        self,
        name,
        expressions,
        reference,
        mapGates,
        mapRow2exp,
        mapRow2Obs,
        encodingRow,
        decodingRow,
        secrets,
        secretsBits,
        outputs,
        outputsBits,
        secretsInputs,
        secretsInputsBits,
        secretsOutputs,
        secretsOutputsBits,
        invertible,
        shareNum,
        shareIndex,
        randoms,
        bits,
        field,
        logic,
        observationsIn,
        observationsOutput,
        observationsCheck,
        checksize,
        checksize_rp,
        reg,
        row_mi,
        checkOptions,
    ):

        self.instructions = ()
        self.name = name
        self.expressions = expressions
        self.reference = reference
        self.mapGates = mapGates
        self.mapRow2exp = mapRow2exp
        self.mapRow2Obs = mapRow2Obs
        self.encodingRow = encodingRow
        self.decodingRow = decodingRow
        self.secrets = secrets
        self.secretsBits = secretsBits
        self.outputs = outputs
        self.outputsBits = outputsBits
        self.secretsInputs = secretsInputs
        self.secretsInputsBits = secretsInputsBits
        self.secretsOutputs = secretsOutputs
        self.secretsOutputsBits = secretsOutputsBits
        self.invertible = invertible
        self.shareNum = shareNum
        self.shareIndex = shareIndex
        self.randoms = randoms
        self.bits = bits
        self.field = field
        self.logic = logic

        self.observationsIn = observationsIn
        self.observationsOutput = observationsOutput
        self.observationsCheck = observationsCheck
        self.checksize = checksize
        self.checksize_rp = checksize_rp
        self.reg = reg

        self.row_mi = row_mi
        self.row_verdict = {}
        self.row_mi_text = {}
        self.rp_statistics = None
        self.verification_result = None

        self.checkOptions = checkOptions

    def __getstate__(self):
        state = self.__dict__.copy()
        state.pop("event", None)
        return state
