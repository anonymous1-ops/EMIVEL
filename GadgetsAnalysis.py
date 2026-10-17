import ast
import keyword
import re
from functools import reduce
from itertools import product
from math import comb
from warnings import warn

from galois import GF
from sympy import Add, Dummy, Integer, Mul, Pow, S, symbols, sympify

from auxiliary import sympyGF2N, sympyGFp
from Parameters import (
    Instruction,
    ObservationPlan,
    OutputChoices,
    OutputRequests,
    TransitionPositions,
)


class CircuitParser:
    def __init__(self, circuit):
        self.gadget = circuit

    def parse(self):
        circuit = self.gadget
        circuit.mapRow2exp = {}
        widths = set()
        declarations = set()
        with open(circuit.checkOptions["path"], encoding="utf-8-sig") as script:
            for row, original in enumerate(script, 1):
                item = original.split("#", 1)[0].strip()
                if not item:
                    continue
                if item == "end":
                    break
                if "<" in item:
                    raise ValueError(
                        f"Line {row}: per-line recovery probabilities are unsupported"
                    )
                if item.startswith("@"):
                    circuit.reference.append(re.sub(r"\s+", "", item[1:]))
                    continue
                if "=" in item:
                    expression = re.sub(r"\s+", "", item)
                    if ":=" in expression:
                        circuit.encodingRow.append(str(row))
                        expression = expression.replace(":=", "=", 1)
                    if "=:" in expression:
                        circuit.decodingRow.append(expression.replace("=:", "=", 1))
                        continue
                    circuit.expressions.append(expression)
                    circuit.mapRow2exp[str(row)] = expression
                    for operator in circuit.mapGates:
                        circuit.mapGates[operator] += expression.count(operator)
                    continue
                parts = item.split(None, 1)
                directive = parts[0]
                if len(parts) != 2:
                    raise ValueError(f"Line {row}: missing argument for directive {directive}")
                value = parts[1].replace(" ", "")
                if directive in ("noise", "para", "vnc", "nc"):
                    raise ValueError(f"Line {row}: unsupported directive {directive}")
                if "public" in directive.lower():
                    raise ValueError(
                        "Verification conditioned on public data is not implemented"
                    )
                if directive == "gadget":
                    circuit.name = parts[1].strip()
                elif directive == "shares":
                    circuit.shareNum = int(value)
                elif directive == "randoms":
                    values = symbols(value, seq=True)
                    if directive in declarations or len(values) != len(set(values)):
                        raise ValueError(f"Line {row}: duplicate randomness declaration")
                    if any(
                        not str(symbol).isidentifier() or keyword.iskeyword(str(symbol))
                        for symbol in values
                    ):
                        raise ValueError(f"Line {row}: invalid randomness identifier")
                    declarations.add(directive)
                    circuit.randoms = values
                elif directive == "invert":
                    circuit.invertible = symbols(value)
                elif directive == "field":
                    if value == "bool":
                        circuit.field, circuit.logic = "bool", True
                    else:
                        field_tree = ast.parse(value, mode="eval")
                        if any(
                            not isinstance(
                                node,
                                (
                                    ast.Expression,
                                    ast.Constant,
                                    ast.BinOp,
                                    ast.Pow,
                                    ast.Add,
                                    ast.Sub,
                                    ast.Mult,
                                ),
                            )
                            or (isinstance(node, ast.Constant) and type(node.value) is not int)
                            for node in ast.walk(field_tree)
                        ):
                            raise ValueError(
                                f"Line {row}: field size must be an integer arithmetic expression"
                            )
                        circuit.field = eval(
                            compile(field_tree, "<field>", "eval"), {"__builtins__": {}}
                        )
                        if type(circuit.field) is not int or circuit.field <= 1:
                            raise ValueError("Field size must be an integer greater than 1")
                        circuit.logic = False
                else:
                    match = re.fullmatch(
                        r"(?:(\d+)bit)?(secrets|secretouts|inputs|outputs)", directive
                    )
                    if match is None:
                        raise ValueError(f"Line {row}: unknown directive {directive}")
                    width_text, kind = match.groups()
                    width = int(width_text) if width_text else 1
                    if width <= 0:
                        raise ValueError(f"Line {row}: bit width must be a positive integer")
                    widths.add(width)
                    values = symbols(value, seq=True)
                    if kind in declarations or len(values) != len(set(values)):
                        raise ValueError(f"Line {row}: duplicate {kind} declaration")
                    if any(
                        not str(symbol).isidentifier() or keyword.iskeyword(str(symbol))
                        for symbol in values
                    ):
                        raise ValueError(f"Line {row}: invalid {kind} identifier")
                    declarations.add(kind)
                    if kind == "inputs":
                        ranges = []
                        for group in value.split(","):
                            bounds = re.fullmatch(r"[A-Za-z_]\w*?(\d+):(\d+)", group)
                            if bounds is None:
                                raise ValueError(
                                    f"Line {row}: input shares must use the name0:n format"
                                )
                            start, stop = map(int, bounds.groups())
                            ranges.append(tuple(range(start, stop)))
                        if not ranges[0] or any(indices != ranges[0] for indices in ranges):
                            raise ValueError(
                                f"Line {row}: input share ranges must be identical and nonempty"
                            )
                        circuit.shareIndex = list(ranges[0])
                        circuit.shareNum = len(circuit.shareIndex)
                    target = {
                        "secrets": "secrets",
                        "secretouts": "outputs",
                        "inputs": "secretsInputs",
                        "outputs": "secretsOutputs",
                    }[kind]
                    setattr(circuit, target, {symbol: i for i, symbol in enumerate(values)})
                    if width_text:
                        bits = symbols(
                            tuple(f"{symbol}{bit}" for symbol in values for bit in range(width))
                        )
                        if len(bits) != len(set(bits)):
                            raise ValueError(f"Line {row}: expanded bit identifiers must be unique")
                        setattr(
                            circuit,
                            target + "Bits",
                            {symbol: i for i, symbol in enumerate(bits)},
                        )
                        circuit.bits = width
        if len(widths) > 1:
            raise ValueError("Inputs, outputs, and secrets must have the same bit width")
        self.validate()
        return circuit

    def validate(self):
        circuit = self.gadget
        options = circuit.checkOptions
        model = options["security"]
        if not circuit.name:
            raise ValueError("A gadget name must be declared")
        if circuit.shareNum <= 0 or circuit.bits <= 0:
            raise ValueError("Share count and bit width must be positive integers")
        if not circuit.logic:
            field = GF(circuit.field)
            if field.degree > 1 and field.characteristic != 2:
                raise NotImplementedError(
                    "Security analysis supports only prime fields GF(p) and binary extension fields GF(2^n)"
                )
        inputs = circuit.secretsInputsBits if circuit.bits > 1 else circuit.secretsInputs
        outputs = circuit.secretsOutputsBits if circuit.bits > 1 else circuit.secretsOutputs
        secrets = circuit.secretsBits if circuit.bits > 1 else circuit.secrets
        secretouts = circuit.outputsBits if circuit.bits > 1 else circuit.outputs
        if not inputs or not outputs:
            raise ValueError("Input and output shares must be declared")
        group_width = circuit.shareNum * circuit.bits
        if len(inputs) % group_width or len(outputs) % group_width:
            raise ValueError("Input or output share counts do not match shares/bits")
        if secrets and len(secrets) * circuit.shareNum != len(inputs):
            raise ValueError("Declared secrets do not match the input-share families")
        if secretouts and len(secretouts) * circuit.shareNum != len(outputs):
            raise ValueError("Declared secret outputs do not match the output-share families")
        if set(circuit.randoms) & (set(inputs) | set(circuit.secretsInputs)):
            raise ValueError("Random masks and input shares must have distinct names")
        if set(circuit.randoms) & (set(secrets) | set(circuit.secrets)):
            raise ValueError("Random masks and secrets must have distinct names")
        if not secrets:
            if model in ("probing_secret", "rps_secret"):
                raise ValueError("NO secrets.")
            warn("NO secrets?")
        if not secretouts:
            if options["correctness"] != "null":
                raise ValueError("NO secretouts?")
            warn("NO secretouts?")
        if not circuit.randoms:
            warn("NO randomness?")
        LeakageAnalyzer.validate_options(options["robust"], circuit.expressions, model)
        if not getattr(circuit, "instructions", ()):
            parsed = {}
            instructions = []
            last_write = {}
            encoded = set()
            allowed = (
                ast.Expression,
                ast.BinOp,
                ast.UnaryOp,
                ast.Name,
                ast.Load,
                ast.Constant,
                ast.Add,
                ast.Sub,
                ast.Mult,
                ast.Div,
                ast.Pow,
                ast.BitAnd,
                ast.BitOr,
                ast.BitXor,
                ast.Invert,
                ast.UAdd,
                ast.USub,
            )

            def expression_info(text, row):
                text = text.strip()
                if text in parsed:
                    return parsed[text]
                try:
                    tree = ast.parse(text, mode="eval")
                except SyntaxError as error:
                    raise ValueError(
                        f"Line {row}: invalid expression syntax: {text}"
                    ) from error
                syntax = tuple(ast.walk(tree))
                if any(
                    not isinstance(node, allowed)
                    or (isinstance(node, ast.Constant) and type(node.value) not in (int, bool))
                    for node in syntax
                ):
                    raise ValueError(
                        f"Line {row}: only variables, integer constants, and arithmetic/bitwise operators are supported"
                    )
                operations = (
                    (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Pow, ast.UAdd, ast.USub)
                    if circuit.logic
                    else (ast.BitAnd, ast.BitOr, ast.BitXor, ast.Invert)
                )
                if any(isinstance(node, operations) for node in syntax):
                    raise ValueError(
                        f"Line {row}: operator is incompatible with the declared field"
                    )
                if circuit.logic and any(
                    isinstance(node, ast.Constant) and node.value not in (0, 1)
                    for node in syntax
                ):
                    raise ValueError(f"Line {row}: bool mode supports only constants 0 and 1")
                nodes, names = [], []
                stack = [(tree.body, False)]
                while stack:
                    node, visited = stack.pop()
                    if visited:
                        nodes.append(node)
                    else:
                        stack.append((node, True))
                        if isinstance(node, ast.Name):
                            names.append(node.id)
                        elif isinstance(node, ast.BinOp):
                            stack.extend(((node.right, False), (node.left, False)))
                        elif isinstance(node, ast.UnaryOp):
                            stack.append((node.operand, False))
                dependencies = frozenset(symbols(name) for name in names)
                parsed[text] = tree, dependencies, tuple(names), syntax, tuple(nodes)
                return parsed[text]

            rows = list(circuit.mapRow2exp.items())
            rows.extend(
                (f"decoding:{i + 1}", line) for i, line in enumerate(circuit.decodingRow)
            )
            for row, expression in rows:
                lhs, rhs = map(str.strip, expression.split("=", 1))
                if not lhs.isidentifier() or keyword.iskeyword(lhs):
                    raise ValueError(f"Line {row}: invalid assignment target: {lhs}")
                stage = (
                    "decoding"
                    if str(row).startswith("decoding:")
                    else "encoding" if row in circuit.encodingRow else "body"
                )
                if stage == "encoding":
                    if lhs in encoded:
                        raise ValueError(
                            f"Input share {lhs} cannot be encoded more than once using :="
                        )
                    encoded.add(lhs)
                pieces = rhs.split(";", 1)
                value = pieces[0].strip()
                barrier = False
                while value.startswith("[") and value.endswith("]"):
                    barrier = True
                    value = value[1:-1].strip()
                extensions = (
                    tuple(part.strip() for part in pieces[1].split(","))
                    if len(pieces) == 2
                    else ()
                )
                tree, dependencies, names, syntax, nodes = expression_info(value, row)
                for extension in extensions:
                    expression_info(extension, row)
                instructions.append(
                    Instruction(
                        len(instructions),
                        lhs,
                        value,
                        expression,
                        stage,
                        row,
                        tree,
                        dependencies,
                        names,
                        last_write.get(lhs),
                        barrier,
                        extensions,
                        syntax,
                        nodes,
                        tuple((name, last_write.get(name)) for name in names),
                    )
                )
                if lhs != "reg":
                    last_write[lhs] = len(instructions) - 1
            circuit.instructions = tuple(instructions)
            circuit.expression_info = parsed
        assigned = set(map(str, circuit.randoms)) | set(map(str, inputs))
        if model in ("probing_secret", "rps_secret"):
            assigned.update(map(str, secrets))
        encoding_assigned = assigned | set(map(str, secrets))
        output_assignments = set()
        circuit.reg = {}
        for instruction in circuit.instructions:
            names = set(instruction.operand_names)
            for text in instruction.extensions:
                names.update(circuit.expression_info[text][2])
            available = encoding_assigned if instruction.stage == "encoding" else assigned
            if instruction.stage == "decoding":
                if options["correctness"] == "null":
                    continue
            unknown = names - available
            if unknown:
                raise ValueError(
                    f"Line {instruction.source_line}: undefined variables: {', '.join(sorted(unknown))}"
                )
            if instruction.lhs != "reg":
                assigned.add(instruction.lhs)
                encoding_assigned.add(instruction.lhs)
                if instruction.stage != "decoding":
                    output_assignments.add(instruction.lhs)
                if instruction.stage == "body" and instruction.barrier:
                    circuit.reg[instruction.index] = instruction.lhs
            elif instruction.stage == "body":
                if not instruction.rhs.isidentifier() or not instruction.operand_versions:
                    raise ValueError(
                        f"Line {instruction.source_line}: reg requires one assigned variable"
                    )
                version = instruction.operand_versions[0][1]
                location = ("input", instruction.rhs) if version is None else version
                circuit.reg[location] = instruction.rhs
        missing = set(map(str, outputs)) - output_assignments
        if missing:
            raise ValueError("Unassigned output shares: " + ", ".join(sorted(missing)))
        if options["correctness"] != "null" and set(map(str, secretouts)) - assigned:
            raise ValueError(
                "Functional correctness requires decoding assignments for secretouts"
            )
        if not circuit.logic and any(
            isinstance(node, ast.BinOp) and (
                isinstance(node.op, ast.Div)
                or isinstance(node.op, ast.Pow) and not (
                    isinstance(node.right, ast.Constant)
                    and type(node.right.value) in (int, bool)
                    and node.right.value >= 0
                )
            )
            for instruction in circuit.instructions
            if instruction.stage != "decoding" or options["correctness"] != "null"
            for text in (instruction.rhs,) + instruction.extensions
            for node in circuit.expression_info[text][4]
        ):
            LeakageAnalyzer(circuit).validate_domains()
        return circuit


class CorrectnessVerifier:
    SBOXES = {
        "AES8": bytes.fromhex(
            "63 7c 77 7b f2 6b 6f c5 30 01 67 2b fe d7 ab 76 "
            "ca 82 c9 7d fa 59 47 f0 ad d4 a2 af 9c a4 72 c0 "
            "b7 fd 93 26 36 3f f7 cc 34 a5 e5 f1 71 d8 31 15 "
            "04 c7 23 c3 18 96 05 9a 07 12 80 e2 eb 27 b2 75 "
            "09 83 2c 1a 1b 6e 5a a0 52 3b d6 b3 29 e3 2f 84 "
            "53 d1 00 ed 20 fc b1 5b 6a cb be 39 4a 4c 58 cf "
            "d0 ef aa fb 43 4d 33 85 45 f9 02 7f 50 3c 9f a8 "
            "51 a3 40 8f 92 9d 38 f5 bc b6 da 21 10 ff f3 d2 "
            "cd 0c 13 ec 5f 97 44 17 c4 a7 7e 3d 64 5d 19 73 "
            "60 81 4f dc 22 2a 90 88 46 ee b8 14 de 5e 0b db "
            "e0 32 3a 0a 49 06 24 5c c2 d3 ac 62 91 95 e4 79 "
            "e7 c8 37 6d 8d d5 4e a9 6c 56 f4 ea 65 7a ae 08 "
            "ba 78 25 2e 1c a6 b4 c6 e8 dd 74 1f 4b bd 8b 8a "
            "70 3e b5 66 48 03 f6 0e 61 35 57 b9 86 c1 1d 9e "
            "e1 f8 98 11 69 d9 8e 94 9b 1e 87 e9 ce 55 28 df "
            "8c a1 89 0d bf e6 42 68 41 99 2d 0f b0 54 bb 16 "
        ),
        "keccak5": bytes.fromhex(
            "00 05 0a 0b 14 11 16 17 09 0c 03 02 0d 08 0f 0e "
            "12 15 18 1b 06 01 04 07 1a 1d 10 13 1e 19 1c 1f "
        ),
        "midori4": bytes.fromhex("0c 0a 0d 03 0e 0b 0f 07 08 09 01 05 00 02 04 06 "),
        "present4": bytes.fromhex("0c 05 06 0b 09 00 0a 0d 03 0e 0f 08 04 07 01 02 "),
        "prince4": bytes.fromhex("0b 0f 03 02 0a 0c 09 01 06 07 08 00 0e 05 0d 04 "),
    }

    def __init__(self, circuit):
        self.gadget = circuit
        self.bits = circuit.bits
        self.secrets = circuit.secretsBits if self.bits > 1 else circuit.secrets
        self.out = circuit.outputsBits if self.bits > 1 else circuit.outputs
        self.randoms = set(circuit.randoms)
        self.correctness = circuit.checkOptions["correctness"]
        self.GF_field = "bool" if circuit.logic else GF(circuit.field)

    @staticmethod
    def compile(name, expressions, inputs, outputs, GF_field=None, namespace=None):
        if not name.isidentifier() or keyword.iskeyword(name):
            name = "_circuit"
        source = [f"def {name}({','.join(inputs)}):"]
        source.extend(f"    {line}" for line in expressions)
        source.append(f"    return [{','.join(outputs)}]")
        namespace = {} if namespace is None else dict(namespace)
        if GF_field is not None:
            namespace["GF_field"] = GF_field
        exec(compile("\n".join(source), "<circuit>", "exec"), namespace)
        return namespace[name]

    def _reference(self, which):
        is_bool = self.gadget.logic
        width = max(1, self.bits) if is_bool else 1
        if which == "ADD":
            return lambda *args: [
                reduce(
                    lambda left, right: left ^ right if is_bool else left + right,
                    args[i::width],
                )
                for i in range(width)
            ]
        if which == "AND":
            return lambda *args: [
                reduce(
                    lambda left, right: left & right if is_bool else left * right,
                    args[i::width],
                )
                for i in range(width)
            ]
        if which == "COPY":
            return lambda *args: [
                value
                for i in range(0, len(args), width)
                for _ in range(2)
                for value in args[i : i + width]
            ]
        if which not in self.SBOXES:
            raise ValueError(f"Unknown gate: {which}")
        table = self.SBOXES[which]
        width = (len(table) - 1).bit_length()
        return lambda *args: [
            (table[int("".join(map(str, args)), 2)] >> (width - 1 - bit)) & 1
            for bit in range(width)
        ]

    def check(self):
        if self.correctness == "null":
            warn("Consider enabling functional correctness verification")
            return None
        from operator import index

        is_bool = self.gadget.logic
        elements = (0, 1) if is_bool else self.GF_field.elements
        field_order = 2 if is_bool else int(self.GF_field.order)
        prime_field = not is_bool and self.GF_field.degree == 1

        def field_power(base, exponent):
            if not exponent.is_Integer:
                raise TypeError("Finite-field operations support only integer exponents")
            exponent = int(exponent)
            if exponent:
                reduced = (abs(exponent) - 1) % (field_order - 1) + 1
                exponent = reduced if exponent > 0 else -reduced
            return base ** exponent

        used_names = set(map(str, self.secrets)) | set(map(str, self.randoms))
        used_names.add(self.gadget.name)
        used_names.update(re.findall(
            r"\b[A-Za-z_]\w*\b",
            "\n".join(self.gadget.expressions + self.gadget.decodingRow + self.gadget.reference),
        ))
        integer_name, power_name, field_name = "_integer", "_field_power", "_field"
        while integer_name in used_names:
            integer_name = "_" + integer_name
        while power_name in used_names:
            power_name = "_" + power_name
        while field_name in used_names:
            field_name = "_" + field_name
        field_namespace = {
            integer_name: Integer,
            power_name: field_power,
            field_name: self.GF_field,
        }
        secret_names = list(map(str, self.secrets))
        random_names = list(map(str, self.randoms))
        circuit_outputs = list(map(str, self.out))
        bit_sboxes = {"AES8": 8, "keccak5": 5, "midori4": 4, "present4": 4, "prince4": 4}
        if self.correctness in bit_sboxes:
            width = bit_sboxes[self.correctness]
            if not is_bool or len(secret_names) != width or len(circuit_outputs) != width:
                raise ValueError(
                    f"{self.correctness} requires {width}-bit Boolean inputs and outputs"
                )

        allowed = (
            ast.Module,
            ast.Assign,
            ast.Name,
            ast.Load,
            ast.Store,
            ast.BinOp,
            ast.BitAnd,
            ast.BitOr,
            ast.BitXor,
            ast.UnaryOp,
            ast.Invert,
            ast.Constant,
        )

        def boolean_tree(expressions):
            tree = ast.parse("\n".join(expressions))
            if not all(
                isinstance(n, allowed)
                and (
                    not isinstance(n, ast.Constant)
                    or (type(n.value) in (int, bool) and n.value in (0, 1))
                )
                for n in ast.walk(tree)
            ):
                raise ValueError(
                    "Boolean correctness checks support only variables, 0/1/True/False, and & | ^ ~"
                )
            return tree

        class FieldConstants(ast.NodeTransformer):
            integer_exponent = False

            def visit_Name(self, node):
                if self.integer_exponent:
                    return ast.copy_location(
                        ast.Call(
                            func=ast.Name(id=integer_name, ctx=ast.Load()),
                            args=[node],
                            keywords=[],
                        ),
                        node,
                    )
                return node

            def visit_Constant(self, node):
                if type(node.value) in (int, bool):
                    value = int(node.value)
                    if prime_field and not self.integer_exponent:
                        value %= field_order
                    return ast.copy_location(
                        ast.Call(
                            func=ast.Name(
                                id=integer_name if self.integer_exponent else field_name,
                                ctx=ast.Load(),
                            ),
                            args=[ast.Constant(value=value)],
                            keywords=[],
                        ),
                        node,
                    )
                return node

            def visit_BinOp(self, node):
                if self.integer_exponent:
                    return self.generic_visit(node)
                node.left = self.visit(node.left)
                if not isinstance(node.op, ast.Pow):
                    node.right = self.visit(node.right)
                elif all(
                    isinstance(
                        child,
                        (
                            ast.Constant,
                            ast.BinOp,
                            ast.UnaryOp,
                            ast.Add,
                            ast.Sub,
                            ast.Mult,
                            ast.Div,
                            ast.Pow,
                            ast.UAdd,
                            ast.USub,
                        ),
                    )
                    for child in ast.walk(node.right)
                ):
                    for child in ast.walk(node.right):
                        if isinstance(child, ast.Constant) and type(child.value) is bool:
                            child.value = int(child.value)
                    exponent = sympify(ast.unparse(node.right))
                    if not exponent.is_Integer:
                        raise TypeError("Finite-field operations support only integer exponents")
                    exponent = int(exponent)
                    if exponent:
                        reduced = (abs(exponent) - 1) % (field_order - 1) + 1
                        exponent = reduced if exponent > 0 else -reduced
                    node.right = ast.Constant(value=exponent)
                else:
                    self.integer_exponent = True
                    exponent = self.visit(node.right)
                    self.integer_exponent = False
                    return ast.copy_location(
                        ast.Call(
                            func=ast.Name(id=power_name, ctx=ast.Load()),
                            args=[node.left, exponent],
                            keywords=[],
                        ),
                        node,
                    )
                return node

            def visit_Call(self, node):

                return node

            def visit_Subscript(self, node):
                node.value = self.visit(node.value)
                return node

        def prepare(lines):
            expressions = []
            for line in lines:
                lhs, rhs = map(str.strip, line.split("=", 1))
                if lhs == "reg":
                    continue
                rhs = rhs.split(";", 1)[0].strip()
                while rhs.startswith("[") and rhs.endswith("]"):
                    rhs = rhs[1:-1].strip()
                if is_bool:
                    rhs = re.sub(
                        r"(?<![\w.])[01](?![\w.])",
                        lambda m: "True" if m.group() == "1" else "False",
                        rhs,
                    )
                else:
                    tree = FieldConstants().visit(ast.parse(rhs, mode="eval"))
                    rhs = ast.unparse(ast.fix_missing_locations(tree))
                expressions.append(lhs + "=" + rhs)
            if is_bool:
                boolean_tree(expressions)
            return expressions

        if self.correctness == "user" and self.gadget.reference:
            Freference = self.compile(
                self.gadget.name,
                prepare(self.gadget.reference),
                secret_names,
                circuit_outputs,
                self.GF_field,
                field_namespace,
            )
        elif self.correctness not in ("null", "user"):
            Freference = self._reference(self.correctness)
        else:
            raise RuntimeError("No reference function is available")

        expressions = prepare(self.gadget.expressions + self.gadget.decodingRow)

        unassigned_randoms = set(random_names)
        used_randoms = set()
        for statement in ast.parse("\n".join(expressions)).body:
            used_randoms.update(
                node.id
                for node in ast.walk(statement)
                if isinstance(node, ast.Name)
                and isinstance(node.ctx, ast.Load)
                and node.id in unassigned_randoms
            )
            if isinstance(statement, ast.Assign):
                unassigned_randoms.difference_update(
                    target.id for target in statement.targets if isinstance(target, ast.Name)
                )
        used_randoms.update(set(circuit_outputs) & unassigned_randoms)
        random_names = [name for name in random_names if name in used_randoms]
        circuit_inputs = secret_names + random_names
        Fcircuit = self.compile(
            self.gadget.name, expressions, circuit_inputs, circuit_outputs,
            self.GF_field, field_namespace
        )

        packed = is_bool
        if packed:
            tree = boolean_tree(expressions)
            for node in ast.walk(tree):
                if isinstance(node, ast.Constant):
                    node.value = -int(node.value)
            Fcircuit = self.compile(
                self.gadget.name,
                [ast.unparse(n) for n in tree.body],
                circuit_inputs,
                circuit_outputs,
            )

        packed_bits = min(len(random_names), 12) if packed else 0
        lanes = 1 << packed_bits
        lane_mask = (1 << lanes) - 1
        planes = (
            tuple(
                sum(((lane >> bit) & 1) << lane for lane in range(lanes))
                for bit in reversed(range(packed_bits))
            )
            if packed
            else ()
        )

        def mask_tests():
            if packed:
                for prefix in product((0, 1), repeat=len(random_names) - packed_bits):
                    yield tuple(-b for b in prefix) + planes
            else:
                yield from product(elements, repeat=len(random_names))

        def normalize(values):
            return tuple((index(v) & 1) if is_bool else index(v) for v in values)

        def tests():
            for check in product(elements, repeat=len(secret_names)):
                expected = normalize(Freference(*check))
                if packed:
                    expected = tuple(lane_mask if b else 0 for b in expected)
                for masks in mask_tests():
                    yield check, masks, expected

        orders = [(False, False)]
        if is_bool and self.correctness in bit_sboxes:
            orders = list(product((False, True), repeat=2))

        total = len(elements) ** (len(secret_names) + len(random_names))
        event = getattr(self.gadget, "event", None)
        if event:
            event(
                "message",
                {
                    "message": f"Functional correctness: exhaustively checking {total} input/random assignments; {lanes if packed else 1} assignments per batch"
                },
            )
        iterator = tests()
        if event:
            iterator = event("iterate", {"items": iterator, "total": total // lanes})
        for check, masks, expected in iterator:
            inputs = tuple(-int(b) for b in check) if packed else tuple(check)
            results = {}
            remaining = []
            for reverse_in, reverse_out in orders:
                if reverse_in not in results:
                    x = inputs[::-1] if reverse_in else inputs
                    actual = Fcircuit(*(x + masks))
                    results[reverse_in] = (
                        tuple(int(b) & lane_mask for b in actual)
                        if packed
                        else normalize(actual)
                    )
                target = expected[::-1] if reverse_out else expected
                if results[reverse_in] == target:
                    remaining.append((reverse_in, reverse_out))
            orders = remaining
            if not orders:
                raise RuntimeError(
                    f"Correctness failed: input={tuple(map(int, check))}; "
                    "no fixed input/output bit order passes all checked assignments"
                )

        if event:
            event(
                "message",
                {
                    "message": "Functional correctness verified for all input and random assignments"
                },
            )
        return True


class LeakageAnalyzer:
    LEAKAGE_OPTIONS = (
        "maskverifTG",
        "ironmaskTG",
        "glitch",
        "transition",
        "transitionall",
        "transitionxor",
        "hw_sumed",
        "hw_vector",
    )

    def __init__(self, circuit):
        self.gadget = circuit

        self.logic = circuit.logic
        self.instructions = tuple(
            item for item in circuit.instructions if item.stage != "decoding"
        )
        self._symbol_cache = {}
        self.GF_field = "bool"
        self.overload_sympyeval = None
        self.bits = self.gadget.bits
        self.secrets = self.gadget.secretsBits if self.bits > 1 else self.gadget.secrets

        self.sharesIn = (
            self.gadget.secretsInputsBits if self.bits > 1 else self.gadget.secretsInputs
        )
        self.sharesOut = (
            self.gadget.secretsOutputsBits if self.bits > 1 else self.gadget.secretsOutputs
        )
        self.randoms = set(self.gadget.randoms)
        encoding_sources, body_sources = set(), set()
        for instruction in self.instructions:
            if instruction.stage == "encoding":
                encoding_sources.update(instruction.dependencies)
            elif instruction.stage == "body":
                body_sources.update(instruction.dependencies)
                for extension in instruction.extensions:
                    body_sources.update(circuit.expression_info[extension][1])
        self.encoding_randoms = (encoding_sources - body_sources) & self.randoms
        self.cmax = self.gadget.checkOptions["cmax"]
        self.mapping = {
            id: (
                id // (self.bits * self.gadget.shareNum),
                id % self.bits,
                (id // self.bits) % self.gadget.shareNum,
            )
            for id in range(len(self.sharesOut))
        }
        self.robust = self.validate_options(
            self.gadget.checkOptions["robust"],
            self.gadget.expressions,
            self.gadget.checkOptions["security"],
        )
        self.model_str = self.gadget.checkOptions["security"]
        self.threshold = self.gadget.checkOptions["threshold"]
        self.encoding_shares = self.gadget.encodingRow

        if not self.gadget.logic:
            self.GF_field = GF(self.gadget.field)
            if self.GF_field.degree > 1 and self.GF_field.characteristic != 2:
                raise NotImplementedError(
                    "Security analysis supports only prime fields GF(p) and binary extension fields GF(2^n)"
                )
            if self.GF_field.characteristic == 2 and self.GF_field.degree > 1:
                self.overload_sympyeval = sympyGF2N()
            else:
                self.overload_sympyeval = sympyGFp()
            self.overload_sympyeval.set_field(self.GF_field)

    @staticmethod
    def validate_options(options, expressions=(), model=None):
        unknown = set(options).difference(LeakageAnalyzer.LEAKAGE_OPTIONS)
        if unknown:
            raise ValueError("Unknown leakage options: " + ", ".join(sorted(unknown)))
        if "hw_sumed" in options and "hw_vector" in options:
            raise ValueError("Choose either hw_sumed or hw_vector, not both")
        if model in ("rps_secret", "rps_share", "rpc", "rpe"):
            if options:
                raise ValueError(
                    "Random probing supports Standard observations only; robust and HW switches are not supported"
                )
            if any(";" in expression for expression in expressions):
                raise ValueError(
                    "Random probing does not support manual semicolon leakage extensions"
                )
            return 0
        for name, code in (
            ("maskverifTG", 9),
            ("ironmaskTG", 10),
        ):
            if name not in options:
                continue
            allowed = (name, "hw_sumed", "hw_vector")
            if any(option not in allowed for option in options):
                raise ValueError(f"{name} cannot be combined with these robust switches")
            if any(";" in expression for expression in expressions):
                raise NotImplementedError(
                    f"{name} does not support manual semicolon leakage extensions"
                )
            return code
        if "glitch" in options:
            if "transitionall" in options:
                return 33
            return 3 if "transition" in options or "transitionxor" in options else 1
        if "transitionall" in options:
            return 22
        if "transition" in options:
            return 2
        if "transitionxor" in options:
            return 4
        return 5 if "hw_sumed" in options or "hw_vector" in options else 0

    def validate_domains(self):
        check_correctness = self.gadget.checkOptions["correctness"] != "null"
        instructions = tuple(
            instruction for instruction in self.gadget.instructions
            if instruction.stage != "decoding" or check_correctness
        )
        expressions = {
            text for instruction in instructions
            for text in (instruction.rhs,) + instruction.extensions
        }
        from time import monotonic

        import numpy as np
        import psutil

        integer_nodes = set()
        for text in expressions:
            pending = [(self.gadget.expression_info[text][0].body, False)]
            while pending:
                node, integer = pending.pop()
                if integer:
                    integer_nodes.add(node)
                if isinstance(node, ast.BinOp):
                    pending.append((node.left, integer))
                    pending.append((node.right, integer or isinstance(node.op, ast.Pow)))
                elif isinstance(node, ast.UnaryOp):
                    pending.append((node.operand, integer))

        field = self.GF_field
        order = int(field.order)
        proved = set()
        process = psutil.Process()
        started = monotonic()
        max_seconds = float(self.gadget.checkOptions["maxhours"]) * 3600
        max_bytes = float(self.gadget.checkOptions["maxmem"]) * 1024**3
        row = None

        def integer_value(node, env):
            value = self._integer_expression(node, env)
            if not value.is_number:
                raise TypeError("Finite-field operations support only integer exponents")
            return value

        def require_nonzero(expression, description):
            expression = self.overload_sympyeval.evaluate(expression)
            if expression in proved:
                return
            factors = [expression]
            parents = []
            while factors:
                factor = factors.pop()
                if factor == 0:
                    raise ZeroDivisionError(f"Line {row}: {description} is zero")
                if factor in proved or factor.is_Number:
                    continue
                if factor.is_Mul:
                    factors.extend(factor.args)
                    parents.append(factor)
                    continue
                elif factor.is_Pow and factor.exp.is_Integer:
                    if factor.exp:
                        factors.append(factor.base)
                    parents.append(factor)
                    continue
                if factor.is_Symbol:
                    raise ZeroDivisionError(
                        f"Line {row}: {description} can be zero for {{{str(factor)!r}: 0}}"
                    )

                from MIA import MIA

                sources = tuple(sorted(factor.free_symbols, key=str))
                evaluate = MIA._compile_field_expressions((factor,), sources, field)[0]
                width = len(sources)
                node_count = 0
                pending = [factor]
                while pending:
                    current = pending.pop()
                    node_count += 1
                    pending.extend(current.args)
                bytes_per_state = (node_count + width + 1) * 64
                total = order ** width
                offset = 0
                batch_size = min(4096, max(1, 262144 // (node_count + width + 1)))
                while offset < total:
                    if monotonic() - started >= max_seconds:
                        raise RuntimeError("Domain validation incomplete: time limit reached")
                    remaining = max_bytes - process.memory_info().rss
                    if remaining <= 0:
                        raise RuntimeError("Domain validation incomplete: memory limit reached")
                    count = min(batch_size, total - offset)
                    if count * bytes_per_state > remaining:
                        count = min(count, int(remaining // bytes_per_state))
                        if not count:
                            raise RuntimeError("Domain validation incomplete: memory limit reached")
                    values = np.empty((count, width), dtype=field.dtypes[-1])
                    scale = 1
                    for column in range(width - 1, -1, -1):
                        values[:, column] = np.fromiter(
                            ((index // scale) % order for index in range(offset, offset + count)),
                            dtype=field.dtypes[-1], count=count,
                        )
                        scale *= order
                    zero = np.flatnonzero(np.asarray(evaluate(field(values))) == 0)
                    if zero.size:
                        witness = dict(zip(map(str, sources), map(int, values[int(zero[0])])))
                        raise ZeroDivisionError(
                            f"Line {row}: {description} can be zero for {witness}"
                        )
                    offset += count
                proved.add(factor)
            proved.update(parents)
            proved.add(expression)

        def validate_operation(node, values, env, exponent=None):
            if isinstance(node.op, ast.Div):
                candidate = node.right
            elif node in integer_nodes:
                power = integer_value(node.right, env)
                if not power.is_negative:
                    return
                candidate = node.left
            elif exponent is not None and exponent < 0:
                candidate = node.left
            else:
                return
            description = f"divisor/base {ast.unparse(candidate)}"
            if node in integer_nodes:
                if integer_value(candidate, env) == 0:
                    raise ZeroDivisionError(f"Line {row}: integer {description} is zero")
            else:
                require_nonzero(values[candidate], description)

        initial = set(self.secrets) | set(self.sharesIn) | self.randoms
        concrete = {str(symbol): symbol for symbol in initial}
        independent = dict(concrete)
        concrete_security = self.model_str in ("probing_secret", "rps_secret")
        for instruction in instructions:
            row = instruction.source_line
            if instruction.lhs == "reg":
                continue
            if instruction.stage == "encoding":
                concrete[instruction.lhs] = self._evaluate(
                    instruction.rhs, concrete, validate=validate_operation
                )
                independent[instruction.lhs] = symbols(instruction.lhs)
                continue
            environments = (
                (concrete,) if concrete_security or instruction.stage == "decoding"
                else (independent, concrete) if check_correctness else (independent,)
            )
            for index, env in enumerate(environments):
                if index == 0 and instruction.stage == "body":
                    for extension in instruction.extensions:
                        self._evaluate(extension, env, validate=validate_operation)
                env[instruction.lhs] = self._evaluate(
                    instruction.rhs, env, validate=validate_operation
                )

    def _integer_expression(self, node, env):
        local, opaque = {}, {}
        for name in {child.id for child in ast.walk(node) if isinstance(child, ast.Name)}:
            value = self.overload_sympyeval.evaluate(env.get(name, symbols(name)))
            if not value.is_Integer:
                if value not in opaque:
                    opaque[value] = Dummy()
                value = opaque[value]
            local[name] = value
        value = sympify(ast.unparse(node), locals=local)
        return Integer(int(bool(value))) if value in (True, False) else value

    def _evaluate(self, text, env=None, values=None, validate=None):
        info = self.gadget.expression_info[text.strip()]
        tree, dependencies, names, syntax, nodes = info
        env = {} if env is None else env
        values = {} if values is None else values
        argument_lists = {}
        for node in nodes:
            if isinstance(node, ast.Name):
                if node.id not in self._symbol_cache:
                    self._symbol_cache[node.id] = symbols(node.id)
                value = env.get(node.id, self._symbol_cache[node.id])
            elif isinstance(node, ast.Constant):
                value = (
                    (S.true if node.value else S.false) if self.logic else Integer(node.value)
                )
            elif isinstance(node, ast.UnaryOp):
                operand = values[node.operand]
                if isinstance(node.op, ast.Invert):
                    value = ~operand
                elif isinstance(node.op, ast.USub):
                    value = (
                        -operand if operand.is_Integer else Mul(-1, operand, evaluate=False)
                    )
                else:
                    value = operand
            else:
                left, right = values[node.left], values[node.right]
                operation = type(node.op)
                if operation is ast.BitXor:
                    value = left ^ right
                elif operation is ast.BitAnd:
                    value = left & right
                elif operation is ast.BitOr:
                    value = left | right
                elif operation is ast.Add:
                    arguments = (
                        argument_lists.get(node.left, (left,))
                        if isinstance(node.left, ast.BinOp)
                        and isinstance(node.left.op, (ast.Add, ast.Sub))
                        else (left,)
                    )
                    arguments += (
                        argument_lists.get(node.right, (right,))
                        if isinstance(node.right, ast.BinOp)
                        and isinstance(node.right.op, (ast.Add, ast.Sub))
                        else (right,)
                    )
                    argument_lists[node] = arguments
                    value = Add(*arguments, evaluate=False)
                elif operation is ast.Sub:
                    arguments = (
                        argument_lists.get(node.left, (left,))
                        if isinstance(node.left, ast.BinOp)
                        and isinstance(node.left.op, (ast.Add, ast.Sub))
                        else (left,)
                    )
                    arguments += (Mul(-1, right, evaluate=False),)
                    argument_lists[node] = arguments
                    value = Add(*arguments, evaluate=False)
                elif operation is ast.Mult:
                    arguments = (
                        argument_lists.get(node.left, (left,))
                        if isinstance(node.left, ast.BinOp)
                        and isinstance(node.left.op, (ast.Mult, ast.Div))
                        else (left,)
                    )
                    arguments += (
                        argument_lists.get(node.right, (right,))
                        if isinstance(node.right, ast.BinOp)
                        and isinstance(node.right.op, (ast.Mult, ast.Div))
                        else (right,)
                    )
                    argument_lists[node] = arguments
                    value = Mul(*arguments, evaluate=False)
                elif operation is ast.Div:
                    if validate is not None:
                        validate(node, values, env)
                    arguments = (
                        argument_lists.get(node.left, (left,))
                        if isinstance(node.left, ast.BinOp)
                        and isinstance(node.left.op, (ast.Mult, ast.Div))
                        else (left,)
                    )
                    arguments += (Pow(right, -1, evaluate=False),)
                    argument_lists[node] = arguments
                    value = Mul(*arguments, evaluate=False)
                else:
                    exponent_names = {
                        child.id for child in ast.walk(node.right) if isinstance(child, ast.Name)
                    }
                    if exponent_names and self.overload_sympyeval is not None:
                        right = self._integer_expression(node.right, env)
                    if right.is_number and not right.is_Integer:
                        right = right.doit()
                    if not right.is_Integer:
                        raise TypeError("Finite-field operations support only integer exponents")
                    if validate is not None:
                        validate(node, values, env, right)
                    value = Pow(left, right, evaluate=False)
            values[node] = value
        return values[tree.body]

    def _literal_constant(self, text):

        text = text.strip()
        if not re.fullmatch(r"[+-]?\d+|True|False", text):
            return None
        number = int(text) if text not in ("True", "False") else int(text == "True")
        if self.logic:
            if number not in (0, 1):
                raise ValueError("Bool mode supports only constants 0 and 1")
            return S.true if number else S.false
        return self.overload_sympyeval.evaluate(Integer(number))

    def _build_probing(self):

        robust = self.robust
        options = self.gadget.checkOptions["robust"]
        hw = "hw_sumed" in options or "hw_vector" in options

        output_names = set(map(str, self.sharesOut))
        output_rows = {}
        source_locations = {}
        encoding_rows = {}
        for instruction in self.instructions:
            lhs = instruction.lhs
            source_locations[str(instruction.source_line)] = (instruction.source_line, lhs)
            if instruction.stage == "encoding":
                encoding_rows[lhs] = instruction.source_line
            if lhs in output_names:
                output_rows[lhs] = instruction.source_line
        missing_outputs = output_names - set(output_rows)
        if missing_outputs:
            raise ValueError("Unassigned output shares: " + ", ".join(sorted(missing_outputs)))
        circuit_inputs = (
            list(self.sharesIn) + list(self.randoms - self.encoding_randoms)
            if (self.model_str == "probing_secret")
            else list(self.sharesIn) + list(self.randoms)
        )
        circuit_randoms = (
            list(self.randoms - self.encoding_randoms)
            if (self.model_str == "probing_secret")
            else list(self.randoms)
        )
        circuit_outputs = list(self.sharesOut)

        initial_values = circuit_randoms + (
            list(self.sharesIn)
            if self.model_str in ("ni", "sni", "pini", "probing_share")
            else []
        )

        encoding_values = (
            list(self.randoms & self.encoding_randoms) if self.model_str == "probing_secret" else []
        )
        source_names = set(map(str, circuit_randoms))
        input_locations = {str(value): str(value) for value in circuit_inputs}
        occupied_names = (
            set(input_locations)
            | output_names
            | {line.split("=", 1)[0].strip() for line in self.gadget.expressions}
        )
        for name in set(input_locations) & output_names:
            if output_rows[name] not in self.encoding_shares:

                location = "__input_" + name
                while location in occupied_names:
                    location = "_" + location
                occupied_names.add(location)
                input_locations[name] = location
        circuit_inputs = [symbols(input_locations[str(value)]) for value in circuit_inputs]
        independent_inputs = self.model_str in ("ni", "sni", "pini", "probing_share")
        allowed_inputs = set(self.sharesIn) | set(self.randoms)
        raw_secrets = set(self.secrets) - allowed_inputs
        raw_secret_pattern = (
            re.compile(
                r"(?<!\w)(?:" + "|".join(map(re.escape, map(str, raw_secrets))) + r")(?!\w)"
            )
            if raw_secrets
            else None
        )

        def validate_inputs(expression, text, row, env):
            if not independent_inputs:
                return
            unknown = set(map(str, sympify(expression).free_symbols - allowed_inputs))
            if raw_secret_pattern:
                unknown.update(
                    name for name in raw_secret_pattern.findall(text) if name not in env
                )
            if unknown:
                raise ValueError(
                    f"{self.model_str}, line {row}: undeclared independent inputs: {', '.join(sorted(unknown))}; "
                    "use declared inputs/randoms or assigned intermediate variables; secrets are allowed only in := encoding"
                )

        env, channels, protected = {}, {}, {}
        leakage, previous_history, last_old_stable = {}, {}, {}
        source_reads = set()
        local_transition = robust in (9, 10)
        for value in encoding_values + initial_values:
            name = str(value)
            env[name] = value
            channels[name] = (value,)
            protected[name] = False
            previous_history[name] = (value,)
        for value in initial_values:
            leakage[input_locations.get(str(value), str(value))] = [(value,)]

        event = getattr(self.gadget, "event", None)
        iterator = self.instructions
        if event:
            iterator = event("iterate", {"items": iterator, "total": len(iterator)})
        for instruction in iterator:
            lhs, rhs, row = instruction.lhs, instruction.rhs, instruction.source_line
            if instruction.stage == "encoding":
                constant = self._literal_constant(rhs) if self.model_str == "probing_secret" else None
                value = (
                    (constant if constant is not None else self._evaluate(rhs, env))
                    if self.model_str == "probing_secret"
                    else symbols(lhs)
                )
                env[lhs] = value
                channels[lhs] = (value,)
                protected[lhs] = True
                previous_history[lhs] = (value,)
                last_old_stable.pop(lhs, None)
                location = input_locations.get(lhs, lhs)
                if symbols(lhs) in self.sharesIn and constant is None:
                    leakage[location] = [(value,)]
                else:
                    leakage.pop(location, None)
                continue
            if lhs == "reg":
                if rhs not in env:
                    raise ValueError(f"Line {row}: reg references undefined variable {rhs}")
                protected[rhs] = True
                if local_transition:
                    channels[rhs] = (env[rhs],) + (
                        last_old_stable.get(rhs, ()) if robust == 10 else ()
                    )
                continue
            if robust != 9 and row == output_rows.get(lhs):
                row = lhs
            manual = tuple(self._evaluate(text, env) for text in instruction.extensions)
            for expression, text in zip(manual, instruction.extensions):
                validate_inputs(expression, text, row, env)
                source_reads.update(map(str, self.gadget.expression_info[text][1]))
            constant = self._literal_constant(rhs)
            if constant is not None and not manual and not local_transition and robust not in (2, 3, 4):
                if lhs in source_names and lhs not in source_reads:
                    leakage.pop(input_locations.get(lhs, lhs), None)
                env[lhs] = constant
                protected[lhs] = True
                channels[lhs] = (constant,)
                previous_history[lhs] = (constant,)
                continue
            value = constant if constant is not None else self._evaluate(rhs, env)
            validate_inputs(value, rhs, row, env)
            operands = (
                instruction.operand_names
                if local_transition
                else tuple(map(str, instruction.dependencies))
            )
            source_reads.update(operands)
            operand_channels = []
            for name in operands:
                if name in env:
                    operand_channels.append(
                        channels[name]
                        if local_transition or not protected[name]
                        else (env[name],)
                    )
                elif not independent_inputs and (
                    symbols(name) in self.secrets or symbols(name) in self.encoding_randoms
                ):
                    operand_channels.append((symbols(name),))
                else:
                    raise ValueError(f"Line {row}: undefined variable {name}")
            old = (env[lhs],) if lhs in env else ()
            if local_transition:
                current = (
                    (value,)
                    if not operand_channels or (robust == 10 and instruction.barrier)
                    else tuple(dict.fromkeys(atom for channel in operand_channels for atom in channel))
                )
                if robust == 10:
                    history = current + old
                    channels[lhs] = history
                    last_old_stable[lhs] = old
                else:
                    history = tuple(dict.fromkeys(old + current))
                    channels[lhs] = (value,) if instruction.barrier else current
                env[lhs] = value
                if any(sympify(atom).free_symbols for atom in history):
                    leakage.setdefault(row, []).append(history)
                continue
            if lhs in source_names and lhs not in source_reads and robust not in (2, 3, 4):
                leakage.pop(input_locations.get(lhs, lhs), None)
            elif (
                lhs in source_names
                and input_locations.get(lhs, lhs) in leakage
                and robust in (2, 3, 4)
            ):
                source_reads.add(lhs)
            env[lhs] = value
            protected[lhs] = instruction.barrier
            channels[lhs] = (
                (value,)
                if instruction.barrier
                else tuple(atom for channel in operand_channels for atom in channel)
            )
            current = (channels[lhs] if robust in (1, 3, 33) else (value,)) + manual
            history = current
            if "transitionxor" not in self.gadget.checkOptions["robust"]:
                history = tuple(
                    atom
                    for atom in history
                    if atom is not True
                    and atom is not False
                    and not (not self.logic and isinstance(atom, Integer))
                )
            if robust in (2, 3, 4):
                history = previous_history.get(lhs, ()) + history
            previous_history[lhs] = current
            if any(sympify(atom).free_symbols for atom in history):
                leakage.setdefault(row, []).append(history)

        if robust == 9:
            for name, row in output_rows.items():
                endpoint = channels[name]
                if any(sympify(atom).free_symbols for atom in endpoint):
                    leakage[name] = [endpoint]
                if row in leakage and frozenset(leakage[row][-1]) == frozenset(endpoint):
                    leakage.pop(row)

        circuit_inputs = [value for value in circuit_inputs if str(value) in leakage]

        leakage_out_set = set(map(str, circuit_outputs)) & set(leakage)
        leakage_inside = set(leakage) - leakage_out_set - set(map(str, circuit_inputs))

        leakage_in = symbols(sorted(leakage_inside, key=int))

        leakage_in += circuit_inputs
        leakage_out = symbols(sorted(leakage_out_set))

        leakage = {symbols(name): list(history[-1]) for name, history in leakage.items()}
        input_symbols = set(circuit_inputs)
        sharesIn_notrans = (
            {symbol: values for symbol, values in leakage.items() if symbol in input_symbols}
            if self.robust in (22, 33)
            else {}
        )

        checksize = -1
        observationsCheck = []

        def transition_units(probes, include_singletons=False):
            return TransitionPositions(
                tuple(probe for probe in probes if probe not in sharesIn_notrans),
                tuple(sharesIn_notrans),
                include_singletons,
            )

        if self.model_str in ("ni", "sni", "pini"):
            if self.model_str == "pini":

                by_index = {}
                for output in leakage_out:
                    index = self.mapping[self.sharesOut[output]][2]
                    by_index.setdefault(index, []).append(output)
                probes = list(leakage_in) + [
                    tuple(by_index[index]) for index in sorted(by_index)
                ]
            else:
                probes = list(leakage_out) + list(leakage_in)
            if self.robust in (22, 33):

                units = transition_units(probes, include_singletons=True)
                orders = range(1, min(self.threshold, len(units)) + 1)
                observationsCheck = ObservationPlan(units, orders)
                checksize = sum(comb(len(units), order) for order in orders)
            else:
                orders = range(1, min(self.threshold, len(probes)) + 1)
                observationsCheck = ObservationPlan(probes, orders)
                checksize = sum(comb(len(probes), order) for order in orders)
        elif self.robust == 22 or self.robust == 33:
            units = transition_units(
                list(leakage_out) + list(leakage_in),
                include_singletons=hw or "transitionxor" in options,
            )
            maximum = min(self.threshold, len(units))

            orders = (
                range(1, maximum + 1)
                if hw
                else (maximum,) if maximum else ()
            )
            observationsCheck = ObservationPlan(units, orders)
            checksize = sum(comb(len(units), order) for order in orders)

        else:
            probes = list(leakage_out) + list(leakage_in)
            maximum = min(self.threshold, len(probes))
            orders = (
                range(1, maximum + 1)
                if hw
                else (maximum,) if maximum else ()
            )
            observationsCheck = ObservationPlan(probes, orders)
            checksize = sum(comb(len(probes), order) for order in orders)

        if not observationsCheck:

            warn("NO leakage?")
        self.gadget.mapRow2Obs = leakage
        locations = {
            location: (encoding_rows.get(name), name)
            for name, location in input_locations.items()
        }
        locations.update(source_locations)
        locations.update({name: (row, name) for name, row in output_rows.items()})
        self.gadget.probe_locations = {probe: locations[str(probe)] for probe in leakage}
        self.gadget.observationsIn = leakage_in
        self.gadget.observationsOutput = leakage_out
        self.gadget.observationsCheck = observationsCheck
        self.gadget.checksize = checksize
        return True

    def _build_random(self):

        from collections import Counter

        if self.model_str not in ("rps_secret", "rps_share", "rpc", "rpe"):
            raise ValueError("Unknown random probing security property")
        if (
            self.model_str not in ("rps_secret", "rps_share")
            and not 0 <= self.threshold < self.gadget.shareNum
        ):
            raise ValueError("RPC/RPE threshold must lie between 0 and shares-1")

        output_names = set(map(str, self.sharesOut))
        assigned_outputs = set()
        for line in self.gadget.expressions:
            lhs = line.split("=", 1)[0].strip()
            if lhs in output_names:
                assigned_outputs.add(lhs)
        if output_names - assigned_outputs:
            raise ValueError(
                "Unassigned output shares: "
                + ", ".join(sorted(output_names - assigned_outputs))
            )

        env = {}
        producers = {}
        nodes = []

        def assign(name, value, computed=True, source_line=None):
            env[name] = value
            producers[name] = len(nodes)
            nodes.append([value, 0, False, computed, (source_line, name)])

        initial = list(self.secrets) if self.model_str == "rps_secret" else list(self.sharesIn)
        allowed_symbols = set(initial) | self.randoms
        for symbol in initial + sorted(self.randoms, key=str):
            assign(str(symbol), symbol, computed=False)

        encoded = set()
        event = getattr(self.gadget, "event", None)
        iterator = self.instructions
        if event:
            iterator = event("iterate", {"items": iterator, "total": len(iterator)})
        for instruction in iterator:
            lhs, rhs = instruction.lhs, instruction.rhs
            row = instruction.source_line
            if lhs == "reg":
                if rhs not in env:
                    raise ValueError(
                        f"Random probing, line {row}: reg references undefined variable {rhs}"
                    )
                continue
            is_encoding = row in self.encoding_shares
            if is_encoding and self.model_str != "rps_secret":
                if lhs in producers:
                    nodes[producers[lhs]][4] = (row, lhs)
                continue
            tree, _, names, syntax, _ = self.gadget.expression_info[rhs]
            exponent_nodes = {
                child
                for node in syntax
                if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow)
                for child in ast.walk(node.right)
            }
            operands = [
                node.id for node in syntax
                if isinstance(node, ast.Name) and node not in exponent_nodes
            ]
            unknown = set(names) - env.keys()
            if unknown:
                raise ValueError(
                    f"{self.model_str}, line {row}: undefined inputs: {', '.join(sorted(unknown))}"
                )
            values = {}
            value = self._evaluate(rhs, env, values)
            if not self.logic:
                value = self.overload_sympyeval.evaluate(value)
            if sympify(value).free_symbols - allowed_symbols:
                raise ValueError(f"{self.model_str}, line {row}: undeclared input symbols")
            if is_encoding:
                assign(lhs, value, computed=False, source_line=row)
                encoded.add(lhs)
                continue
            for name in operands:
                nodes[producers[name]][1] += 1

            for node in instruction.syntax:
                if (
                    node is not tree.body
                    and node not in exponent_nodes
                    and isinstance(node, (ast.BinOp, ast.UnaryOp))
                ):
                    inner_value = values[node]
                    if not self.logic:
                        inner_value = self.overload_sympyeval.evaluate(inner_value)
                    nodes.append([inner_value, 1, False, True, (row, lhs)])
            assign(lhs, value, source_line=row)
        if self.model_str == "rps_secret":
            missing = set(map(str, self.sharesIn)) - encoded
            if missing:
                raise ValueError(
                    "rps_secret requires := encoding for input shares: " + ", ".join(sorted(missing))
                )
        leakage_out = {symbol: env[str(symbol)] for symbol in self.sharesOut}
        for name in output_names:
            nodes[producers[name]][2] = True

        wires = []
        wire_locations = []

        for value, uses, is_output, computed, location in nodes:
            if not sympify(value).free_symbols:
                continue
            if uses == 0:
                if not computed or is_output:
                    continue

                wires.append(value)
                wire_locations.append(location)
                continue

            multiplicity = 2 * (uses + int(is_output)) - 1 - int(is_output)
            wires.extend([value] * multiplicity)
            wire_locations.extend([location] * multiplicity)

        len_wires = len(wires)
        cmax = min(self.cmax, len_wires)
        self.cmax = cmax
        self.gadget.checkOptions["cmax"] = cmax
        checksize_rp = [comb(len_wires, c) for c in range(len_wires + 1)]
        positions = tuple(wires)
        observationsCheck = [
            ObservationPlan(positions, (c,)) if c <= cmax else checksize_rp[c]
            for c in range(len_wires + 1)
        ]

        outputs = list(self.sharesOut)
        group_width = self.gadget.shareNum * self.bits
        if len(outputs) % group_width:
            raise ValueError("Declared output shares do not match shares/bits")
        output_groups = [
            outputs[i : i + group_width] for i in range(0, len(outputs), group_width)
        ]

        if self.model_str in ("rps_secret", "rps_share"):
            observationsCheck[0] = {self.model_str: []}
        elif self.model_str == "rpc":
            output_blocks = tuple(
                tuple(outputs[i : i + self.bits]) for i in range(0, len(outputs), self.bits)
            )
            observationsCheck[0] = {
                "rpc": ObservationPlan(output_blocks, (self.threshold,), flatten=True)
            }
        else:
            low = ObservationPlan(range(self.gadget.shareNum), (self.threshold,))
            high = ObservationPlan(range(self.gadget.shareNum), (self.gadget.shareNum - 1,))
            observationsCheck[0] = {
                "rpe1": OutputChoices(output_groups, self.bits, (low,) * len(output_groups)),
                "rpe2": OutputChoices(output_groups, self.bits, (high,) * len(output_groups)),
                "rpe_requests": OutputRequests(
                    output_groups, self.bits, self.gadget.shareNum, self.threshold
                ),
            }
        self.gadget.mapRow2Obs = dict(Counter(wires)) | leakage_out
        self.gadget.observationsIn = wires
        self.gadget.random_wire_channels = None
        self.gadget.random_wire_locations = tuple(wire_locations)
        self.gadget.probe_locations = {
            symbol: nodes[producers[str(symbol)]][4] for symbol in leakage_out
        }
        self.gadget.random_channel_metadata = {
            "sampling": "independent_physical_locations",
            "robust": (),
            "requested_outputs": "stable_joint_values",
            "copy_tree": "binary_without_external_output_edges",
        }
        self.gadget.observationsOutput = leakage_out
        self.gadget.observationsCheck = observationsCheck
        self.gadget.checksize = len_wires + 1
        self.gadget.checksize_rp = checksize_rp
        return True

    def analyze(self):
        if self.model_str in ("rps_secret", "rps_share", "rpc", "rpe"):
            if self.cmax is None or self.cmax < 0:
                warn("cmax was not specified; using cmax=4")
                self.cmax = 4
                self.gadget.checkOptions["cmax"] = 4
            self._build_random()
        else:
            self._build_probing()
        return self.gadget
