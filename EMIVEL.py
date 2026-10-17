from argparse import ArgumentParser
from builtins import print as builtin_print
from contextlib import ExitStack
from datetime import datetime
from decimal import Decimal
from fractions import Fraction
from functools import wraps
from pathlib import Path
from timeit import default_timer
from warnings import warn
import hashlib
import json

from alive_progress import alive_bar, alive_it
from rich.console import Console
from sympy import Add, Integer, Rational, Symbol, series

import GadgetsAnalysis
import Parameters
from GadgetsChecker import Verifier

console = Console()


def ET(func):

    @wraps(func)
    def ExecutionTime(*args, **kwargs):
        import psutil
        from threading import Event, Thread

        process = psutil.Process()
        stopped = Event()
        peak_rss = 0

        def sample_memory():
            nonlocal peak_rss
            try:
                children = process.children(recursive=True)
            except psutil.Error:
                children = []
            total = 0
            for child in [process] + children:
                try:
                    total += child.memory_info().rss
                except psutil.Error:
                    pass
            peak_rss = max(peak_rss, total)

        def monitor_memory():
            while not stopped.wait(0.1):
                sample_memory()

        sample_memory()
        monitor = Thread(target=monitor_memory, name="maskingChecker-memory", daemon=True)
        monitor.start()
        sTime = default_timer()
        try:
            result = func(*args, **kwargs)
        finally:
            eTime = default_timer()
            stopped.set()
            monitor.join()
            sample_memory()
        end = eTime - sTime
        minute, second = divmod(end, 60)
        hour, minute = divmod(minute, 60)
        builtin_print(
            "%s took %fh %f m %fs; peak memory = %.2f MiB; %s"
            % (
                func.__name__,
                hour,
                minute,
                second,
                peak_rss / (1024**2),
                datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            )
        )
        return result

    return ExecutionTime


def print_parameters(circuit):
    builtin_print("Name = %s".rjust(50, "-") % circuit.name)
    builtin_print("Gates = %s".rjust(50, "-") % circuit.mapGates)
    builtin_print("Secrets = %s".rjust(50, "-") % str(circuit.secrets))
    builtin_print("Secrets (bits) = %s".rjust(50, "-") % str(circuit.secretsBits))
    builtin_print("outputs = %s".rjust(50, "-") % str(circuit.outputs))
    builtin_print("outputs (bits) = %s".rjust(50, "-") % str(circuit.outputsBits))
    builtin_print("Shares's number = %s".rjust(50, "-") % str(circuit.shareNum))
    if circuit.checkOptions["security"] in ("rps_share", "probing_share"):
        builtin_print(
            "Simulator shares per input (n-1) = %s".rjust(50, "-") % (circuit.shareNum - 1)
        )
    builtin_print("Shares's index = %s".rjust(50, "-") % str(circuit.shareIndex))
    builtin_print("Inputs = %s".rjust(50, "-") % str(circuit.secretsInputs))
    builtin_print("Inputs (bits) = %s".rjust(50, "-") % str(circuit.secretsInputsBits))
    builtin_print("Outputs = %s".rjust(50, "-") % str(circuit.secretsOutputs))
    builtin_print("Outputs (bits) = %s".rjust(50, "-") % str(circuit.secretsOutputsBits))
    builtin_print("Randoms = %s".rjust(50, "-") % str(circuit.randoms))
    from galois import GF

    if circuit.field == "bool":
        builtin_print("Field = %s".rjust(50, "-") % circuit.field)
    else:
        builtin_print("Field = %s".rjust(50, "-") % GF(circuit.field))
    if len(circuit.mapRow2Obs) < 20:
        builtin_print("All Probes = %s".rjust(50, "-") % circuit.mapRow2Obs)
    builtin_print(
        "Total checking observations set number= \x1b[1;33m %s \x1b[0m".rjust(62, "-")
        % circuit.checksize
    )
    if circuit.checkOptions["cmax"] != None:
        cmax = (
            circuit.checkOptions["cmax"]
            if circuit.checkOptions["cmax"] < circuit.checksize // 2
            else circuit.checksize // 2
        )
        builtin_print(
            "Max checking observations number (random probing model)= \x1b[1;33m %s \x1b[0m".rjust(
                62, "-"
            )
            % circuit.checksize_rp[cmax]
        )
    builtin_print("Total Internal Probes = %s".rjust(50, "-") % len(circuit.observationsIn))
    builtin_print("Total Output Probes = %s".rjust(50, "-") % len(circuit.observationsOutput))
    builtin_print("Total Regs (protected gates) = %s".rjust(50, "-") % len(circuit.reg))
    builtin_print("Check options = %s".rjust(50, "-") % circuit.checkOptions)


def report_results(verifier, result):
    circuit = verifier.gadget
    options = circuit.checkOptions
    finished_at = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    model = "+".join(options["robust"]) or "Standard"
    field = "bool" if circuit.field == "bool" else f"GF({circuit.field})"
    footer = (
        f"--- gadget: {circuit.name}, security: {options['security']}, "
        f"model: {model}, field: {field} Finished on {finished_at}"
    )

    if not verifier.randomprobing:
        processed, total = result["processed_count"], result["checksize"]
        if result["complete"]:
            console.print(
                f"Check complete: {processed}/{total} observations processed 📌", markup=False
            )
            if verifier.tech == 1:
                verdict = (
                    "insecure"
                    if result["counts"]["unknown"] or result["counts"]["insecure"]
                    else "secure"
                )
                console.print(f"⚠️ {verdict} (false positives possible)", markup=False)
            elif result["counts"]["insecure"]:
                console.print("💔 insecure", markup=False)
            elif result["counts"]["unknown"]:
                console.print("⚠️ unresolved", markup=False)
            else:
                console.print("💚 secure", markup=False)
        else:
            console.print(
                f"⚠️ incomplete: {processed}/{total} observations processed", markup=False
            )
            if result.get("stop_reason"):
                console.print(result["stop_reason"], markup=False)
            if verifier.tech == 1 and (
                result["counts"]["unknown"] or result["counts"]["insecure"]
            ):
                console.print("⚠️ insecure (false positives possible)", markup=False)
            elif result["counts"]["insecure"]:
                console.print("💔 insecure", markup=False)

    with ExitStack() as files:
        text_file = None
        if verifier.toFile:
            Path("checkResult").mkdir(parents=True, exist_ok=True)
            text_file = files.enter_context(
                open(Path("checkResult") / (circuit.name + ".txt"), "a", encoding="utf-8")
            )

        def emit(line, *, display=True):
            if display:
                console.print(line, markup=False, highlight=True, soft_wrap=True)
            if text_file is not None:
                text_file.write(line + "\n")

        preview = {}
        if not verifier.randomprobing:
            largest, tied_count, unknown_count = None, 0, 0
            unknown_preview = {}
            for rows, value in circuit.row_mi.items():
                if circuit.row_verdict.get(rows, "unknown") == "unknown":
                    unknown_count += 1
                    if len(unknown_preview) < 5:
                        unknown_preview[rows] = value
                    continue
                magnitude = Decimal(str(circuit.row_mi_text.get(rows) or value))
                if largest is None or magnitude > largest:
                    largest, tied_count = magnitude, 1
                    preview = {rows: value}
                elif magnitude == largest:
                    tied_count += 1
                    if len(preview) < 5:
                        preview[rows] = value
            if largest is None:
                preview, tied_count = unknown_preview, unknown_count
            if tied_count > 5:
                amount = (
                    str(largest)
                    if largest is not None
                    else (
                        "not computed (static verification unresolved)"
                        if verifier.tech == 1
                        else "undetermined"
                    )
                )
                console.print(f"MI/CMI (value, count) = ({amount}, {tied_count})", markup=False)
                preview.clear()
        else:

            summary = verifier.random_summary
            components = summary["components"]
            basis = "p**i" if summary["basis"] == "power" else "p**i*(1-p)**(N-i)"
            emit(f"F coefficients (c_0, ..., c_N); basis = {basis}")
            for index, branch in enumerate(components, 1):
                if branch["active"]:
                    label = branch.get("label")
                    emit(
                        f"F[{index}] (k={branch['root_degree']}, {label}) = {list(branch['upper_coefficients'])}"
                    )

            local = summary["series_component"]
            coefficients, degree = local["series_coefficients"], local["root_degree"]
            order = options["cmax"] + 1
            if degree == 1:
                head = verifier._polynomial_text(coefficients[:order])
                expansion = ("" if head == "0" else head + " + ") + f"O(p**{order})"
            else:
                first = next((i for i, value in enumerate(coefficients) if value), None)
                if first is None or Fraction(first, degree) >= order:
                    expansion = f"O(p**{order})"
                else:
                    p = Symbol("p", positive=True)
                    head = Add(
                        *(
                            Integer(coefficients[i]) * p ** (i - first)
                            for i in range(first, min(first + order, len(coefficients)))
                        )
                    )
                    expansion = str(
                        series(
                            p ** Rational(first, degree) * head ** Rational(1, degree),
                            p,
                            0,
                            order,
                        )
                    )
            emit(f"f(p)_{options['cmax']} = {expansion}")

            emit("F threshold bounds:")
            thresholds = list(enumerate(components, 1)) if len(components) > 1 else []
            thresholds.append((None, summary))
            for index, bound in thresholds:
                values = []
                for name in ("min", "max"):
                    value = bound[f"log2_p_{name}"]
                    values.append(
                        f"log2(p_{name}) = {value}"
                        if value is not None
                        else f"log2(p_{name}) = unavailable (no positive p_{name} found)"
                    )
                prefix = "" if index is None else f"F[{index}] ({bound.get('label')}): "
                emit(prefix + "; ".join(values))
            if result.get("stop_reason"):
                emit("Stopped: " + result["stop_reason"])

        records = circuit.row_mi if text_file is not None else preview
        for rows, value in records.items():
            status = circuit.row_verdict.get(rows, "unknown")
            if status == "unknown":
                amount = (
                    "not computed (static verification unresolved)"
                    if verifier.tech == 1
                    else "undetermined"
                )
            else:
                amount = str(circuit.row_mi_text.get(rows) or value)
            emit(f"MI/CMI = {amount}: {rows}", display=rows in preview)

        if text_file is not None:
            text_file.write(footer + "\n")

    if verifier.toFile:
        report = dict(result)
        report.update(schema_version=3, gadget=circuit.name, finished_at=finished_at)
        if verifier.randomprobing:
            report["random_summary"] = verifier.random_summary
            report["observations"] = [
                {
                    "row": str(rows),
                    "mi": value,
                    "mi_text": circuit.row_mi_text.get(rows),
                    "status": circuit.row_verdict.get(rows, "unknown"),
                    "exact_zero": (
                        False if circuit.row_verdict.get(rows) == "insecure" else None
                    ),
                }
                for rows, value in circuit.row_mi.items()
            ]
        else:
            report["parameters"] = {
                "model": options["security"],
                "threshold": options.get("threshold"),
                "technique": options.get("tech."),
                "robust": options.get("robust", []),
                "field": circuit.field,
                "bits": circuit.bits,
                "workers": options.get("mcore", 0),
            }
        report["check_options"] = dict(options)
        source_dir = Path(__file__).resolve().parent
        report["source_sha256"] = {
            name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
            for name in (
                "EMIVEL.py",
                "GadgetsChecker.py",
                "GadgetsAnalysis.py",
                "MIA.py",
                "auxiliary.py",
                "Parameters.py",
            )
        }
        input_path = Path(options.get("path") or "")
        report["gadget_sha256"] = (
            hashlib.sha256(input_path.read_bytes()).hexdigest()
            if input_path.is_file()
            else None
        )
        suffix = ".random.jsonl" if verifier.randomprobing else ".verification.jsonl"
        with open(Path("checkResult") / (circuit.name + suffix), "a", encoding="utf-8") as file:
            file.write(json.dumps(report, ensure_ascii=False, default=str) + "\n")
        console.print(f"result saved. total leakage ({len(circuit.row_mi)})", markup=False)
    console.print(footer, markup=False, soft_wrap=True)


def parseArgs():

    parser = ArgumentParser(description="Analyze and verify masked circuits.")

    parser.add_argument(
        "-p",
        "--path",
        metavar="/gadgets/...",
        required=True,
        help="The path of the gadget file.",
    )
    parser.add_argument(
        "-m",
        "--model",
        metavar="PROPERTY",
        required=True,
        nargs=1,
        type=str.lower,
        choices=[
            "ni",
            "sni",
            "pini",
            "probing_secret",
            "probing_share",
            "rpc",
            "rpe",
            "rps_secret",
            "rps_share",
        ],
        help="Security property: probing_secret/probing_share, ni, sni, pini, rps_secret/rps_share, rpc, or rpe.",
    )
    parser.add_argument(
        "-t",
        "--threshold",
        metavar="1, 2, ...",
        required=True,
        type=int,
        help="The probing-threshold of the probing attack model.",
    )

    parser.add_argument(
        "-cv",
        "--correctness",
        metavar="AND, ADD,COPY,AES8,keccak5,midori4,present4,prince4",
        choices=[
            "AND",
            "ADD",
            "COPY",
            "AES8",
            "keccak5",
            "midori4",
            "present4",
            "prince4",
            "user",
        ],
        default="null",
        help="Functional Correctness Verification for Gate-Level Circuits and Cryptographic S-Boxes.",
    )

    parser.add_argument(
        "-r",
        "--robust",
        metavar="glitch, transition, ...",
        nargs="+",
        choices=GadgetsAnalysis.LeakageAnalyzer.LEAKAGE_OPTIONS,
        default=[],
        help="Leakage options, including hw_sumed or hw_vector; HW is applied after transition XOR.",
    )

    parser.add_argument(
        "-c",
        "--coefficient",
        metavar="1, 2, ...",
        help="The max coefficient of the random probing attack model.",
        type=int,
    )

    parser.add_argument(
        "--tech",
        metavar="MI or static or both",
        nargs=1,
        choices=["mi", "static", "both"],
        default=["both"],
        help="If need to compute MI only without static type checking.",
    )
    parser.add_argument(
        "--abort",
        metavar="t or f",
        nargs=1,
        choices=["t", "f"],
        default="f",
        help="If need to stop when finding an insecure observation.",
    )
    parser.add_argument(
        "--detail",
        metavar="t or f",
        nargs=1,
        choices=["t", "f"],
        default="f",
        help="Print live insecure/unresolved observations with source locations and MI/CMI when available.",
    )
    parser.add_argument(
        "--watch",
        metavar="ROW_OR_LHS",
        nargs="+",
        default=[],
        help="Also print observations containing these source line numbers or assignment variables, including secure ones. Works without --detail t.",
    )
    parser.add_argument(
        "--tofile",
        metavar="t or f",
        nargs=1,
        choices=["t", "f"],
        default="t",
        help="If need to write insecure observation and its MI to file.",
    )
    parser.add_argument(
        "--mcore",
        metavar="0, 1, 2, ...",
        type=int,
        default=0,
        help="Worker processes; 0 runs sequentially.",
    )
    parser.add_argument(
        "--maxhours",
        metavar="1, 2, ...",
        type=int,
        default=12,
        help="Verification time limit in hours.",
    )
    parser.add_argument(
        "--maxmem",
        metavar="1, 2, ...",
        type=int,
        default=5,
        help="Per-process memory limit in GiB.",
    )

    args = parser.parse_args()
    if any(value < 0 for value in (args.threshold, args.mcore, args.maxhours, args.maxmem)):
        parser.error("threshold, mcore, maxhours, and maxmem must be nonnegative")
    try:
        GadgetsAnalysis.LeakageAnalyzer.validate_options(args.robust, model=args.model[0])
    except (ValueError, NotImplementedError) as exc:
        parser.error(str(exc))
    if args.coefficient is not None and args.model[0] not in ("rps_secret", "rps_share", "rpc", "rpe"):
        parser.error("-c/--coefficient is only available for random probing models")
    return args


@ET
def maskingChecker():

    gadget = Parameters.CircuitIR(
        name="",
        expressions=[],
        reference=[],
        mapGates={"&": 0, "^": 0, "~": 0, "+": 0, "*": 0, "-": 0},
        mapRow2exp={},
        mapRow2Obs={},
        encodingRow=[],
        decodingRow=[],
        secrets=(),
        secretsBits=(),
        outputs=(),
        outputsBits=(),
        secretsInputs=(),
        secretsInputsBits=(),
        secretsOutputs=(),
        secretsOutputsBits=(),
        invertible=(),
        shareNum=0,
        shareIndex=(),
        randoms=(),
        bits=1,
        field="bool",
        logic=True,
        observationsIn=[],
        observationsOutput={},
        observationsCheck=[],
        checksize=0,
        checksize_rp=[],
        reg={},
        row_mi={},
        checkOptions={
            "path": "",
            "correctness": "",
            "security": "",
            "robust": [],
            "cmax": -1,
            "tech.": "",
            "abort": "",
            "detail": "",
            "toFile": "",
            "mcore": 0,
            "maxhours": 12,
            "maxmem": 5,
            "threshold": -1,
        },
    )

    stack = ExitStack()
    progress = None

    def event(name, payload):
        nonlocal progress
        if name == "progress_start":
            stack.close()
            progress = stack.enter_context(alive_bar(payload["total"]))
        elif name == "progress":
            if progress is not None:
                progress(payload.get("advance", 1))
        elif name == "progress_end":
            stack.close()
            progress = None
        elif name == "detail":
            locations = ", ".join(
                f"{row if row is not None else 'declaration'}:{lhs}"
                for row, lhs in payload["locations"]
            )
            status = payload["status"]
            label = {
                "safe": "secure",
                "insecure": "insecure",
                "unknown": "unresolved (not proved secure)",
            }[status]
            icon = (
                "⚠"
                if args.tech[0] == "static" or status == "unknown"
                else "💚" if status == "safe" else "💔"
            )
            text = f"{icon} ({locations}) {label}"
            if payload["request"] is not None:
                text += f"; request={payload['request']}"
            if payload["mi"] is not None:
                value = payload["mi_text"] or payload["mi"]
                text += f"; {payload['quantity']}={value}"
            console.print(text, markup=False)
        elif name == "iterate":
            return alive_it(payload["items"], total=payload["total"])
        elif name == "warning":
            warn(payload["message"])
        elif name in ("message", "stop"):
            console.print(payload["message"], markup=False)

    gadget.event = event
    args = parseArgs()
    console.print("Analyzing...")
    gadget.checkOptions = {
        "path": args.path,
        "correctness": args.correctness,
        "security": args.model[0],
        "robust": args.robust,
        "cmax": args.coefficient,
        "tech.": args.tech[0],
        "abort": args.abort[0],
        "detail": args.detail[0],
        "watch": args.watch,
        "toFile": args.tofile[0],
        "mcore": args.mcore,
        "maxhours": args.maxhours,
        "maxmem": args.maxmem,
        "threshold": args.threshold,
    }
    GadgetsAnalysis.CircuitParser(gadget).parse()
    GadgetsAnalysis.CorrectnessVerifier(gadget).check()
    GadgetsAnalysis.LeakageAnalyzer(gadget).analyze()
    print_parameters(gadget)
    verifier = Verifier(gadget, event=event)
    console.print("Initializing...")
    verifier.initialize()
    console.print("Checking...")
    try:
        result = verifier.run()
    finally:
        stack.close()
    report_results(verifier, result)
    return True


if __name__ == "__main__":
    maskingChecker()
