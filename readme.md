# EMIVEL

EMIVEL checks the functional correctness and security of masked gadgets and circuits described in text files. It combines symbolic static verification with MI/CMI computation.

## Features

| Area | Support |
| --- | --- |
| Fields | Boolean operations, prime fields GF(p), and binary extension fields GF(2^n). |
| Security properties | `probing_secret`, `probing_share`, `ni`, `sni`, `pini`; random probing: `rps_secret`, `rps_share`, `rpc`, `rpe`. |
| Leakage models | Standard, Transition, XOR-Transition, HW-XOR-Transition, Glitch, HW-Glitch, and combined Transition + Glitch. |
| Transition options | `transition` follows successive assignments to the same variable; `transitionall` considers pairs of circuit locations. Native TG variants: `maskverifTG` and `ironmaskTG`. |
| HW observations | `hw_sumed` sums component HW values; `hw_vector` keeps a separate HW value for each observation component. |
| Correctness | Exhaustive checking against `AND`, `ADD`, `COPY`, `AES8`, `keccak5`, `midori4`, `present4`, `prince4`, or a user reference. |
| Mask failures and reuse | Assign a mask to `0` to model a failure; reuse the same random variable to model reused randomness. |
| Execution | Serial or process parallel verification, lazy observation enumeration, live observation reporting, saved results, runtime and peak memory. |

`probing_secret` and `rps_secret` test secret leakage (MI). `probing_share` and `rps_share` test share simulation (CMI), using at most n-1 input shares per input family. NI/SNI/PINI/RPC/RPE use their corresponding share-simulation conditions.

Random probing supports **Standard observations only**, without transition, glitch, or HW extensions. It reports failure coefficients and bounds on f(p), together with log2 threshold bounds. Orders above `-c` remain bounded rather than exactly counted.

## Installation

Tested with Python 3.10 and the following package versions:

```sh
python -m pip install sympy==1.10.1 galois==0.4.6 numpy==2.2.6 numba==0.61.2 alive-progress==2.4.1 rich==15.0.0 bidict==0.23.1 psutil==7.1.0 mpmath==1.4.1
```

## Example: 2-share ISW multiplication

Run commands from this directory. The supplied [`test/ISW_2share.txt`](test/ISW_2share.txt) computes `(a0 XOR a1) AND (b0 XOR b1)`, using one fresh multiplication mask `r`. The masks `ra` and `rb` encode the two inputs.

```text
gadget ISW_2share
    field bool
    secrets a,b
    secretouts c
    inputs a0:2,b0:2
    outputs c0:2
    randoms ra,rb,r
    @c=a&b
    a0:=ra
    a1:=a^a0
    b0:=rb
    b1:=b^b0
    t0=a0&b1
    t1=a1&b0
    t2=r^t0
    t3=t2^t1
    t4=a0&b0
    c0=t4^r
    t5=a1&b1
    c1=t5^t3
    c=:c0^c1
end
```

The nine property checks below use `-cv AND` for multiplication correctness and Hybrid verification (`--tech both`, the default).

Ordinary probing, NI, SNI and PINI at order 1:

```sh
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m probing_secret -t 1
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m probing_share -t 1
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m ni -t 1
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m sni -t 1
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m pini -t 1
```

RPS, RPC and RPE, counting random-probe subsets through cmax=2:

```sh
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m rps_secret -t 1 -c 2
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m rps_share -t 1 -c 2
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m rpc -t 1 -c 2
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m rpe -t 1 -c 2
```

Results append under `checkResult/`, with runtime and peak memory printed in the terminal.

The file uses `:=` for encoding, `=` for gadget operations, and `=:` for decoding. Encoding is excluded from transition/glitch extension. `inputs a0:2,b0:2` declares the two share families `(a0,a1)` and `(b0,b1)`. The `@c=a&b` line supplies the same reference for `-cv user`.

To use the file's reference and MI-only verification:

```sh
python EMIVEL.py -p test/ISW_2share.txt -cv user -m sni -t 1 --tech mi
```

### Leakage model commands

Use this command and append the options from one row below:

```sh
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m probing_secret -t 1
```

| Leakage model | Append |
| --- | --- |
| Standard | Nothing |
| Transition (successive assignments) | `-r transition` |
| Transition (all location pairs) | `-r transitionall` |
| XOR-Transition | `-r transitionxor` |
| Glitch | `-r glitch` |
| Native maskVerif TG | `-r maskverifTG` |
| Native IronMask TG | `-r ironmaskTG` |
| Summed HW | `-r hw_sumed` |
| Componentwise HW | `-r hw_vector` |
| HW-XOR-Transition (sum) | `-r transitionxor hw_sumed` |
| HW-XOR-Transition (vector) | `-r transitionxor hw_vector` |
| HW-Glitch (sum) | `-r glitch hw_sumed` |
| HW-Glitch (vector) | `-r glitch hw_vector` |

Transition + Glitch is selected only through `maskverifTG` or `ironmaskTG`. Combining `glitch` with `transition`, `transitionall`, or `transitionxor` is rejected. Either HW option can also be appended to a TG row. Choose only one: for observation components `(o1, ..., ok)`, `hw_sumed` produces `HW(o1) + ... + HW(ok)`, while `hw_vector` produces `(HW(o1), ..., HW(ok))`. For XOR-Transition, HW is applied after the transition XOR.

For example:

```sh
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m probing_secret -t 1 -r glitch hw_sumed
python EMIVEL.py -p test/ISW_2share.txt -cv AND -m probing_secret -t 1 -r glitch hw_vector
```

This ISW file has no successive assignments to the same variable, so SSA-based Transition/TG commands do not exercise old/new overwrites. `transitionall` still generates circuit-location pairs. Encoding is excluded from both transition and glitch extensions.

## Common options

| Option | Meaning |
| --- | --- |
| `--tech static`, `mi`, `both` | Static-only, MI-only, or Hybrid; default: `both`. |
| `-t N` | Ordinary probe budget or RPC/RPE simulation parameter; also required for RPS. |
| `-c N` | Set the random-probing truncation parameter `c_max` to `N`. |
| `-r hw_sumed` / `-r hw_vector` | Sum / vector of component HW values; combine with an ordinary leakage model as above. |
| `--mcore N` | N worker processes; `0` runs sequentially. Analysis itself is serial. |
| `--detail t` | For ordinary probing, report insecure or unresolved observations as they finish. Ignored for random probing. |
| `--watch c0 c1` | For ordinary probing, also report observations containing these assignment variables, including secure ones; source line numbers are also accepted. Ignored for random probing. |
| `--abort t` | Stop at the first insecure/unresolved result according to the selected technique. Default: `f`. |
| `--maxhours N`, `--maxmem N` | Time limit in hours and per-process memory limit in GiB. |
| `--tofile f` | Disable result saving. Default: `t`. |

Use `python EMIVEL.py --help` for all options. Incomplete checks are reported explicitly.

## Source layout

`EMIVEL.py` handles the CLI and output; `GadgetsAnalysis.py` parses circuits and builds observations; `GadgetsChecker.py` verifies security; `MIA.py` computes MI/CMI; `Parameters.py` defines the internal representation and lazy plans; `auxiliary.py` provides shared finite-field and symbolic operations.
