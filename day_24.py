from collections import Counter, defaultdict, deque
from itertools import zip_longest

import aoc_helper
from aoc_helper import (
    Grid,
    PrioQueue,
    SparseGrid,
    decode_text,
    extract_ints,
    extract_iranges,
    extract_ranges,
    extract_uints,
    frange,
    irange,
    iter,
    list,
    map,
    multirange,
    range,
    search,
    tail_call,
)

raw = aoc_helper.fetch(24, 2024)


def parse_raw(raw: str):
    a, b = raw.split("\n\n")
    a = (
        list(a.splitlines())
        .mapped(lambda x: x.split(": "))
        .mapped(lambda x: (x[0], x[1] == "1"))
    )
    b = list(b.splitlines()).mapped(lambda x: x.split(" -> "))
    return a, b


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    a, b = data
    wire_vals = {}
    for wire, val in a:
        wire_vals[wire] = val
    to_eval = deque(b)
    while to_eval:
        formula, wire = to_eval.popleft()
        try:
            if "XOR" in formula:
                a, b = formula.split(" XOR ")
                a = wire_vals[a]
                b = wire_vals[b]
                wire_vals[wire] = a ^ b
            elif "AND" in formula:
                a, b = formula.split(" AND ")
                a = wire_vals[a]
                b = wire_vals[b]
                wire_vals[wire] = a and b
            elif "OR" in formula:
                a, b = formula.split(" OR ")
                a = wire_vals[a]
                b = wire_vals[b]
                wire_vals[wire] = a or b
        except KeyError:
            to_eval.append((formula, wire))
    return int(
        "".join(
            iter(wire_vals.items())
            .filter(lambda x: x[0][0] == "z")
            .sorted()
            .reversed()
            .mapped(lambda x: "01"[x[1]])
        ),
        2,
    )


aoc_helper.lazy_test(
    day=24,
    year=2024,
    parse=parse_raw,
    solution=part_one,
    test_data=(
        """x00: 1
x01: 0
x02: 1
x03: 1
x04: 0
y00: 1
y01: 1
y02: 1
y03: 1
y04: 1

ntg XOR fgs -> mjb
y02 OR x01 -> tnw
kwq OR kpj -> z05
x00 OR x03 -> fst
tgd XOR rvg -> z01
vdt OR tnw -> bfw
bfw AND frj -> z10
ffh OR nrd -> bqk
y00 AND y03 -> djm
y03 OR y00 -> psh
bqk OR frj -> z08
tnw OR fst -> frj
gnj AND tgd -> z11
bfw XOR mjb -> z00
x03 OR x00 -> vdt
gnj AND wpb -> z02
x04 AND y00 -> kjc
djm OR pbm -> qhw
nrd AND vdt -> hwm
kjc AND fst -> rvg
y04 OR y02 -> fgs
y01 AND x02 -> pbm
ntg OR kjc -> kwq
psh XOR fgs -> tgd
qhw XOR tgd -> z09
pbm OR djm -> kpj
x03 XOR y03 -> ffh
x00 XOR y04 -> ntg
bfw OR bqk -> z06
nrd XOR fgs -> wpb
frj XOR qhw -> z04
bqk OR frj -> z07
y03 OR x01 -> nrd
hwm AND bqk -> z03
tgd XOR rvg -> z12
tnw OR pbm -> gnj""",
        2024,
    ),
)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    b: list
    a, rules = data
    c = None
    swaps = set()
    for i in range(45):
        j = f"{i:02}"

        def find(a, b, op):
            return (
                rules.find(lambda x: x[0] in (f"{a} {op} {b}", f"{b} {op} {a}"))
                or [None, None]
            )[1]

        # a full-adder should be M=X^Y, N=X&Y, R=C&M, Z=C^M, C=R|N
        m = find(f"x{j}", f"y{j}", "XOR")
        n = find(f"x{j}", f"y{j}", "AND")
        if c is not None:
            r = find(c, m, "AND")
            if r is None:
                m, n = n, m
                swaps |= {m, n}
                r = find(c, m, "AND")
            z = find(c, m, "XOR")
            if m.startswith("z"):
                m, z = z, m
                swaps |= {m, z}
            if n.startswith("z"):
                n, z = z, n
                swaps |= {n, z}
            if r.startswith("z"):
                r, z = z, r
                swaps |= {r, z}
            c = find(r, n, "OR")
        else:
            c = n

        if c.startswith("z") and c != "z45":
            c, z = z, c
            swaps |= {c, z}
    return ",".join(sorted(swaps))


aoc_helper.lazy_submit(day=24, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=24, year=2024, solution=part_two, data=data)
