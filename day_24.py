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


def solve(a, b):
    import z3

    solver = z3.Solver()
    wire_vals = {}
    for wire, val in a:
        wire_vals[wire] = z3.Int(wire)
        solver.add(wire_vals[wire] == val)
    for _, wire in b:
        wire_vals[wire] = z3.Int(wire)
    swaps = {
        wire_a: {wire_b: z3.Int(wire_a + "_" + wire_b) for wire_b in wire_vals}
        for wire_a in wire_vals
    }
    is_swapped = {}
    total_swaps = 0
    for y, (wire_a, row) in enumerate(swaps.items()):
        row_total = 0
        for x, (wire_b, swap) in enumerate(row.items()):
            if y == x:
                solver.add(swap == 0)
            elif y < x:
                solver.add(swap == swaps[wire_b][wire_a])
            row_total += swap
        solver.add(row_total <= 1)
        is_swapped[wire_a] = row_total
        total_swaps += row_total
    solver.add(total_swaps == 8)  # 4 swaps = 8 affected wires
    for formula, wire in b:
        out = (1 - is_swapped[wire]) * wire_vals[wire]
        for swapped_with, swap in swaps[wire].items():
            out += swap * wire_vals[swapped_with]
        if "XOR" in formula:
            lhs, rhs = formula.split(" XOR ")
            lhs = wire_vals[lhs]
            rhs = wire_vals[rhs]
            solver.add(out == lhs + rhs)
        elif "AND" in formula:
            lhs, rhs = formula.split(" AND ")
            lhs = wire_vals[lhs]
            rhs = wire_vals[rhs]
            solver.add(out == lhs * rhs)
        elif "OR" in formula:
            lhs, rhs = formula.split(" OR ")
            lhs = wire_vals[lhs]
            rhs = wire_vals[rhs]
            solver.add(out == lhs + rhs - 2 * lhs * rhs)
    xs = [wire_vals[wire] for wire, val in sorted(a) if wire.startswith("x")]
    x = 0
    for x_ in xs:
        x *= 2
        x += x_
    ys = [wire_vals[wire] for wire, val in sorted(a) if wire.startswith("y")]
    y = 0
    for y_ in ys:
        y *= 2
        y += y_
    zs = [wire_vals[wire] for wire in sorted(wire_vals) if wire.startswith("z")]
    z = 0
    for z_ in zs:
        z *= 2
        z += z_
    solver.add(z == x + y)
    return solver, solver.check() == z3.sat


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
        find = lambda a, b, op: (
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
    # out = b.mapped(lambda i: i[1]).filtered(lambda x: x.startswith("z")).max()
    # to_find = [out]
    # for formula, wire in b:
    #     print(
    #         "let",
    #         wire,
    #         "=",
    #         formula.replace("XOR", "^").replace("OR", "+").replace("AND", "*"),
    #     )
    # while to_find:
    #     wire = to_find.pop()
    #     formula = (b.find(lambda x: x[1] == wire) or " ")[0]
    #     if formula == " ":
    #         continue
    #     lhs, _, rhs = formula.split(" ")
    #     rval = f"({formula})"
    #     # if "XOR" in formula:
    #     #     rval = f"(({lhs} + {rhs}) * ({lhs} * {rhs})')"
    #     out = out.replace(
    #         wire, rval.replace("XOR", "^").replace("OR", "+").replace("AND", "*")
    #     )
    #     to_find.extend([rhs, lhs])
    # print(out)
    # solver, sat = solve(a, b)
    # assert sat
    # global model
    # model = solver.model()
    # for c, d, e, f, g, h, i, j in b.iter().map(lambda x: x[1]).combinations(8):
    #     for c_swap in {d, e, f, g, h, i, j}:
    #         for swap2a in {d, e, f, g, h, i, j} - {c_swap}:
    #             for swap2b in {d, e, f, g, h, i, j} - {c_swap, swap2a}:
    #                 for swap3a in {d, e, f, g, h, i, j} - {c_swap, swap2a, swap2b}:
    #                     for swap3b in {d, e, f, g, h, i, j} - {
    #                         c_swap,
    #                         swap2a,
    #                         swap2b,
    #                         swap3a,
    #                     }:
    #                         for swap4a in {d, e, f, g, h, i, j} - {
    #                             c_swap,
    #                             swap2a,
    #                             swap2b,
    #                             swap3a,
    #                             swap3b,
    #                         }:
    #                             swap4b = (
    #                                 {d, e, f, g, h, i, j}
    #                                 - {c_swap, swap2a, swap2b, swap3a, swap3b, swap4a}
    #                             ).pop()
    #                             solver, sat = solve(
    #                                 a,
    #                                 b.mapped(
    #                                     lambda x: (
    #                                         x[0],
    #                                         {
    #                                             c: c_swap,
    #                                             c_swap: c,
    #                                             swap2a: swap2b,
    #                                             swap2b: swap2a,
    #                                             swap3a: swap3b,
    #                                             swap3b: swap3a,
    #                                             swap4a: swap4b,
    #                                             swap4b: swap4a,
    #                                         }.get(x[1], x[1]),
    #                                     )
    #                                 ),
    #                             )
    #                             if sat:
    #                                 print(solver.model())
    #                                 print(
    #                                     f'part_one((data[0],data[1].mapped(lambda x: (x[0], {"{"+                                            (
    #                                             f"{c!r}: {c_swap!r},"+
    #                                             f"{c_swap!r}: {c!r},"+
    #                                             f"{swap2a!r}: {swap2b!r},"+
    #                                             f"{swap2b!r}: {swap2a!r},"+
    #                                             f"{swap3a!r}: {swap3b!r},"+
    #                                             f"{swap3b!r}: {swap3a!r},"+
    #                                             f"{swap4a!r}: {swap4b!r},"+
    #                                             f"{swap4b!r}: {swap4a!r}"
    #                                         )+"}"}.get(x[1], x[1])))))'
    #                                 )
    #                                 return ",".join(sorted([c, d, e, f, g, h, i, j]))


aoc_helper.lazy_submit(day=24, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=24, year=2024, solution=part_two, data=data)
