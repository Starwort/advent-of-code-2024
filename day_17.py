from collections import Counter, defaultdict, deque
from itertools import count

import aoc_helper
from aoc_helper import (
    Grid,
    PrioQueue,
    SparseGrid,
    chunk,
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

raw = aoc_helper.fetch(17, 2024)


def parse_raw(raw: str):
    return extract_ints(raw)


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    a, b, c, *rest = data
    ip = 0

    def opa(cell):
        match rest[cell]:
            case 0 | 1 | 2 | 3:
                return rest[cell]
            case 4:
                return a
            case 5:
                return b
            case 6:
                return c

    out = []

    while ip in range(len(rest)):
        opc = rest[ip]
        ip += 2
        match opc:
            case 0:
                a >>= opa(ip - 1)
            case 1:
                b ^= rest[ip - 1]
            case 2:
                b = opa(ip - 1) & 7
            case 3:
                if a:
                    ip = rest[ip - 1]
            case 4:
                b ^= c
            case 5:
                out.append(opa(ip - 1) & 7)
            case 6:
                b = a >> opa(ip - 1)
            case 7:
                c = a >> opa(ip - 1)
    return ",".join(map(str, out))


aoc_helper.lazy_test(day=17, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    a, b, c, *rest = data
    instructions = []
    found_jump = False
    for opc, opa in chunk(rest, 2):
        opa2 = [0, 1, 2, 3, "a", "b", "c", "_"][opa]
        assert not found_jump
        match opc:
            case 0:
                instructions.append(f"a >>= {opa2}")
            case 1:
                instructions.append(f"b ^= {opa}")
            case 2:
                instructions.append(f"b = {opa2} & 7")
            case 3:
                assert opa == 0
                found_jump = True
            case 4:
                instructions.append("b ^= c")
            case 5:
                instructions.append(f"return {opa2} & 7")
            case 6:
                instructions.append(f"b = a >> {opa2}")
            case 7:
                instructions.append(f"c = a >> {opa2}")
    vals = globals() | locals()
    exec(
        "def out_val(a):\n    b=c=0\n" + "\n".join("    " + i for i in instructions),
        vals,
        vals,
    )
    possible_a = [0]
    for i in rest[::-1]:
        possible_a = [
            new_a
            for a in range(8)
            for last_a in possible_a
            if vals["out_val"](new_a := a + (last_a << 3)) == i and new_a
        ]
    return min(possible_a)


aoc_helper.lazy_test(day=17, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=17, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=17, year=2024, solution=part_two, data=data)
