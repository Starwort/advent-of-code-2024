from collections import Counter, defaultdict, deque

import aoc_helper
import z3
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

raw = aoc_helper.fetch(13, 2024)


def parse_raw(raw: str):
    return list(raw.split("\n\n")).mapped(extract_ints)


data = parse_raw(raw)


def optimise_machine(ax, ay, bx, by, tx, ty):
    a = z3.Int("a")
    b = z3.Int("b")
    o = z3.Optimize()
    o.add(a >= 0)
    o.add(b >= 0)
    o.add(a * ax + b * bx == tx)
    o.add(a * ay + b * by == ty)
    obj = o.minimize(3 * a + b)
    if o.check() == z3.sat:
        return obj.value().as_long()
    return 0


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    return data.mapped(lambda i: optimise_machine(*i)).sum()


# aoc_helper.lazy_test(day=13, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    return data.mapped(
        lambda i: optimise_machine(*i[:4], i[4] + 10000000000000, i[5] + 10000000000000)
    )


# aoc_helper.lazy_test(day=13, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=13, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=13, year=2024, solution=part_two, data=data)
