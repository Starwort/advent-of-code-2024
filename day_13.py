from collections import Counter, defaultdict, deque

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
import z3

raw = aoc_helper.fetch(13, 2024)


def parse_raw(raw: str):
    return list(raw.split("\n\n")).mapped(lambda i: extract_ints(i).chunked(2))


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    total = 0
    for machine in data:
        button_a, button_b, target = machine
        best = float("inf")
        for a in range(101):
            for b in range(101):
                if (
                    a * button_a[0] + b * button_b[0],
                    a * button_a[1] + b * button_b[1],
                ) == target:
                    best = min(best, 3 * a + b)
        if best != float("inf"):
            total += best
    return total


# aoc_helper.lazy_test(day=13, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    total = 0
    for machine in data:
        button_a, button_b, target = machine
        target = (target[0] + 10000000000000, target[1] + 10000000000000)
        a = z3.Int("a")
        b = z3.Int("b")
        o = z3.Optimize()
        o.add(a >= 0)
        o.add(b >= 0)
        o.add(a * button_a[0] + b * button_b[0] == target[0])
        o.add(a * button_a[1] + b * button_b[1] == target[1])
        o.minimize(3 * a + b)
        if o.check() == z3.sat:
            model = o.model()
            total += 3 * model[a].as_long() + model[b].as_long()
    return total


# aoc_helper.lazy_test(day=13, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=13, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=13, year=2024, solution=part_two, data=data)
