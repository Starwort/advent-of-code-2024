from collections import Counter, defaultdict, deque
from functools import cache

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

raw = aoc_helper.fetch(19, 2024)


def parse_raw(raw: str):
    a, b = raw.split("\n\n")
    return list(a.split(", ")), list(b.split("\n"))


data = parse_raw(raw)


def make(s: str, a: list[str]):
    @cache
    def make(s: str):
        if not s:
            return 1
        tot = 0
        for x in a:
            if s.startswith(x):
                tot += make(s[len(x) :])
        return tot

    return make(s)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    b: list[str]
    a: list[str]
    a, b = data
    return b.filtered(lambda x: make(x, a)).len()


aoc_helper.lazy_test(day=19, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    b: list[str]
    a: list[str]
    a, b = data

    return b.mapped(lambda x: make(x, a)).sum()


aoc_helper.lazy_test(day=19, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=19, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=19, year=2024, solution=part_two, data=data)
