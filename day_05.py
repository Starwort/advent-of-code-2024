from collections import Counter, defaultdict, deque
from functools import cmp_to_key

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

raw = aoc_helper.fetch(5, 2024)


def parse_raw(raw: str):
    a, b = raw.split("\n\n")
    return set(extract_ints(a).chunked(2).mapped(tuple)), list(b.splitlines()).mapped(
        extract_ints
    )


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    a, b = data
    b = b.filtered(
        lambda i: iter(a).all(
            lambda j: j[0] not in i or j[1] not in i or i.index(j[0]) < i.index(j[1])
        )
    )
    return b.mapped(lambda i: i[i.len() // 2]).sum()


aoc_helper.lazy_test(day=5, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    a, b = data
    c = b.filtered(
        lambda i: iter(a).all(
            lambda j: j[0] not in i or j[1] not in i or i.index(j[0]) < i.index(j[1])
        )
    )
    b = b.filtered(lambda i: i not in c)
    a = {i: -1 for i in a} | {(i[1], i[0]): 1 for i in a}
    for i in b:
        i.sort(key=cmp_to_key(lambda x, y: a.get((x, y), 0)))
    return b.mapped(lambda i: i[i.len() // 2]).sum()


aoc_helper.lazy_test(day=5, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=5, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=5, year=2024, solution=part_two, data=data)
