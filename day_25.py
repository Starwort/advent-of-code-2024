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

raw = aoc_helper.fetch(25, 2024)


def parse_raw(raw: str):
    return list(map(Grid.from_string, raw.split("\n\n")))


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data: list[Grid[int]] = data):
    height = data[0].height
    keys = data.filtered(lambda i: i[0].all()).mapped(
        lambda i: i.transpose().data.mapped(lambda i: i.filtered(1).len())
    )
    locks = data.filtered(lambda i: i[0].none()).mapped(
        lambda i: i.transpose().data.mapped(lambda i: i.filtered(1).len())
    )
    return sum(
        all(k + l <= height for k, l in zip(key, lock))
        for key in keys
        for lock in locks
    )


aoc_helper.lazy_test(day=25, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data): ...


aoc_helper.lazy_test(day=25, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=25, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=25, year=2024, solution=part_two, data=data)
