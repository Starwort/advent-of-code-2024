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

raw = aoc_helper.fetch(2, 2024)


def parse_raw(raw: str):
    return list(raw.splitlines()).mapped(extract_ints)


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    return data.filtered(safe).len()


aoc_helper.lazy_test(day=2, year=2024, parse=parse_raw, solution=part_one)


def safe(i: list[int]):
    return (i == sorted(i) or i == sorted(i, reverse=True)) and i.windowed(2).mapped(
        lambda i: 1 <= abs(i[0] - i[1]) <= 3
    ).all()


def safe2(i: list[int]):
    return (
        range(i.len())
        .map(
            lambda j: i.enumerated()
            .filtered(lambda k: k[0] != j)
            .mapped(lambda k: k[1])
        )
        .map(safe)
        .any()
    )


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    return data.filtered(safe2).len()


aoc_helper.lazy_test(
    day=2,
    year=2024,
    parse=parse_raw,
    solution=part_two,
    test_data=(
        """7 6 4 2 1
1 2 7 8 9
9 7 6 2 1
1 3 2 4 5
8 6 4 4 1
1 3 6 7 9""",
        4,
    ),
)

aoc_helper.lazy_submit(day=2, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=2, year=2024, solution=part_two, data=data)
