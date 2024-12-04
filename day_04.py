import re
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

raw = aoc_helper.fetch(4, 2024)


def parse_raw(raw: str):
    return Grid.from_string(raw, str)


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    return (
        list(
            [
                g := SparseGrid.from_string("XMAS", str, str),
                g := g.rotate_45_clockwise(),
                g := g.rotate_45_clockwise(),
                g := g.rotate_45_clockwise(),
                g := g.rotate_45_clockwise(),
                g := g.rotate_45_clockwise(),
                g := g.rotate_45_clockwise(),
                g.rotate_45_clockwise(),
            ]
        )
        .mapped(lambda i: data.find_all(i).count())
        .sum()
    )


aoc_helper.lazy_test(
    day=4,
    year=2024,
    parse=parse_raw,
    solution=part_one,
)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    return (
        list(
            [
                g := SparseGrid.from_string("M.S\n.A.\nM.S", str, str),
                g := g.rotate_45_clockwise().rotate_45_clockwise(),
                g := g.rotate_45_clockwise().rotate_45_clockwise(),
                g.rotate_45_clockwise().rotate_45_clockwise(),
            ]
        )
        .mapped(lambda i: data.find_all(i).count())
        .sum()
    )


aoc_helper.lazy_test(day=4, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=4, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=4, year=2024, solution=part_two, data=data)
