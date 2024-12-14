from collections import Counter, defaultdict, deque
from itertools import count

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

raw = aoc_helper.fetch(14, 2024)


def parse_raw(raw: str):
    return extract_ints(raw).chunked(2).chunked(2)


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    data = data.copy()
    for i in range(100):
        for j, ((x, y), (dx, dy)) in data.enumerated():
            x += dx
            y += dy
            x %= 101
            y %= 103
            data[j] = (x, y), (dx, dy)
    return (
        data.filtered(lambda r: r[0][0] < 50 and r[0][1] < 51).len()
        * data.filtered(lambda r: r[0][0] < 50 and r[0][1] > 51).len()
        * data.filtered(lambda r: r[0][0] > 50 and r[0][1] < 51).len()
        * data.filtered(lambda r: r[0][0] > 50 and r[0][1] > 51).len()
    )


# aoc_helper.lazy_test(day=14, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    data = data.copy()
    for time in count(1):
        for j, ((x, y), (dx, dy)) in data.enumerated():
            x += dx
            y += dy
            x %= 101
            y %= 103
            data[j] = (x, y), (dx, dy)
        if len({r for r, _ in data}) == data.len():
            grid = Grid(list([list([False]) * 101 for _ in range(103)]))
            for (x, y), _ in data:
                grid[y][x] = True
            print(grid)
            return time


aoc_helper.lazy_test(day=14, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=14, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=14, year=2024, solution=part_two, data=data)
