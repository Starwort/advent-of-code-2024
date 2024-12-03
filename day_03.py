from collections import Counter, defaultdict, deque
import re

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

raw = aoc_helper.fetch(3, 2024)


def parse_raw(raw: str):
    return re.findall(r"mul\((\d+),(\d+)\)|(do\(\))|(don't\(\))", raw)


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    return list(data).mapped(lambda i: int(i[0]) * int(i[1])).sum()


aoc_helper.lazy_test(day=3, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    on = True
    total = 0
    for a, b, do, dont in data:
        if dont:
            on = False
        elif do:
            on = True
        elif on:
            total += int(a) * int(b)

    return total


aoc_helper.lazy_test(day=3, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=3, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=3, year=2024, solution=part_two, data=data)
