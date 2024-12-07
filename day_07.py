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

raw = aoc_helper.fetch(7, 2024)


def parse_raw(raw: str):
    return list(raw.splitlines()).mapped(extract_ints)


data = parse_raw(raw)


def could_work(cal: list[int]):
    target, first, *rest = cal
    for i in range(2 ** (len(rest))):
        val = first
        for bit, num in enumerate(rest):
            if (i >> bit) & 1:
                val += num
            else:
                val *= num
        if val == target:
            return True
    return False


def could_work2(cal: list[int]):
    target, first, *rest = cal
    for i in range(3 ** (len(rest))):
        val = first
        for bit, num in enumerate(rest):
            match (i // (3**bit)) % 3:
                case 0:
                    val *= num
                case 1:
                    val += num
                case 2:
                    val *= 10 ** len(str(num))
                    val += num
        if val == target:
            return True
    return False


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    return data.filtered(could_work).mapped(lambda i: i[0]).sum()


aoc_helper.lazy_test(day=7, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    return data.filtered(could_work2).mapped(lambda i: i[0]).sum()


aoc_helper.lazy_test(day=7, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=7, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=7, year=2024, solution=part_two, data=data)
