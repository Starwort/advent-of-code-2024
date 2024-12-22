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

raw = aoc_helper.fetch(22, 2024)


def parse_raw(raw: str):
    return extract_ints(raw)


data = parse_raw(raw)


def evolve(secret: int):
    secret ^= secret * 64
    secret %= 16777216
    secret ^= secret // 32
    secret %= 16777216
    secret ^= secret * 2048
    secret %= 16777216
    return secret


def part_one(data=data):
    for i in range(2000):
        data = data.mapped(evolve)
    return data.sum()


aoc_helper.lazy_test(day=22, year=2024, parse=parse_raw, solution=part_one)


def part_two(data=data):
    vals = defaultdict(int)
    for val in data:
        data = list([val])
        for _ in range(1999):
            data.append(evolve(data[-1]))
        diffs = data.windowed(2).mapped(lambda i: i[1] % 10 - i[0] % 10)
        seen = set()
        for val, (a, b, c, d) in zip(data[4:], diffs.windowed(4)):
            if (a, b, c, d) not in seen:
                vals[a, b, c, d] += val % 10
                seen.add((a, b, c, d))
            a, b, c, d = b, c, d, -(val % 10 - (val := evolve(val)) % 10)
    return max(vals.values())


aoc_helper.lazy_submit(day=22, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=22, year=2024, solution=part_two, data=data)
