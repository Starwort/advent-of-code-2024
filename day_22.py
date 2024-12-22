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
    import numpy as np

    all_data = list([data])
    for i in range(2000):
        data = data.mapped(evolve)
        all_data.append(data)
    arr = np.array(all_data)
    arr = np.repeat(arr.reshape(*arr.shape, 1), 5, axis=2)
    arr %= 10
    arr[1:, :, 1] = arr[1:, :, 0] - arr[:-1, :, 0]
    arr[2:, :, 2] = arr[1:-1, :, 0] - arr[:-2, :, 0]
    arr[3:, :, 3] = arr[1:-2, :, 0] - arr[:-3, :, 0]
    arr[4:, :, 4] = arr[1:-3, :, 0] - arr[:-4, :, 0]
    seen = {}
    for row in arr[4:]:
        for a, b, c, d in row[:, 1:]:
            if (a, b, c, d) in seen:
                continue
            vals = np.argmax(
                (arr[4:, :, 4] == a)
                * (arr[4:, :, 3] == b)
                * (arr[4:, :, 2] == c)
                * (arr[4:, :, 1] == d),
                axis=0,
            )
            tot = 0
            for i, val in enumerate(vals):
                tot += arr[4 + val, i, 0]
            seen[a, b, c, d] = tot
    seq, val = max(seen.items(), key=lambda i: i[1])
    return val


aoc_helper.lazy_submit(day=22, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=22, year=2024, solution=part_two, data=data)
