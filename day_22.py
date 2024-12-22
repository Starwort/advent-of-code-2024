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


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
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


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
# def part_two(data=data):
#     all_data = list[list[tuple[int, int]]]([data.mapped(lambda i: (0, i % 10))])
#     for i in range(2000):
#         data2 = data.mapped(evolve)
#         all_data.append(
#             iter(zip(data, data2))
#             .map(lambda i: (i[1] % 10 - i[0] % 10, i[1] % 10))
#             .collect()
#         )
#         data = data2
#     seen = {}
#     for a, b, c, d in all_data[1:].windowed(4):
#         for (a, _), (b, _), (c, _), (d, _) in zip(a, b, c, d):
#             if (a, b, c, d) in seen:
#                 continue
#             total = 0
#             for as_, bs, cs, ds in all_data[1:].windowed(4):
#                 for (a_, _), (b_, _), (c_, _), (d_, val) in zip(as_, bs, cs, ds):
#                     if (a_, b_, c_, d_) == (a, b, c, d):
#                         total += val
#             seen[a, b, c, d] = total
#     return max(seen.items(), key=lambda i: i[1])[1]


def part_two(data=data):
    import numpy as np

    global arr
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


# def part_two(data=data):
#     vals = defaultdict(int)
#     for val in data:
#         data = list([val])
#         for _ in range(1999):
#             data.append(evolve(data[-1]))
#         diffs = data.windowed(2).mapped(lambda i: i[1] % 10 - i[0] % 10)
#         seen = set()
#         for val, (a, b, c, d) in zip(data[4:], diffs.windowed(4)):
#             if (a, b, c, d) not in seen:
#                 vals[a, b, c, d] += val % 10
#                 seen.add((a, b, c, d))
#             a, b, c, d = b, c, d, -(val % 10 - (val := evolve(val)) % 10)
#     seq, val = max(vals.items(), key=lambda i: i[1])
#     print(seq)
#     return val
#     return max(vals.values())


# aoc_helper.lazy_test(day=22, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=22, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=22, year=2024, solution=part_two, data=data)
