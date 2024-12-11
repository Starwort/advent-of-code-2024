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

raw = aoc_helper.fetch(11, 2024)


def parse_raw(raw: str):
    return extract_ints(raw)


data = parse_raw(raw)


def step_stone(stone: int):
    if stone == 0:
        return [1]
    if (x := len(str(stone))) % 2 == 0:
        return [int(str(stone)[: x // 2]), int(str(stone)[x // 2 :])]
    return [stone * 2024]


def step(data=data):
    return data.mapped(step_stone).flat()


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    for _ in range(25):
        data = step(data)
    return len(data)


aoc_helper.lazy_test(day=11, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    stones = Counter(data)
    for _ in range(75):
        next_stones = (
            iter(stones.items())
            .map(lambda i: [(j, i[1]) for j in step_stone(i[0])])
            .flatten()
            .collect()
            .sorted()
        )
        stones = defaultdict(int)
        for stone, count in next_stones:
            stones[stone] += count
    return sum(stones.values())


aoc_helper.lazy_test(day=11, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=11, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=11, year=2024, solution=part_two, data=data)
