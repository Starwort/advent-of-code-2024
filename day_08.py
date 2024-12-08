from collections import Counter, defaultdict, deque
from itertools import combinations

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

raw = aoc_helper.fetch(8, 2024)


def parse_raw(raw: str):
    nodes = set()

    def classify(c: str):
        if c == ".":
            return None
        nodes.add(c)
        return c

    return Grid.from_string(raw, classify=classify), nodes


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    grid: Grid[str]
    grid, nodes = data
    antinodes = set()
    for i in nodes:
        for a, b in combinations(grid.find_all(SparseGrid.from_string(i, str, str)), 2):
            dx = a[0] - b[0]
            dy = a[1] - b[1]
            ax = a[0] + dx
            ay = a[1] + dy
            bx = b[0] - dx
            by = b[1] - dy
            if 0 <= ax < grid.width and 0 <= ay < grid.height:
                antinodes.add((ax, ay))
            if 0 <= bx < grid.width and 0 <= by < grid.height:
                antinodes.add((bx, by))
    return len(antinodes)


aoc_helper.lazy_test(day=8, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    grid: Grid[str]
    grid, nodes = data
    antinodes = set()
    for i in nodes:
        for a, b in combinations(grid.find_all(SparseGrid.from_string(i, str, str)), 2):
            dx = a[0] - b[0]
            dy = a[1] - b[1]
            ax, ay = a
            bx, by = b
            while 0 <= ax < grid.width and 0 <= ay < grid.height:
                antinodes.add((ax, ay))
                ax += dx
                ay += dy
            while 0 <= bx < grid.width and 0 <= by < grid.height:
                antinodes.add((bx, by))
                bx -= dx
                by -= dy
    return len(antinodes)


aoc_helper.lazy_test(day=8, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=8, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=8, year=2024, solution=part_two, data=data)
