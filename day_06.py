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

raw = aoc_helper.fetch(6, 2024)


def parse_raw(raw: str):
    grid = Grid.from_string(
        raw,
        classify=lambda i: {
            ".": 0,
            "#": 1,
            "^": 2,
            ">": 3,
            "v": 4,
            "<": 5,
        }[i],
    )
    for y, row in enumerate(grid):
        for x, val in enumerate(row):
            if val in (2, 3, 4, 5):
                start = (x, y), [[0, -1], [1, 0], [0, 1], [-1, 0]][val - 2]
                grid[y][x] = 0
                return grid, start
    return grid, ((0, 0), [1, 0])


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    grid, ((x, y), (dx, dy)) = data
    positions = set()
    while 0 <= x < grid.width and 0 <= y < grid.height:
        positions.add((x, y))
        nx, ny = x + dx, y + dy
        if 0 <= nx < grid.width and 0 <= ny < grid.height and grid[ny][nx] == 1:
            dx, dy = -dy, dx
        else:
            x, y = nx, ny
    return len(positions)


aoc_helper.lazy_test(
    day=6,
    year=2024,
    parse=parse_raw,
    solution=part_one,
)


def collect_path(data=data):
    grid, ((x, y), (dx, dy)) = data
    positions = set()
    while 0 <= x < grid.width and 0 <= y < grid.height:
        positions.add((x, y))
        nx, ny = x + dx, y + dy
        if 0 <= nx < grid.width and 0 <= ny < grid.height and grid[ny][nx] == 1:
            dx, dy = -dy, dx
        else:
            x, y = nx, ny
    return positions


def try_obstruction(data=data, ox=0, oy=0):
    grid, ((x, y), (dx, dy)) = data
    positions = set()
    while 0 <= x < grid.width and 0 <= y < grid.height:
        if (x, y, dx, dy) in positions:
            return True
        positions.add((x, y, dx, dy))
        nx, ny = x + dx, y + dy
        if (
            0 <= nx < grid.width
            and 0 <= ny < grid.height
            and (grid[ny][nx] == 1 or nx == ox and ny == oy)
        ):
            dx, dy = -dy, dx
        else:
            x, y = nx, ny
    return False


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    ans = 0
    _, (pos, _) = data
    for x, y in collect_path(data):
        if (x, y) != pos and try_obstruction(data, x, y):
            ans += 1
    return ans


aoc_helper.lazy_test(day=6, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=6, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=6, year=2024, solution=part_two, data=data)
