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

raw = aoc_helper.fetch(20, 2024)


def parse_raw(raw: str):
    grid = Grid.from_string(raw, classify=".#SE".index)
    start = next(grid.find_all(2))
    end = next(grid.find_all(3))
    grid[start] = 0
    grid[end] = 0
    return grid, start, end


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    grid: Grid[int]
    grid, start, end = data
    cells = defaultdict(lambda: float("inf"))
    q = PrioQueue([(0, start)])
    for d, p in q:
        if cells[p] <= d:
            continue
        cells[p] = d
        for np, n in grid.orthogonal_neighbours(*p):
            if n == 0:
                q.push((d + 1, np))
    out = (
        list(cells)
        .mapped(
            lambda p: [
                cells[(p[0] + x, p[1] + y)] - cells[p] - 2
                for x, y in (
                    (-2, 0),
                    (-1, -1),
                    (0, -2),
                    (1, -1),
                    (2, 0),
                    (1, 1),
                    (0, 2),
                    (-1, 1),
                )
            ]
        )
        .flat()
        .filtered(lambda i: i != float("inf"))
        .filtered(lambda i: i > 0)
    )
    print(Counter(out))
    return out.filtered(lambda i: i >= 100).len()


aoc_helper.lazy_test(
    day=20,
    year=2024,
    parse=parse_raw,
    solution=part_one,
    test_data=(
        """###############
#...#...#.....#
#.#.#.#.#.###.#
#S#...#.#.#...#
#######.#.#.###
#######.#.#...#
#######.#.###.#
###..E#...#...#
###.#######.###
#...###...#...#
#.#####.#.###.#
#.#...#.#.#...#
#.#.#.#.#.#.###
#...#...#...###
###############""",
        0,
    ),
)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    grid: Grid[int]
    grid, start, end = data
    cells = defaultdict(lambda: float("inf"))
    q = PrioQueue([(0, start)])
    for d, p in q:
        if cells[p] <= d:
            continue
        cells[p] = d
        for np, n in grid.orthogonal_neighbours(*p):
            if n == 0:
                q.push((d + 1, np))
    out = (
        list(cells)
        .mapped(
            lambda p: [
                cells[(p[0] + x, p[1] + y)] - cells[p] - abs(x) - abs(y)
                for x in irange(-20, 20)
                for y in irange(-20, 20)
                if abs(x) + abs(y) <= 20
            ]
        )
        .flat()
        .filtered(lambda i: i != float("inf"))
        .filtered(lambda i: i > 50)
    )
    print(Counter(out))
    return out.filtered(lambda i: i >= 100).len()


aoc_helper.lazy_test(
    day=20,
    year=2024,
    parse=parse_raw,
    solution=part_two,
    test_data=(
        """###############
#...#...#.....#
#.#.#.#.#.###.#
#S#...#.#.#...#
#######.#.#.###
#######.#.#...#
#######.#.###.#
###..E#...#...#
###.#######.###
#...###...#...#
#.#####.#.###.#
#.#...#.#.#...#
#.#.#.#.#.#.###
#...#...#...###
###############""",
        0,
    ),
)

aoc_helper.lazy_submit(day=20, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=20, year=2024, solution=part_two, data=data)
