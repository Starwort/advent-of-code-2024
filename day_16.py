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

raw = aoc_helper.fetch(16, 2024)


def parse_raw(raw: str):
    grid = Grid.from_string(raw.replace("S", ".").replace("E", "."))
    start = end = (0, 0)
    for y, row in enumerate(raw.splitlines()):
        for x, cell in enumerate(row):
            if cell == "S":
                start = (x, y)
            elif cell == "E":
                end = (x, y)
    return grid, start, end


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    # def score(path: tuple[tuple[int, int], ...]):
    #     dx = 1
    #     dy = 0
    #     (x, y), *rest = path
    #     cost = len(rest)
    #     for nx, ny in rest:
    #         if nx - x != dx or ny - y != dy:
    #             cost += 1000
    #             dx = nx - x
    #             dy = ny - y
    #         x, y = nx, ny
    #     return cost

    # grid: Grid[str]
    # grid, start, end = data

    # return (
    #     grid.explore(
    #         start=start,
    #         can_move=lambda _, __, ___, cell: cell == ".",
    #         return_path_when=lambda pos, _: pos == end,
    #         unique_paths=True,
    #     )
    #     .map(score)
    #     .min()
    # )

    grid: Grid[int]
    grid, start, end = data

    to_explore = PrioQueue([(0, start, 1, 0, [])])
    seen = set()
    for cost, pos, dx, dy, path in to_explore:
        if pos == end:
            return cost
        if (pos, dx, dy) in seen:
            continue
        seen.add((pos, dx, dy))
        x, y = pos

        for (nx, ny), cell in grid.orthogonal_neighbours(x, y):
            if cell:
                continue
            ndx = nx - x
            ndy = ny - y
            penalty = 1
            if ndx != dx or ndy != dy:
                penalty += 1000
            to_explore.push(
                (cost + penalty, (nx, ny), ndx, ndy, [*path, (nx, ny, dx, dy)])
            )


aoc_helper.lazy_test(
    day=16,
    year=2024,
    parse=parse_raw,
    solution=part_one,
    test_data=(
        """###############
#.......#....E#
#.#.###.#.###.#
#.....#.#...#.#
#.###.#####.#.#
#.#.#.......#.#
#.#.#####.###.#
#...........#.#
###.#.#####.#.#
#...#.....#.#.#
#.#.#.###.#.#.#
#.....#...#.#.#
#.###.#.#.#.#.#
#S..#.....#...#
###############""",
        7036,
    ),
)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    best_score = part_one(data)

    grid: Grid[int]
    grid, start, end = data

    to_explore = PrioQueue([(0, start, 1, 0, [start])])
    seen = {}
    options = set()
    for cost, pos, dx, dy, path in to_explore:
        if cost > best_score:
            continue
        if pos == end:
            for x, y in path:
                options.add((x, y))
            continue
        if seen.get((pos, dx, dy), cost) != cost:
            continue
        seen[pos, dx, dy] = cost
        x, y = pos

        for (nx, ny), cell in grid.orthogonal_neighbours(x, y):
            if cell:
                continue
            ndx = nx - x
            ndy = ny - y
            penalty = 1
            if ndx != dx or ndy != dy:
                penalty += 1000
            to_explore.push((cost + penalty, (nx, ny), ndx, ndy, [*path, (nx, ny)]))
    return len(options)


aoc_helper.lazy_test(
    day=16,
    year=2024,
    parse=parse_raw,
    solution=part_two,
    test_data=(
        """#################
#...#...#...#..E#
#.#.#.#.#.#.#.#.#
#.#.#.#...#...#.#
#.#.#.#.###.#.#.#
#...#.#.#.....#.#
#.#.#.#.#.#####.#
#.#...#.#.#.....#
#.#.#####.#.###.#
#.#.#.......#...#
#.#.###.#####.###
#.#.#...#.....#.#
#.#.#.#####.###.#
#.#.#.........#.#
#.#.#.#########.#
#S#.............#
#################""",
        64,
    ),
)

aoc_helper.lazy_submit(day=16, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=16, year=2024, solution=part_two, data=data)
