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

raw = aoc_helper.fetch(18, 2024)


def parse_raw(raw: str):
    return extract_ints(raw).chunked(2)


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    space = SparseGrid(bool)
    for x, y in data[:1024]:
        space[x, y] = True
    min_x, min_y, max_x, max_y = space.bounds([False])
    grid = Grid(
        list(
            [
                list(space[x, y] for x in irange(min_x, max_x))
                for y in irange(min_y, max_y)
            ]
        )
    )
    print(min_x, min_y, max_x, max_y)
    return grid.pathfind(
        (0, 0),
        (max_x, max_y),
        next_state=lambda _, x, y, from_, to: None if to else (),
        cost_function=lambda _, __: 1,
    )


aoc_helper.lazy_test(
    day=18,
    year=2024,
    parse=parse_raw,
    solution=part_one,
    test_data=(
        """5,4
4,2
4,5
3,0
2,1
6,3
2,4
1,5
0,6
3,3
2,6
5,1
1,2
5,5
2,5
6,5
1,4
0,4
6,4
1,1
6,1
1,0
0,5
1,6
2,0""",
        22,
    ),
)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    space = SparseGrid(bool)
    for x, y in data[:1024]:
        space[x, y] = True
    min_x, min_y, max_x, max_y = space.bounds([False])
    grid = Grid(
        list(
            [
                list(space[x, y] for x in irange(min_x, max_x))
                for y in irange(min_y, max_y)
            ]
        )
    )
    # binary search would be more efficient but I didn't need it
    for x, y in data[1024:]:
        grid[x, y] = True
        if (
            grid.pathfind(
                (0, 0),
                (max_x, max_y),
                next_state=lambda _, x, y, from_, to: None if to else (),
                cost_function=lambda _, __: 1,
            )
            is None
        ):
            return f"{x},{y}"


aoc_helper.lazy_test(day=18, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=18, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=18, year=2024, solution=part_two, data=data)
