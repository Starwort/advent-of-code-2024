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

raw = aoc_helper.fetch(10, 2024)


def parse_raw(raw: str):
    return Grid.from_string(raw)


data = parse_raw(raw)


def solve_part(data: Grid[int], is_part_2: bool):
    return (
        data.find_all(0)
        .map(
            lambda head: data.explore(
                can_move=lambda _, from_cell, __, to_cell: to_cell == from_cell + 1,
                start=head,
                return_path_when=lambda _, cell: cell == 9,
                unique_paths=is_part_2,
            ).count()
        )
        .sum()
    )


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    return solve_part(data, False)


# aoc_helper.lazy_test(day=10, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    return solve_part(data, True)


aoc_helper.lazy_test(
    day=10,
    year=2024,
    parse=parse_raw,
    solution=part_two,
    test_data=(
        """####.0#
##4321#
##5##2#
##6543#
##7##4#
##8765#
##9####""",
        3,
    ),
    #     test_data=(
    #         """89010123
    # 78121874
    # 87430965
    # 96549874
    # 45678903
    # 32019012
    # 01329801
    # 10456732""",
    #         81,
    #     ),
)

aoc_helper.lazy_submit(day=10, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=10, year=2024, solution=part_two, data=data)
