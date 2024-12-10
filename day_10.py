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


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    ans = 0
    for head in data.find_all(SparseGrid.from_string("0", int)):
        reachable = set()
        seen = set()
        q = deque([(head, 0)])
        while q:
            pos, cell = q.popleft()
            if cell == 9:
                reachable.add(pos)
            if pos in seen:
                continue
            seen.add(pos)
            for npos, ncell in data.orthogonal_neighbours(*pos):
                if ncell == cell + 1:
                    q.append((npos, ncell))
        ans += len(reachable)
    return ans


# aoc_helper.lazy_test(day=10, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    ans = 0
    for head in data.find_all(SparseGrid.from_string("0", int)):
        trails = set()
        q = deque([(head, 0, tuple[tuple[int, int], ...]())])
        while q:
            pos, cell, path = q.popleft()
            if cell == 9:
                trails.add(path)
            for npos, ncell in data.orthogonal_neighbours(*pos):
                if ncell == cell + 1:
                    q.append((npos, ncell, (*path, npos)))
        ans += len(trails)
    return ans


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
