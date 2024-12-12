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

raw = aoc_helper.fetch(12, 2024)


def parse_raw(raw: str):
    return Grid.from_string(raw, str)


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    return data.regions().map(lambda i: len(i[0]) * i[1].mapped(len).sum()).sum()


aoc_helper.lazy_test(
    day=12,
    year=2024,
    parse=parse_raw,
    solution=part_one,
    test_data=(
        """RRRRIICCFF
RRRRIICCCF
VVRRRCCFFF
VVRCCCJFFF
VVVVCJJCFE
VVIVCCJJEE
VVIIICJJEE
MIIIIIJJEE
MIIISIJEEE
MMMISSJEEE""",
        1930,
    ),
)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    return data.regions().map_each(len).map(iter.prod).sum()


aoc_helper.lazy_test(
    day=12,
    year=2024,
    parse=parse_raw,
    solution=part_two,
    test_data=(
        """RRRRIICCFF
RRRRIICCCF
VVRRRCCFFF
VVRCCCJFFF
VVVVCJJCFE
VVIVCCJJEE
VVIIICJJEE
MIIIIIJJEE
MIIISIJEEE
MMMISSJEEE""",
        1206,
    ),
)
aoc_helper.lazy_test(
    day=12,
    year=2024,
    parse=parse_raw,
    solution=part_two,
    test_data=(
        """EEEEE
EXXXX
EEEEE
EXXXX
EEEEE""",
        236,
    ),
)
aoc_helper.lazy_test(
    day=12,
    year=2024,
    parse=parse_raw,
    solution=part_two,
    test_data=(
        """AAAAAA
AAABBA
AAABBA
ABBAAA
ABBAAA
AAAAAA""",
        368,
    ),
)

aoc_helper.lazy_submit(day=12, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=12, year=2024, solution=part_two, data=data)
