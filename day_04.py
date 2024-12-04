from collections import Counter, defaultdict, deque
import re

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

raw = aoc_helper.fetch(4, 2024)


def parse_raw(raw: str):
    return Grid.from_string(raw, str)


data = parse_raw(raw)


def diagonals(grid: Grid[str]) -> list[str]:
    out = list()
    for i in range(grid.data.len()):
        d = ""
        j = 0
        while i + j < grid.data.len() and i + j < grid.data[i + j].len():
            d += grid.data[i + j][j]
            j += 1
        out.append(d)
    for x in range(1, grid.data[0].len()):
        d = ""
        j = 0
        while j < grid.data.len() and x + j < grid.data[j].len():
            d += grid.data[j][x + j]
            j += 1
        out.append(d)
    return out


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    return (
        data.data.mapped(lambda i: len(re.findall("XMAS", "".join(i)))).sum()
        + data.data.mapped(
            lambda i: len(re.findall("XMAS", "".join(i.reversed())))
        ).sum()
        + data.data.transposition()
        .mapped(lambda i: len(re.findall("XMAS", "".join(i))))
        .sum()
        + data.data.transposition()
        .mapped(lambda i: len(re.findall("XMAS", "".join(i.reversed()))))
        .sum()
        + diagonals(data).mapped(lambda i: len(re.findall("XMAS", i))).sum()
        + diagonals(data).mapped(lambda i: len(re.findall("XMAS", i[::-1]))).sum()
        + diagonals(data.rotate_clockwise())
        .mapped(lambda i: len(re.findall("XMAS", i)))
        .sum()
        + diagonals(data.rotate_clockwise())
        .mapped(lambda i: len(re.findall("XMAS", i[::-1])))
        .sum()
    )


aoc_helper.lazy_test(
    day=4,
    year=2024,
    parse=parse_raw,
    solution=part_one,
    test_data=(
        """MMMSXXMASM
MSAMXMSMSA
AMXSXMAAMM
MSAMASMSMX
XMASAMXAMM
XXAMMXXAMA
SMSMSASXSS
SAXAMASAAA
MAMMMXMMMM
MXMXAXMASX""",
        18,
    ),
)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    ans = 0
    for y in range(data.data.len()):
        for x in range(data.data[y].len()):
            if data.data[y][x] == "A":
                corners = {
                    pos: val
                    for pos, val in data.neighbours(x, y).filtered(
                        lambda i: i[0][0] != x and i[0][1] != y
                    )
                }
                # one corner is M, the opposite is S, for both corners
                if (
                    len(corners) == 4
                    and iter(corners.values()).filter("M").count() == 2
                    and iter(corners.values()).filter("S").count() == 2
                    and corners[x - 1, y - 1] != corners[x + 1, y + 1]
                ):
                    ans += 1
    return ans


aoc_helper.lazy_test(day=4, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=4, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=4, year=2024, solution=part_two, data=data)
