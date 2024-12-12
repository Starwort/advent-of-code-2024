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
    fences = set()
    bounds = defaultdict(
        lambda: [(float("inf"), float("inf")), (float("-inf"), float("-inf"))]
    )
    kinds = set()
    for y, row in enumerate(data):
        for x, cell in enumerate(row):
            kinds.add(cell)
            bound = bounds[cell]
            bound[0] = (min(bound[0][0], x), min(bound[0][1], y))
            bound[1] = (max(bound[1][0], x), max(bound[1][1], y))
            if x == 0 or cell != row[x - 1]:
                fences.add((x - 0.5, y))
            if y == 0 or cell != data[y - 1][x]:
                fences.add((x, y - 0.5))
            if x == len(row) - 1 or cell != row[x + 1]:
                fences.add((x + 0.5, y))
            if y == len(data.data) - 1 or cell != data[y + 1][x]:
                fences.add((x, y + 0.5))
    ans = 0
    used = set()
    for cell in kinds:
        for pos in data.find_all(cell):
            if pos in used:
                continue
            area = 0
            perim = 0
            for *_, (x, y) in data.explore(
                can_move=lambda _, a, __, b: a == b, start=pos
            ):
                used.add((x, y))
                area += 1
                if (x - 0.5, y) in fences:
                    perim += 1
                if (x + 0.5, y) in fences:
                    perim += 1
                if (x, y - 0.5) in fences:
                    perim += 1
                if (x, y + 0.5) in fences:
                    perim += 1
            ans += area * perim
    return ans


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
    fences = set()
    kinds = set()
    for y, row in enumerate(data):
        for x, cell in enumerate(row):
            kinds.add(cell)
            if x == 0 or cell != row[x - 1]:
                fences.add((x - 0.5, y))
            if y == 0 or cell != data[y - 1][x]:
                fences.add((x, y - 0.5))
            if x == len(row) - 1 or cell != row[x + 1]:
                fences.add((x + 0.5, y))
            if y == len(data.data) - 1 or cell != data[y + 1][x]:
                fences.add((x, y + 0.5))
    ans = 0
    used = set()
    for cell in kinds:
        for pos in data.find_all(cell):
            if pos in used:
                continue
            # if cell == "C":
            #     print(f"{pos=}")
            verticals = {}
            horizontals = {}
            area = 0
            grid = SparseGrid(lambda: ".")
            for *_, (x, y) in data.explore(
                can_move=lambda _, a, __, b: a == b, start=pos
            ):
                grid[2 * x, 2 * y] = cell
                # if cell == "C":
                #     print(f"{x=}, {y=}")
                used.add((x, y))
                area += 1
                x2 = x
                y2 = y
                if (x - 0.5, y2) in fences:
                    y = y2
                    if x - 0.5 in verticals:
                        # print(x - 0.5, verticals[x - 0.5])
                        for wall in verticals[x - 0.5]:
                            if y in wall:
                                break
                        else:
                            wall = {y}
                            while (x - 0.5, y) in fences and data[x, y] == cell:
                                wall.add(y)
                                y += 1
                            y -= 1
                            while (x - 0.5, y) in fences and data[x, y] == cell:
                                wall.add(y)
                                y -= 1
                            verticals[x - 0.5].append(wall)
                    else:
                        wall = {y}
                        while (x - 0.5, y) in fences and data[x, y] == cell:
                            wall.add(y)
                            y += 1
                        y -= 1
                        while (x - 0.5, y) in fences and data[x, y] == cell:
                            wall.add(y)
                            y -= 1
                        verticals[x - 0.5] = [wall]
                if (x + 0.5, y2) in fences:
                    y = y2
                    if x + 0.5 in verticals:
                        # print(x + 0.5, verticals[x + 0.5])
                        for wall in verticals[x + 0.5]:
                            if y in wall:
                                break
                        else:
                            wall = {y}
                            while (x + 0.5, y) in fences and data[x, y] == cell:
                                wall.add(y)
                                y += 1
                            y -= 1
                            while (x + 0.5, y) in fences and data[x, y] == cell:
                                wall.add(y)
                                y -= 1
                            verticals[x + 0.5].append(wall)
                    else:
                        wall = {y}
                        while (x + 0.5, y) in fences and data[x, y] == cell:
                            wall.add(y)
                            y += 1
                        y -= 1
                        while (x + 0.5, y) in fences and data[x, y] == cell:
                            wall.add(y)
                            y -= 1
                        verticals[x + 0.5] = [wall]
                if (x2, y2 - 0.5) in fences:
                    x = x2
                    y = y2
                    if y - 0.5 in horizontals:
                        # print(y - 0.5, horizontals[y - 0.5])
                        for wall in horizontals[y - 0.5]:
                            if x in wall:
                                break
                        else:
                            wall = {x}
                            while (x, y - 0.5) in fences and data[x, y] == cell:
                                wall.add(x)
                                x += 1
                            x -= 1
                            while (x, y - 0.5) in fences and data[x, y] == cell:
                                wall.add(x)
                                x -= 1
                            horizontals[y - 0.5].append(wall)
                    else:
                        wall = {x}
                        while (x, y - 0.5) in fences and data[x, y] == cell:
                            wall.add(x)
                            x += 1
                        x -= 1
                        while (x, y - 0.5) in fences and data[x, y] == cell:
                            wall.add(x)
                            x -= 1
                        horizontals[y - 0.5] = [wall]
                if (x2, y2 + 0.5) in fences:
                    x = x2
                    y = y2
                    if y + 0.5 in horizontals:
                        # print(y + 0.5, horizontals[y + 0.5])
                        for wall in horizontals[y + 0.5]:
                            if x in wall:
                                break
                        else:
                            wall = {x}
                            while (x, y + 0.5) in fences and data[x, y] == cell:
                                wall.add(x)
                                x += 1
                            x -= 1
                            while (x, y + 0.5) in fences and data[x, y] == cell:
                                wall.add(x)
                                x -= 1
                            horizontals[y + 0.5].append(wall)
                    else:
                        wall = {x}
                        while (x, y + 0.5) in fences and data[x, y] == cell:
                            wall.add(x)
                            x += 1
                        x -= 1
                        while (x, y + 0.5) in fences and data[x, y] == cell:
                            wall.add(x)
                            x -= 1
                        horizontals[y + 0.5] = [wall]
            sides = sum(map(len, horizontals.values())) + sum(
                map(len, verticals.values())
            )
            for y, walls in horizontals.items():
                for wall in walls:
                    for x in wall:
                        grid[2 * x, int(2 * y)] = "-"
            for x, walls in verticals.items():
                for wall in walls:
                    for y in wall:
                        grid[int(2 * x), 2 * y] = "|"
            # grid.pretty_print(str, ["."])
            # print(f"{cell} {area} * {sides} = {area * sides}")
            ans += area * sides
    return ans


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
