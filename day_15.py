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

raw = aoc_helper.fetch(15, 2024)


def parse_raw(raw: str):
    a, b = raw.split("\n\n")
    return Grid.from_string(a, lambda i: ".#O@".index(i)), "".join(b.split())


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    grid: Grid[int]
    grid, moves = data
    grid = grid.deepcopy()
    rx, ry = next(grid.find_all(3))
    grid[ry][rx] = 0
    for move in moves:
        dx, dy = {
            "^": (0, -1),
            "v": (0, 1),
            "<": (-1, 0),
            ">": (1, 0),
        }[move]
        match grid[rx + dx, ry + dy]:
            case 0:
                rx += dx
                ry += dy
            case 1:
                continue
            case 2:
                bx, by = rx + dx, ry + dy
                while grid[bx, by] == 2:
                    bx += dx
                    by += dy
                if grid[bx, by] == 1:
                    continue
                grid[by][bx] = 2
                rx += dx
                ry += dy
                grid[ry][rx] = 0
    return grid.find_all(2).map(lambda i: 100 * i[1] + i[0]).sum()


# aoc_helper.lazy_test(day=15, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    grid, moves = data
    rx, ry = next(grid.find_all(3))
    grid[ry][rx] = 0
    rx = 2 * rx
    grid = Grid[str](
        list(
            list(((".", "."), ("#", "#"), ("[", "]"))[i] for i in row).flat()
            for row in grid
        )
    )
    for move in moves:
        dx, dy = {
            "^": (0, -1),
            "v": (0, 1),
            "<": (-1, 0),
            ">": (1, 0),
        }[move]

        def can_push(bx, by):
            match grid[bx, by]:
                case "[":
                    match grid[bx + 2 * dx, by + dy]:
                        case "#":
                            return False
                        case "[" | "]":
                            if not can_push(bx + 2 * dx, by + dy):
                                return False
                    match grid[bx + dx + 1, by + dy]:
                        case "#":
                            return False
                        case "[" | "]":
                            if not can_push(bx + dx + 1, by + dy):
                                return False
                    return True
                case "]":
                    match grid[bx + 2 * dx, by + dy]:
                        case "#":
                            return False
                        case "[" | "]":
                            if not can_push(bx + 2 * dx, by + dy):
                                return False
                    match grid[bx + dx - 1, by + dy]:
                        case "#":
                            return False
                        case "[" | "]":
                            if not can_push(bx + dx - 1, by + dy):
                                return False
                    return True

        def push(bx, by):
            if not can_push(bx, by):
                raise ValueError(
                    f"Invalid push: {bx}, {by} -> {dx}, {dy} on \n{'\n'.join(''.join(row) for row in grid)}"
                )
            match grid[bx, by]:
                case "[":
                    grid[by][bx] = "."
                    grid[by][bx + 1] = "."
                    match grid[bx + 2 * dx, by + dy]:
                        case "[" | "]":
                            push(bx + 2 * dx, by + dy)
                    match grid[bx + dx + 1, by + dy]:
                        case "[" | "]":
                            push(bx + dx + 1, by + dy)
                    grid[by + dy][bx + dx] = "["
                    grid[by + dy][bx + dx + 1] = "]"
                case "]":
                    grid[by][bx] = "."
                    grid[by][bx - 1] = "."
                    match grid[bx + 2 * dx, by + dy]:
                        case "[" | "]":
                            push(bx + 2 * dx, by + dy)
                    match grid[bx + dx - 1, by + dy]:
                        case "[" | "]":
                            push(bx + dx - 1, by + dy)
                    grid[by + dy][bx + dx - 1] = "["
                    grid[by + dy][bx + dx] = "]"

        match grid[rx + dx, ry + dy]:
            case ".":
                rx += dx
                ry += dy
            case "#":
                continue
            case "[" | "]":
                bx, by = rx + dx, ry + dy
                valid = True
                while grid[bx, by] in ("[", "]"):
                    valid = can_push(bx, by)
                    if not valid:
                        break
                    bx += 2 * dx
                    by += dy
                if not valid:
                    continue
                rx += dx
                ry += dy
                push(rx, ry)
    return grid.find_all("[").map(lambda i: 100 * i[1] + i[0]).sum()


aoc_helper.lazy_test(
    day=15,
    year=2024,
    parse=parse_raw,
    solution=part_two,
    test_data=(
        """##########
#..O..O.O#
#......O.#
#.OO..O.O#
#..O@..O.#
#O#..O...#
#O..O..O.#
#.OO.O.OO#
#....O...#
##########

<vv>^<v^>v>^vv^v>v<>v^v<v<^vv<<<^><<><>>v<vvv<>^v^>^<<<><<v<<<v^vv^v>^
vvv<<^>^v^^><<>>><>^<<><^vv^^<>vvv<>><^^v>^>vv<>v<<<<v<^v>^<^^>>>^<v<v
><>vv>v^v^<>><>>>><^^>vv>v<^^^>>v^v^<^^>v^^>v^<^v>v<>>v^v^<v>v^^<^^vv<
<<v<^>>^^^^>>>v^<>vvv^><v<<<>^^^vv^<vvv>^>v<^^^^v<>^>vvvv><>>v^<<^^^^^
^><^><>>><>^^<<^^v>>><^<v>^<vv>>v>>>^v><>^v><<<<v>>v<v<v>vvv>^<><<>^><
^>><>^v<><^vvv<^^<><v<<<<<><^v<<<><<<^^<v<^^^><^>>^<v^><<<^>>^v<v^v<v^
>^>>^v>vv>^<<^v<>><<><<v<<v><>v<^vv<<<>^^v^>^^>>><<^v>>v^v><^^>>^<>vv^
<><^^>^^^<><vvvvv^v<v<<>^v<v>v<<^><<><<><<<^^<<<^<<>><<><^^^>^^<>^>v<>
^^>vv<^v^v<vv>^<><v<^v>^^^>>>^^vvv^>vvv<>>>^<^>>>>>^<<^v>^vvv<>^<><<v>
v^^>>><<^^<>>^v^<v^vv<>v^<<>^<^v^v><^<<<><<^<v><v<>vv>>v><v^<vv<>v^<<^""",
        9021,
    ),
)

aoc_helper.lazy_submit(day=15, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=15, year=2024, solution=part_two, data=data)
