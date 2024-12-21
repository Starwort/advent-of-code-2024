from collections import Counter, defaultdict, deque
from functools import cache
from math import prod

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

raw = aoc_helper.fetch(21, 2024)


def parse_raw(raw: str):
    return list(raw.splitlines())


data = parse_raw(raw)


@cache
def path(seq: str, depth=0, max_depth=2):
    def visits(x, y, moves, hole):
        for m in moves:
            if (x, y) == hole:
                return True
            match m:
                case "^":
                    y -= 1
                case "v":
                    y += 1
                case "<":
                    x -= 1
                case ">":
                    x += 1
        return (x, y) == hole

    def move_options(x, y, tx, ty, hole):
        dx, dy = tx - x, ty - y
        moves = ["v" if dy > 0 else "^"] * abs(dy) + ["<" if dx < 0 else ">"] * abs(dx)
        out = list(set(list(moves).permutations())).filtered(
            lambda i: not visits(x, y, i, hole)
        ).mapped(lambda i: "".join(i) + "a") or list("a")
        return out

    out = 0
    x, y = (2, 3) if depth == 0 else (2, 0)
    for i in seq:
        tx, ty = {
            "7": (0, 0),
            "8": (1, 0),
            "9": (2, 0),
            "4": (0, 1),
            "5": (1, 1),
            "6": (2, 1),
            "1": (0, 2),
            "2": (1, 2),
            "3": (2, 2),
            "0": (1, 3),
            "A": (2, 3),
            #
            "^": (1, 0),
            "a": (2, 0),
            "<": (0, 1),
            "v": (1, 1),
            ">": (2, 1),
        }[i]
        options = move_options(x, y, tx, ty, (0, 3) if depth == 0 else (0, 0))
        if depth == max_depth:
            out += len(options[0])
        else:
            out += options.mapped(lambda i: path(i, depth + 1, max_depth)).min()
        x, y = tx, ty
    return out


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    return data.mapped(lambda i: (path(i) * int(i[:-1]))).sum()


aoc_helper.lazy_test(day=21, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    return data.mapped(lambda i: (path(i, max_depth=25) * int(i[:-1]))).sum()


aoc_helper.lazy_test(day=21, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=21, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=21, year=2024, solution=part_two, data=data)
