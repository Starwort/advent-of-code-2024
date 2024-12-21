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


# @cache
# def solve_seq(seq: str, x=2, y=3, x2=2, y2=0):
#     if seq == "":
#         return []
#     # 789
#     # 456
#     # 123
#     #  0A
#     q = PrioQueue([(x, y, x2, y2, [])])
#     seen = set()
#     for x, y, x2, y2, presses in q:
#         if (x, y, x2, y2) in seen:
#             continue
#         seen.add((x, y))
#         if {
#             (0, 0): "7",
#             (1, 0): "8",
#             (2, 0): "9",
#             (0, 1): "4",
#             (1, 1): "5",
#             (2, 1): "6",
#             (0, 2): "1",
#             (1, 2): "2",
#             (2, 2): "3",
#             (1, 3): "0",
#             (2, 3): "A",
#         }[x, y] == seq[0]:
#             if x2 == 2 and y2 == 0:
#                 return [*presses, "A", *solve_seq(seq[1:], x, y, x2, y2)]
#             else:
#                 dx = 2 - x2
#                 return [
#                     *presses,
#                     *(">" for _ in range(dx)),
#                     *("^" for _ in range(y2)),
#                     "A",
#                     *solve_seq(seq[1:], x, y, 2, 0),
#                 ]
#         for dx, dy in ((0, 1), (0, -1), (1, 0), (-1, 0)):
#             nx, ny = x2 + dx, y2 + dy
#             if nx < 0 or ny < 0 or nx >= 3 or ny >= 2:
#                 continue
#             if nx == ny == 0:
#                 continue
#             q.push(
#                 (
#                     x,
#                     y,
#                     nx,
#                     ny,
#                     presses
#                     + [
#                         {
#                             (-1, 0): "<",
#                             (1, 0): ">",
#                             (0, -1): "^",
#                             (0, 1): "v",
#                         }[dx, dy]
#                     ],
#                 )
#             )


# def solve_seq(seq: str):
#     # 789
#     # 456
#     # 123
#     #  0A
#     x, y = 2, 3
#     x2, y2 = 2, 0
#     out = []
#     for n in seq:
#         tx, ty = {
#             "0": (1, 3),
#             "1": (0, 2),
#             "2": (1, 2),
#             "3": (2, 2),
#             "4": (0, 1),
#             "5": (1, 1),
#             "6": (2, 1),
#             "7": (0, 0),
#             "8": (1, 0),
#             "9": (2, 0),
#             "A": (2, 3),
#         }[n]
#         dx = tx - x
#         dy = ty - y
#         if dx < 0:
#             out.extend(["<", "v", "<", *("A" for _ in range(-dx))])
#             x2, y2 = 0, 1
#             x = tx
#         elif dx > 0:
#             out.extend(["v", *("A" for _ in range(dx))])
#             x2, y2 = 2, 1
#             x = tx
#         if dy < 0:
#             out.extend(
#                 [
#                     [">", "", "<"][x2],
#                     *("^" for _ in range(y2)),
#                     *("A" for _ in range(-dy)),
#                 ]
#             )
#             x2, y2 = 1, 0
#             y = ty
#         elif dy > 0:
#             out.extend(
#                 [
#                     [">", "", "<"][x2],
#                     *("v" for _ in range(1 - y2)),
#                     *("A" for _ in range(dy)),
#                 ]
#             )
#             x2, y2 = 1, 1
#             y = ty
#         out.extend([*(">" for _ in range(2 - x2)), *("^" for _ in range(y2)), "A"])
#     return out


# def best_path(x, y, dx, dy, hole=(0, 0)):
#     if hole[1] != y:
#         return [">" if dx > 0 else "<"] * abs(dx) + ["^" if dy < 0 else "v"] * abs(dy)
#     else:
#         return ["v" if dy > 0 else "^"] * abs(dy) + ["<" if dx < 0 else ">"] * abs(dx)


# def path_for_code(code):
#     x, y = 2, 3
#     path = []
#     for c in code:
#         tx, ty = {
#             "7": (0, 0),
#             "8": (1, 0),
#             "9": (2, 0),
#             "4": (0, 1),
#             "5": (1, 1),
#             "6": (2, 1),
#             "1": (0, 2),
#             "2": (1, 2),
#             "3": (2, 2),
#             "0": (1, 3),
#             "A": (2, 3),
#         }[c]
#         path.extend(best_path(x, y, tx - x, ty - y, hole=(0, 3)))
#         x, y = tx, ty
#         path.append("A")
#     return path


# def path_for_path(path):
#     x, y = 2, 0
#     out = []
#     for c in path:
#         tx, ty = {
#             "^": (1, 0),
#             "A": (2, 0),
#             "<": (0, 1),
#             "v": (1, 1),
#             ">": (2, 1),
#         }[c]
#         out.extend(best_path(x, y, tx - x, ty - y))
#         x, y = tx, ty
#         out.append("A")
#     return out


# def solve_seq(seq: str):
#     return path_for_path(path_for_path(path_for_code(seq)))


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


# def path_to(x, y, tx, ty):
#     q = PrioQueue([(0, x, y, [])])
#     for _, x, y, path in q:
#         if x == tx and y == ty:
#             return path
#         for dx, dy in ((0, 1), (0, -1), (1, 0), (-1, 0)):
#             nx, ny = x + dx, y + dy
#             if nx < 0 or ny < 0 or nx >= 3 or ny >= 2:
#                 continue
#             if nx == ny == 0:
#                 continue
#             q.push(
#                 (
#                     len(path) + 1,
#                     nx,
#                     ny,
#                     path + [{"^": "v", "v": "^", "<": ">", ">": "<"}[dx, dy]],
#                 )
#             )


# def solve_seq(seq: str):
#     x, y = 2, 3
#     x2, y2 = 2, 0
#     x3, y3 = 2, 0
#     out = []
#     for n in seq:
#         tx, ty = {
#             "0": (1, 3),
#             "1": (0, 2),
#             "2": (1, 2),
#             "3": (2, 2),
#             "4": (0, 1),
#             "5": (1, 1),
#             "6": (2, 1),
#             "7": (0, 0),
#             "8": (1, 0),
#             "9": (2, 0),
#             "A": (2, 3),
#         }[n]
#         out += path_to(x, y, tx, ty)
#         x, y = tx, ty


# def solve_seq(seq: str):
#     # 789
#     # 456
#     # 123
#     #  0A

#     #  ^A
#     # <v>

#     def next_states(s):
#         x, y, x2, y2, x3, y3, seq = s
#         for dx, dy in ((0, 1), (0, -1), (1, 0), (-1, 0)):
#             nx, ny = x3 + dx, y3 + dy
#             if nx < 0 or ny < 0 or nx >= 3 or ny >= 2:
#                 continue
#             if nx == ny == 0:
#                 continue
#             yield x, y, x2, y2, nx, ny, seq
#         match x3, y3:
#             case 1, 0:
#                 if y2 > 0:
#                     yield x, y, x2, y2 - 1, x3, y3, seq
#             case 1, 1:
#                 if y2 < 1:
#                     yield x, y, x2, y2 + 1, x3, y3, seq
#             case 2, 0:
#                 match x2, y2:
#                     case 0, 1:
#                         if x > 0:
#                             yield x - 1, y, x2, y2, x3, y3, seq
#                     case 1, 0:
#                         if y > 0:
#                             yield x, y + 1, x2, y2, x3, y3, seq
#                     case 2, 1:
#                         if x < 2:
#                             yield x + 1, y, x2, y2, x3, y3, seq
#                     case 1, 1:
#                         if y < 1:
#                             yield x, y + 1, x2, y2, x3, y3, seq
#                     case 2, 0:
#                         if {
#                             "0": (1, 3),
#                             "1": (0, 2),
#                             "2": (1, 2),
#                             "3": (2, 2),
#                             "4": (0, 1),
#                             "5": (1, 1),
#                             "6": (2, 1),
#                             "7": (0, 0),
#                             "8": (1, 0),
#                             "9": (2, 0),
#                             "A": (2, 3),
#                         }[seq[0]] == (x, y):
#                             yield x, y, x2, y2, x3, y3, seq[1:]
#             case 2, 1:
#                 if x2 < 2:
#                     yield x, y, x2 + 1, y2, x3, y3, seq
#             case 0, 1:
#                 if x2 > 0:
#                     yield x, y, x2 - 1, y2, x3, y3, seq

#     def heuristic(s):
#         x, y, x2, y2, x3, y3, seq = s
#         tx, ty = {
#             "0": (1, 3),
#             "1": (0, 2),
#             "2": (1, 2),
#             "3": (2, 2),
#             "4": (0, 1),
#             "5": (1, 1),
#             "6": (2, 1),
#             "7": (0, 0),
#             "8": (1, 0),
#             "9": (2, 0),
#             "A": (2, 3),
#         }[seq[0]]
#         dx, dy = tx - x, ty - y
#         tx2, ty2 = (
#             (0, 1)
#             if dx < 0
#             else (
#                 (2, 1) if dx > 0 else (1, 0) if dy < 0 else (1, 1) if dy > 0 else (2, 0)
#             )
#         )
#         dx2, dy2 = tx2 - x2, ty2 - y2
#         tx3, ty3 = (
#             (0, 1)
#             if dx2 < 0
#             else (
#                 (2, 1)
#                 if dx2 > 0
#                 else (1, 0) if dy2 < 0 else (1, 1) if dy2 > 0 else (2, 0)
#             )
#         )
#         dx3, dy3 = tx3 - x3, ty3 - y3
#         return (
#             4 * len(seq)
#             + 3 * abs(dx)
#             + 3 * abs(dy)
#             + 2 * abs(dx2)
#             + 2 * abs(dy2)
#             + abs(dx3)
#             + abs(dy3)
#         )

#     return search(
#         (2, 3, 2, 0, 2, 0, seq),
#         lambda s: s[-1] == "",
#         next_states,
#         heuristic=heuristic,
#     )[1]


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
