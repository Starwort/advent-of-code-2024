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

raw = aoc_helper.fetch(9, 2024)


def parse_raw(raw: str):
    return list(raw).mapped(int)


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    blocks = list()
    for kind, file in data.enumerated():
        if kind % 2 == 0:
            blocks.extend(kind // 2 for _ in range(file))
        else:
            blocks.extend(-1 for _ in range(file))
    while -1 in blocks:
        block = blocks.pop()
        blocks[blocks.index(-1)] = block
    return blocks.enumerated().mapped(lambda i: i[0] * i[1]).sum()


aoc_helper.lazy_test(day=9, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
# def part_two(data=data):
#     blocks = list()
#     data = data.enumerated().mapped(lambda i: (i[0] // 2, i[1], i[0] % 2 == 0))
#     pos = 0
#     for id, len, is_file in data:
#         if is_file:
#             blocks.append((pos, id, len))
#         pos += len
#     for id in data.mapped(lambda i: i[1]).reversed():
#         i, (pos, _, len) = blocks.enumerated().find(lambda i: i[1][1] == id)
#         last_pos2 = 0
#         for j, (pos2, _, len2) in blocks[:i].enumerated():
#             if pos2 - last_pos2 >= len:
#                 blocks.pop(i)
#                 blocks.insert(j, (last_pos2, id, len))
#                 break
#             last_pos2 = pos2 + len2
#     print(blocks)
#     return blocks.mapped(
#         lambda i: range(i[0], i[0] + i[2]).map(lambda j: j * i[1]).sum()
#     ).sum()


def part_two(data=data):
    blocks = list()
    for kind, file in data.enumerated():
        if kind % 2 == 0:
            blocks.extend(kind // 2 for _ in range(file))
        else:
            blocks.extend(-1 for _ in range(file))
    ids = set(blocks) - {-1}
    for id in sorted(ids, reverse=True):
        first = blocks.index(id)
        len = 1
        while first + len < blocks.len() and blocks[first + len] == id:
            len += 1
        for i, _ in blocks.enumerated().filtered(lambda i: i[1] == -1):
            if i > first:
                break
            if blocks[i : i + len].all(lambda i: i == -1):
                blocks[first : first + len] = [-1] * len
                blocks[i : i + len] = [id] * len
                break
        else:
            blocks.extend(id for _ in range(len))
            break
    return (
        blocks.enumerated()
        .filtered(lambda i: i[1] != -1)
        .mapped(lambda i: i[0] * i[1])
        .sum()
    )


aoc_helper.lazy_test(day=9, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=9, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=9, year=2024, solution=part_two, data=data)
