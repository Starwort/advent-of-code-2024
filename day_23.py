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

raw = aoc_helper.fetch(23, 2024)


def parse_raw(raw: str):
    return list(raw.splitlines()).mapped(lambda i: list(i.split("-")))


data = parse_raw(raw)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_one(data=data):
    all_connections = {}
    for computer in set(data.flat()):
        connections = set()
        for a, b in data:
            if a == computer:
                connections.add(b)
            if b == computer:
                connections.add(a)
        all_connections[computer] = connections
    groups = set()
    for computer, others in all_connections.items():
        for other in others:
            for last in others & all_connections[other]:
                groups.add(frozenset([computer, other, last]))
    return iter(groups).filter(lambda i: any(j[0] == "t" for j in i)).count()


aoc_helper.lazy_test(day=23, year=2024, parse=parse_raw, solution=part_one)


# providing this default is somewhat of a hack - there isn't any other way to
# force type inference to happen, AFAIK - but this won't work with standard
# collections (list, set, dict, tuple)
def part_two(data=data):
    all_connections = {}
    for computer in set(data.flat()):
        connections = set()
        for a, b in data:
            if a == computer:
                connections.add(b)
            if b == computer:
                connections.add(a)
        all_connections[computer] = connections
    groups = set()
    for computer, others in all_connections.items():
        for other in others:
            rest_of_eligible_group = others & all_connections[other]
            group = frozenset([computer, other]) | rest_of_eligible_group
            for i in rest_of_eligible_group:
                if i in group:
                    group &= {i} | all_connections[i]
            groups.add(group)
    return ",".join(sorted(iter(groups).max(len)))


aoc_helper.lazy_test(day=23, year=2024, parse=parse_raw, solution=part_two)

aoc_helper.lazy_submit(day=23, year=2024, solution=part_one, data=data)
aoc_helper.lazy_submit(day=23, year=2024, solution=part_two, data=data)
