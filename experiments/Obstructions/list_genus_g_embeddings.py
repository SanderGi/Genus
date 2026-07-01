import itertools
from sage.graphs.graph_generators import graphs  # type: ignore

TARGET_GENUS = 1

# Build graph K_{3,3} + e
G = graphs.CompleteBipartiteGraph(3, 3)
G.add_edge(0, 1)
assert G.num_edges() == 10

g = G.genus()
assert (
    g <= TARGET_GENUS
), f"Cannot find rotation systems of genus {TARGET_GENUS} when graph has genus {g}"

adjacency_list = [[]] * G.num_verts()
for v in G.vertices():
    adjacency_list[v] = G.neighbors(v)

print("K_{3,3}+e adjacency list:", adjacency_list)


def calc_genus(rotation_system):
    cycles = []
    edges = set()
    for s in range(len(rotation_system)):
        for n in rotation_system[s]:
            c: list[tuple[int, int]] = []
            d: tuple[int, int] = (s, n)
            nah = False
            while d not in c:
                if d in edges:
                    nah = True
                    break
                c.append(d)
                edges.add(d)
                r = rotation_system[d[1]]
                i = r.index(d[0]) + 1
                d = (d[1], r[i % len(r)])
            if nah:
                break
            cycle = [v for v, _ in c] + [c[0][0]]
            cycles.append(cycle)
    F = len(cycles)
    V = len(rotation_system)
    E = len(edges) / 2
    return int((V - E + F - 2) / (-2))


print(f"Genus {TARGET_GENUS} Rotation Systems:")
count = 0
for permutation in itertools.product(*[range(len(l)) for l in adjacency_list]):
    rotation_system = []
    for i, s in enumerate(permutation):
        cpy = [v for v in adjacency_list[i]]
        for _ in range(s):
            cpy = cpy + [cpy.pop(0)]
        rotation_system.append(cpy)
    g = calc_genus(rotation_system)
    if g == TARGET_GENUS:
        print(rotation_system)
        count += 1
print("Count:", count)
