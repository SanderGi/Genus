import sys
import math
import itertools


def bipartite_kneser(n, k):
    """
    Generates the adjacency list for the Bipartite Kneser graph H(n, k)
    using numbered integers (0 to V-1) instead of subset tuples.
    """
    if k > n // 2:
        raise ValueError("k must be less than or equal to n/2")

    ground_set = set(range(n))

    # 1. Generate all tuple vertices for both partitions
    part_A = list(itertools.combinations(range(n), k))
    part_B = list(itertools.combinations(range(n), n - k))
    all_tuples = part_A + part_B

    # 2. Map every tuple to a unique sequential integer index
    tuple_to_id = {t: i for i, t in enumerate(all_tuples)}

    # Initialize the numbered adjacency list
    adj_list = {i: [] for i in range(len(all_tuples))}

    # How many extra elements we need to expand a k-subset to an (n-k)-subset
    needed_extra_elements = (n - k) - k

    # 3. Mathematically construct the edges and map them to their integer IDs
    for a in part_A:
        remaining = list(ground_set - set(a))
        a_id = tuple_to_id[a]

        for extra in itertools.combinations(remaining, needed_extra_elements):
            b = tuple(sorted(a + extra))
            b_id = tuple_to_id[b]

            # Map the bi-directional edge using integer IDs
            adj_list[a_id].append(b_id)
            adj_list[b_id].append(a_id)

    return adj_list


N = int(sys.argv[1])
K = int(sys.argv[2])
V = 2 * math.comb(N, K)
DEG = math.comb(N - K, (N - K) - K)
E = math.comb(N, K) * DEG
print(f"DEG={DEG}")
with open(f"./adjacency_lists/bipartite-kneser{N}-{K}.txt", "a") as f:
    print(f"{V} {E}", file=f)
    for v, neigh in bipartite_kneser(N, K).items():
        print(" ".join(map(lambda x: str(x + 1), neigh)), file=f)
