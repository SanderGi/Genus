# Ever wondered what the genus of the Balaban 10 cage is?

Unless "automorphism" and "graph cycles" are part of your daily vocabulary, you probably haven't. But if you have, the answer is 9.

These are the scripts/programs used to calculate it. I wrote the FitCycles scripts that determined the genus (based on ideas for an algorithm by [Austin](https://austinulrigg.github.io/)) and the ReverseCycle utility program to convert it into a format that the CalcCycles programs could use to check the solution. The CalcCycles programs were written by [Sam King](https://www.linkedin.com/in/samkingwa/). Austin did the main work in deciphering the math and checking the solution manually. Also credit to the rest of the recreational math group at the University of Washington for input on the programs/math and for providing computational resources for experimentation.

[![19 cycles](19Cycles.png)](19Cycles.png)

## Usage

To run the C program for ruling out genus 8 for the Balaban 10 Cage, `cd Balaban10` and run `make run`. This will compile the C program and run it. The output will be in `FitCycles.out`. To run with a different vertex labeling or set of cycles, modify `generate.ipynb` or `generate_austin.ipynb` and run the notebook to generate the input files. Then run `make run` again. To run the complete C version that doesn't require python to generate the cycles, `cd Balaban10C` and run `make run`. 

To run the python scripts you must have [SageMath installed](https://doc.sagemath.org/html/en/installation/index.html) and select the SageMath kernel in Jupyter/VS Code/whatever you use. Then run the notebooks in the Balaban10 directory.

To run the C program for any graph, `cd CalcGenus` and run `make run`. This will compile the C program and run it. The output will be in `CalcGenus.out`. To change the adjacency list, change the `ADJACENCY_LIST_FILENAME` in `CalcGenus.c` and run `make run` again. You will also need to provide said adjacency list. The format is simply the number of vertices and number of edges on the first line followed by the neighbors of each vertex on the following lines. See the examples in `CalcGenus/adjacency_lists/`.

## How it works
Read more about the mathematical graph theory context in [Pearls in Graph Theory - A Comprehensive Introduction - By Nora Hartsfield and Gerhard Ringel](https://proofits.wordpress.com/wp-content/uploads/2012/09/nora_hartsfield_gerhard_ringel_pearls_in_graph.pdf) (particularly Chapter 10). In short, the problem boils down to "fitting" as many simple directed cycles (that are not just one edge) onto the 10 Cage graph as possible. Fitting just means that together, the cycles should use each directed edge exactly once. The shortest cycle is 10 edges long (there are 528 of these counting both orientations) and there are 210 edges (counting both directions) to fit. The maximum number of fitting cycles is therefore at most 210/10 = 21 which would correspond to a genus of 8. If 19 is the maximum number of cycles that can be fit, then the genus is 9. This comes from [Euler's Formula](https://en.wikipedia.org/wiki/Euler_characteristic), F - E + V = 2 - 2g, where E is the number of edges (105), V is the number of vertices (70), g is the genus and F is the number of faces (the number of cycles we can fit also known as circuits in Chapter 10 of the book). To rule out the possibility of a genus of 8, it seems at first that you would need to check all 528 choose 21 possible combinations of 10 edge cycles which would not be feasible. However, Austin came up with a sequence of case work to show that it is impossible to fit 21 cycles. This uses the automorphisms of the graph to deduce a 10 edge cycle that must be part of a 21 cycle fitting if one exists. It then keeps adding cycles using some clever constraints to fail early (each vertex must be used exactly 3 times, if the sequence i -> j -> k occurs in a cycle it can't occur in reverse in another cycle in the fitting, etc.). This requires about 100K cases to be checked so I wrote a program to check all the cases (see the simple but inefficient algorithm [in python](Balaban10/austin_adj_no_21.ipynb) or the optimized [C implementation](Balaban10/FitCycles.c) for details).

[![Fit cycles C code run](FitCyclesRun.png)](FitCyclesRun.png)

To find an example fitting with 19 cycles, I figured out how to modify Austin's algorithm to find the maximum fitting given a range of cycle lengths (see the implementation [in python](Balaban10/austin_adj_max_fit.ipynb)). Turns out finding such an example only requires up to length 14 cycles to be checked which is feasible to compute (computing with all the cycles would take too long to finish in a realistic amount of time because they quickly grow into the hundred of thousands -- e.g. there are 75K cycles of length 20). I then wrote a script to test the solution and visualize it [in python](Balaban10/test.ipynb) and others further tested both by hand and with the Java programs in the CalcCycles directory.

For comparison, the SageMath code to find the genus of a Balaban 10 cage has been computing for a week and still hasn't finished. So this 7 second C algorithm is a significant improvement. There is also a [complete C implementation](Balaban10C/FitCycles.c) that only needs an adjacency list and can generate the cycles and other auxiliary data structures automatically.

### Extending the algorithm to any graph

This is a curious problem given it is [NP hard](https://en.wikipedia.org/wiki/Graph_embedding#Computational_complexity). For reasonably sized graphs, this algorithm easily confirms in a few seconds the genus is 4 for the Tutte-Coxeter Graph and is also 9 for the other two 10 Cages (Harries and Harries-Wong) like the Balaban 10 Cage. The extended and fully automated version of the algorithm can be found [implemented in C](CalcGenus/CalcGenus.c).

## Comparison with SageMath

In addition to being faster and scaling better (see sections on practical performance and time complexity), this algorithm also gives upper and lower bounds on the genus as it iterates. This allows stopping early if only an estimate is needed. 

### Time Complexity

Let `V` be the number of vertices and `E` the number of edges. The [current SageMath algorithm](https://github.com/sagemath/sage/blob/develop/src/sage/graphs/genus.pyx) claims `O(V \prod_{v \in V(G)} (deg(v)-1)!)` runtime. This simplifies to `O(2^V)` for 3-regular graphs, and `O(V(V-1)!^{V})` for complete graphs. 

The algorithm in this repository is roughly `O(2^(V^2 + 3V)/V^(V + 1))` for complete graphs. It has some optimizations that allows it to stop early not captured in the below analysis.

- Finding all c elementary cycles of a graph: `O((c + 1)(V + E)) = O(cV + cE)` using Johnson's algorithm
- Organizing by vertex: `O(cV)` by iterating through the cycles of length at most V
- Iterating through all cycles of length k: `O(V!/k/(V-k)!)` since this is the number of k-length cycles in a complete graph. This is worst case `O(V!/((V/2)!)^2)` which is roughly `O(2^V)`.

- Find the most used vertex to explore: `O(V)` by iterating through the vertices (overall time complexity is better when write is kept `O(1)`)
- Looking up the cycles that use a vertex: `O(1)` via hashset lookup
- Checking if a cycle is used: `O(1)` via hashset lookup
- Checking if the edges of a cycle are used: `O(e)` where `e` is the number of edges in the cycle by storing the edges used in a hashset
- Checking ijk criterion of a cycle: `O(e)` by storing the current rotation with the adjacency list
- Search iteration (f = implied fit, b = cycles by vertex >= u = unused >= a = w/ edges available >= d = ijk good): `T(f) = O(V) + O(1) + b O(1) + u O(e) + a O(e) + d T(f-1); T(0) = 0` => `O(d^f * (V + b + u e + a e)) = O(d^f * (V + b + e(u + a))) < O(b^(f + 2))`
- All search iterations (n = number of start cycles to try out < `V 2^V`): `O(b^(f + 2) * n) < O((2^V/V)^(V + 2) * V 2^V) = O(2^(V^2 + 3V)/V^(V + 1))`

Except for very small graphs, this is a significant speedup of worst case performance. See below for the theoretical scaling factors (with columns normalized to start at 1):

V  | SageMath | This Algorithm | Speedup Factor
-- | -------- | -------------- | --------------
1  | 1        | 1              | 1.0
2  | 4        | 8              | 0.5
3  | 216      | 202            | 1.1
4  | 331776   | 16384          | 20
5  | 2.5e10   | 4.4e6          | 5700
6  | 1.4e17   | 4.0e9          | 3.5e7
7  | 8.3e25   | 1.3e13         | 6.5e12
8  | 7.0e36   | 1.4e17         | 4.8e19
9  | 1.1e50   | 5.8e21         | 1.9e28
10 | 4.0e65   | 8.5e26         | 4.7e38
11 | 4.1e83   | 4.5e32         | 9.0e50
12 | 1.5e104  | 9.0e38         | 1.6e65
13 | 2.1e127  | 6.5e45         | 3.2e81
14 | 1.5e153  | 1.8e53         | 8.3e99
15 | 5.6e181  | 1.8e61         | 3.1e120
16 | 1.3e213  | 6.9e69         | 2.0e143
17 | 2.3e247  | 1.0e79         | 2.3e168
18 | 3.3e284  | 5.4e88         | 6.0e195

### Practical Performance

The genus for various cage graphs using the adjacency lists from [win.tue.nl](https://www.win.tue.nl/~aeb/graphs/cages/cages.html). Number (\# links to adjacency list), valency (k), girth (g), vertices (v), edges (e), size of the automorphism group (\|G\|), genus, computation time for the genus (time), and computation time for the genus using SageMath (SM time).

\#                                                | k   | g   | v    | e     | \|G\|      | genus      | time (s) | SM time (s)
------------------------------------------------- | --- | --- | ---- | ----- | ---------- | ---------- | -------- | -----------
[1/1](CalcGenus/adjacency_lists/3-3-cage.txt)     | 3   | 3   | 4    | 6     | 24         | 0          | 0.010    | 0.004
[1/1](CalcGenus/adjacency_lists/3-4-cage.txt)     | 3   | 4   | 6    | 9     | 72         | 1          | 0.010    | 0.039
[1/1](CalcGenus/adjacency_lists/3-5-cage.txt)     | 3   | 5   | 10   | 15    | 120        | 1          | 0.012    | 0.027
[1/1](CalcGenus/adjacency_lists/3-6-cage.txt)     | 3   | 6   | 14   | 21    | 336        | 1          | 0.014    | 0.010
[1/1](CalcGenus/adjacency_lists/3-7-cage.txt)     | 3   | 7   | 24   | 36    | 32         | 2          | 0.016    | 1.737
[1/1](CalcGenus/adjacency_lists/3-8-cage.txt)     | 3   | 8   | 30   | 45    | 1440       | 4          | 0.104    | 118.958
[1/18](CalcGenus/adjacency_lists/3-9-cage1.txt)   | 3   | 9   | 58   | 87    | 4          | 7          | 23.917   | days
[2/18](CalcGenus/adjacency_lists/3-9-cage2.txt)   | 3   | 9   | 58   | 87    | 2          | 7          | 35.163   | days
[3/18](CalcGenus/adjacency_lists/3-9-cage3.txt)   | 3   | 9   | 58   | 87    | 24         | 7          | 238.89   | days
[4/18](CalcGenus/adjacency_lists/3-9-cage4.txt)   | 3   | 9   | 58   | 87    | 4          | 7          | 32.896   | days
[5/18](CalcGenus/adjacency_lists/3-9-cage5.txt)   | 3   | 9   | 58   | 87    | 4          | 7          | 32.859   | days
[6/18](CalcGenus/adjacency_lists/3-9-cage6.txt)   | 3   | 9   | 58   | 87    | 2          | 7          | 23.305   | days
[7/18](CalcGenus/adjacency_lists/3-9-cage7.txt)   | 3   | 9   | 58   | 87    | 1          | 7          | 31.474   | days
[8/18](CalcGenus/adjacency_lists/3-9-cage8.txt)   | 3   | 9   | 58   | 87    | 2          | 7          | 32.003   | days
[9/18](CalcGenus/adjacency_lists/3-9-cage9.txt)   | 3   | 9   | 58   | 87    | 1          | 7          | 19.568   | days
[10/18](CalcGenus/adjacency_lists/3-9-cage10.txt) | 3   | 9   | 58   | 87    | 2          | 7          | 32.433   | days
[11/18](CalcGenus/adjacency_lists/3-9-cage11.txt) | 3   | 9   | 58   | 87    | 1          | 7          | 32.498   | days
[12/18](CalcGenus/adjacency_lists/3-9-cage12.txt) | 3   | 9   | 58   | 87    | 2          | 7          | 32.605   | days
[13/18](CalcGenus/adjacency_lists/3-9-cage13.txt) | 3   | 9   | 58   | 87    | 1          | 7          | 35.797   | days
[14/18](CalcGenus/adjacency_lists/3-9-cage14.txt) | 3   | 9   | 58   | 87    | 12         | 7          | 41.168   | days
[15/18](CalcGenus/adjacency_lists/3-9-cage15.txt) | 3   | 9   | 58   | 87    | 8          | 7          | 42.802   | days
[16/18](CalcGenus/adjacency_lists/3-9-cage16.txt) | 3   | 9   | 58   | 87    | 2          | 7          | 50.437   | days
[17/18](CalcGenus/adjacency_lists/3-9-cage17.txt) | 3   | 9   | 58   | 87    | 6          | 7          | 478.01   | days
[18/18](CalcGenus/adjacency_lists/3-9-cage18.txt) | 3   | 9   | 58   | 87    | 6          | 7          | 43.754   | days
[1/3](CalcGenus/adjacency_lists/3-10-cage1.txt)   | 3   | 10  | 70   | 105   | 120        | 9          | 115.72   | DNF
[2/3](CalcGenus/adjacency_lists/3-10-cage2.txt)   | 3   | 10  | 70   | 105   | 24         | 9          | 147.85   | DNF
[3/3](CalcGenus/adjacency_lists/3-10-cage3.txt)   | 3   | 10  | 70   | 105   | 80         | 9          | 129.68   | DNF
[1/1](CalcGenus/adjacency_lists/3-11-cage.txt)    | 3   | 11  | 112  | 168   | 64         | [14, 16]   | days     | DNF
[1/1](CalcGenus/adjacency_lists/3-12-cage.txt)    | 3   | 12  | 126  | 189   | 12096      | 17         | 46249.80 | DNF
[1/1](CalcGenus/adjacency_lists/4-5-cage.txt)     | 4   | 5   | 19   | 38    | 24         | 4          | 11.585   | days
[1/1](CalcGenus/adjacency_lists/4-6-cage.txt)     | 4   | 6   | 26   | 52    | 11232      | 5          | 0.011    | DNF
[1/?](CalcGenus/adjacency_lists/4-7-cage.txt)     | 4   | 7   | 67   | 134   | 4          | [16, 17]   | days     | DNF
[1/1](CalcGenus/adjacency_lists/4-8-cage.txt)     | 4   | 8   | 80   | 160   | 51840      | [21, 22]   | days     | DNF
[1/?](CalcGenus/adjacency_lists/4-12-cage.txt)    | 4   | 12  | 728  | 1456  | 8491392    | [244, 365] | DNF      | DNF
[1/4](CalcGenus/adjacency_lists/5-5-cage1.txt)    | 5   | 5   | 30   | 75    | 120        | [8, 10]    | days     | DNF
[2/4](CalcGenus/adjacency_lists/5-5-cage2.txt)    | 5   | 5   | 30   | 75    | 20         | [8, 13]    | days     | DNF
[3/4](CalcGenus/adjacency_lists/5-5-cage3.txt)    | 5   | 5   | 30   | 75    | 30         | [8, 14]    | days     | DNF
[4/4](CalcGenus/adjacency_lists/5-5-cage4.txt)    | 5   | 5   | 30   | 75    | 96         | [8, 14]    | days     | DNF
[1/1](CalcGenus/adjacency_lists/5-6-cage.txt)     | 5   | 6   | 42   | 105   | 241920     | [15, 16]   | days     | DNF
[1/1](CalcGenus/adjacency_lists/5-8-cage.txt)     | 5   | 8   | 170  | 425   | 3916800    | [75, 90]   | DNF      | DNF
[1/?](CalcGenus/adjacency_lists/5-12-cage.txt)    | 5   | 12  | 2730 | 6825  | 503193600  |[1480, 2048]| OOM      | DNF
[1/1](CalcGenus/adjacency_lists/6-5-cage.txt)     | 6   | 5   | 40   | 120   | 480        | [17, 22]   | days     | DNF
[1/1](CalcGenus/adjacency_lists/6-6-cage.txt)     | 6   | 6   | 62   | 186   | 744000     | [32, 34]   | DNF      | DNF
[1/1](CalcGenus/adjacency_lists/6-8-cage.txt)     | 6   | 8   | 312  | 936   | 9360000    | [196, 222] | DNF      | DNF
[1/?](CalcGenus/adjacency_lists/6-12-cage.txt)    | 6   | 12  | 7812 | 23436 | 5859000000 |[5860, 7813]| OOM      | DNF
[1/1](CalcGenus/adjacency_lists/7-5-cage.txt)     | 7   | 5   | 50   | 175   | 252000     | [28, 34]   | DNF      | DNF
[1/1](CalcGenus/adjacency_lists/7-6-cage.txt)     | 7   | 6   | 90   | 315   | 15120      | [61, 67]   | DNF      | DNF
  
The genus for various complete graphs generated using the `CompleteGraph` function in SageMath follows. Number (\# links to adjacency list), valency (k), girth (g), vertices (v), edges (e), size of the automorphism group (\|G\|), genus, computation time for the genus (time), and computation time for the genus using SageMath (SM time).

\#                                       | k   | g   | v    | e     | \|G\|              | genus    | time (s) | SM time (s)
---------------------------------------- | --- | --- | ---- | ----- | ------------------ | -------- | -------- | -----------
[k2](CalcGenus/adjacency_lists/k2.txt)   | 1   | Inf | 2    | 1     | 2                  | 0        | ---      | 0.004
[k3](CalcGenus/adjacency_lists/k3.txt)   | 2   | 3   | 3    | 3     | 6                  | 0        | 0.008    | 0.004
[k4](CalcGenus/adjacency_lists/k4.txt)   | 3   | 3   | 4    | 6     | 24                 | 0        | 0.008    | 0.003
[k5](CalcGenus/adjacency_lists/k5.txt)   | 4   | 3   | 5    | 10    | 120                | 1        | 0.008    | 0.005
[k6](CalcGenus/adjacency_lists/k6.txt)   | 5   | 3   | 6    | 15    | 720                | 1        | 0.008    | 0.023
[k7](CalcGenus/adjacency_lists/k7.txt)   | 6   | 3   | 7    | 21    | 5040               | 1        | 0.020    | days
[k8](CalcGenus/adjacency_lists/k8.txt)   | 7   | 3   | 8    | 28    | 40320              | 2        | 18.079   | DNF
[k9](CalcGenus/adjacency_lists/k9.txt)   | 8   | 3   | 9    | 36    | 362880             | 3        | days     | DNF

The genus for various complete bipartite graphs generated using the `CompleteBipartiteGraph` function in SageMath follows. Number (\# links to adjacency list), valency (k), girth (g), vertices (v), edges (e), size of the automorphism group (\|G\|), genus, computation time for the genus (time), and computation time for the genus using SageMath (SM time).

\#                                         | k   | g   | v    | e     | \|G\|        | genus    | time (s) | SM time (s)
------------------------------------------ | --- | --- | ---- | ----- | ------------ | -------- | -------- | -----------
[k3-3](CalcGenus/adjacency_lists/k3-3.txt) | 3   | 4   | 6    | 9     | 72           | 1        | 0.010    | 0.047
[k4-4](CalcGenus/adjacency_lists/k4-4.txt) | 4   | 4   | 8    | 16    | 1152         | 1        | 0.012    | 0.010
[k5-5](CalcGenus/adjacency_lists/k5-5.txt) | 5   | 4   | 10   | 25    | 28800        | 3        | 111.48   | DNF
[k6-6](CalcGenus/adjacency_lists/k6-6.txt) | 6   | 4   | 12   | 36    | 1036800      | 4        | 0.014    | DNF
