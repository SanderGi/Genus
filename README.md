# Ever wondered what the genus of the Balaban 10 cage is?

Unless "automorphism" and "graph cycles" are part of your daily vocabulary, you probably haven't. But if you have, the answer is 9.

These are the scripts/programs used to calculate it. I wrote the FitCycles scripts that determined the genus (based on ideas for an algorithm by [Austin](https://austinulrigg.github.io/)) and the ReverseCycle utility program to convert it into a format that the CalcCycles programs could use to check the solution. The CalcCycles programs were written by [Sam King](https://www.linkedin.com/in/samkingwa/). Austin did the main work in deciphering the math and checking the solution manually. Also credit to the rest of the recreational math group at the University of Washington for input on the programs/math and for providing computational resources for experimentation.

[![19 cycles](19Cycles.png)](19Cycles.png)

## How it works
Read more about the mathematical graph theory context in [Pearls in Graph Theory - A Comprehensive Introduction - By Nora Hartsfield and Gerhard Ringel](https://proofits.wordpress.com/wp-content/uploads/2012/09/nora_hartsfield_gerhard_ringel_pearls_in_graph.pdf) (particularly Chapter 10). In short, the problem boils down to "fitting" as many simple directed cycles (that are not just one edge) onto the 10 Cage graph as possible. Fitting just means that together, the cycles should use each directed edge exactly once. The shortest cycle is 10 edges long (there are 528 of these counting both orientations) and there are 210 edges (counting both directions) to fit. The maximum number of fitting cycles is therefore at most 210/10 = 21 which would correspond to a genus of 8. If 19 is the maximum number of cycles that can be fit, then the genus is 9. This comes from [Euler's Formula](https://en.wikipedia.org/wiki/Euler_characteristic), F - E + V = 2 - 2g, where E is the number of edges (105), V is the number of vertices (70), g is the genus and F is the number of faces (the number of cycles we can fit also known as circuits in Chapter 10 of the book). To rule out the possibility of a genus of 8, it seems at first that you would need to check all 528 choose 21 possible combinations of 10 edge cycles which would not be feasible. However, Austin came up with a sequence of case work to show that it is impossible to fit 21 cycles. This uses the automorphisms of the graph to deduce a 10 edge cycle that must be part of a 21 cycle fitting if one exists. It then keeps adding cycles using some clever constraints to fail early (each vertex must be used exactly 3 times, if the sequence i -> j -> k occurs in a cycle it can't occur in reverse in another cycle in the fitting, etc.). This requires about 100K cases to be checked so I wrote a program to check all the cases (see the simple but inefficient algorithm [in python](Balaban10/austin_adj_no_21.ipynb) or the optimized [C implementation](Balaban10/FitCycles.c) for details).

[![Fit cycles C code run](FitCyclesRun.png)](FitCyclesRun.png)

To find an example fitting with 19 cycles, I figured out how to modify Austin's algorithm to find the maximum fitting given a range of cycle lengths (see the implementation [in python](Balaban10/austin_adj_max_fit.ipynb)). Turns out finding such an example only requires up to length 14 cycles to be checked which is feasible to compute (computing with all the cycles would take too long to finish in a realistic amount of time because they quickly grow into the hundred of thousands -- e.g. there are 75K cycles of length 20). I then wrote a script to test the solution and visualize it [in python](Balaban10/test.ipynb) and others further tested both by hand and with the Java programs in the CalcCycles directory.

For comparison, the SageMath code to find the genus of a Balaban 10 cage has been computing for a week and still hasn't finished. So this 7 second C algorithm is a significant improvement. There is also a [complete C implementation](Balaban10C/FitCycles.c) that only needs an adjacency list and can generate the cycles and other auxiliary data structures automatically.

## Extending the algorithm to any graph

This is a curious problem given it is [NP hard](https://en.wikipedia.org/wiki/Graph_embedding#Computational_complexity). For reasonably sized graphs, this algorithm easily confirms in a few seconds the genus is 4 for the Tutte-Coxeter Graph and is also 9 for the other two 10 Cages (Harries and Harries-Wong) like the Balaban 10 Cage. The extended and fully automated version of the algorithm can be found [implemented in C](CalcGenus/CalcGenus.c).

## How to run

To run the C program for ruling out genus 8 for the Balaban 10 Cage, `cd Balaban10` and run `make run`. This will compile the C program and run it. The output will be in `FitCycles.out`. To run with a different vertex labeling or set of cycles, modify `generate.ipynb` or `generate_austin.ipynb` and run the notebook to generate the input files. Then run `make run` again. To run the complete C version that doesn't require python to generate the cycles, `cd Balaban10C` and run `make run`. 

To run the python scripts you must have [SageMath installed](https://doc.sagemath.org/html/en/installation/index.html) and select the SageMath kernel in Jupyter/VS Code/whatever you use. Then run the notebooks in the Balaban10 directory.

To run the C program for any graph, `cd CalcGenus` and run `make run`. This will compile the C program and run it. The output will be in `CalcGenus.out`. To change the adjacency list, change the `ADJACENCY_LIST_FILENAME` in `CalcGenus.c` and run `make run` again. You will also need to provide said adjacency list. The format is simply the number of vertices and number of edges on the first line followed by the neighbors of each vertex on the following lines. See the examples in `CalcGenus/adjacency_lists/`.

## Result Table
The genus for various cage graphs using the adjacency lists from [win.tue.nl](https://www.win.tue.nl/~aeb/graphs/cages/cages.html). Number (\# links to adjacency list), valency (k), girth (g), vertices (v), edges (e), size of the automorphism group (\|G\|), and genus.

\#                                              | k   | g   | v    | e     | \|G\|      | genus 
----------------------------------------------- | --- | --- | ---- | ----- | ---------- | -----
[1/1](CalcGenus/adjacency_lists/3-3-cage.txt)   | 3   | 3   | 4    | 6     | 24         | 0
[1/1](CalcGenus/adjacency_lists/3-4-cage.txt)   | 3   | 4   | 6    | 9     | 72         | 1
[1/1](CalcGenus/adjacency_lists/3-5-cage.txt)   | 3   | 5   | 10   | 15    | 120        | 1
[1/1](CalcGenus/adjacency_lists/3-6-cage.txt)   | 3   | 6   | 14   | 21    | 336        | 1
[1/1](CalcGenus/adjacency_lists/3-7-cage.txt)   | 3   | 7   | 24   | 36    | 32         | 2
[1/1](CalcGenus/adjacency_lists/3-8-cage.txt)   | 3   | 8   | 30   | 45    | 1440       | 4
[1/18](CalcGenus/adjacency_lists/3-9-cage.txt)  | 3   | 9   | 58   | 87    | 4          | 7
[2/18](CalcGenus/adjacency_lists/3-9-cage.txt)  | 3   | 9   | 58   | 87    | 2          | 7
[3/18](CalcGenus/adjacency_lists/3-9-cage.txt)  | 3   | 9   | 58   | 87    | 24         | 7
[4/18](CalcGenus/adjacency_lists/3-9-cage.txt)  | 3   | 9   | 58   | 87    | 4          | 7
[5/18](CalcGenus/adjacency_lists/3-9-cage.txt)  | 3   | 9   | 58   | 87    | 4          | 7
[6/18](CalcGenus/adjacency_lists/3-9-cage.txt)  | 3   | 9   | 58   | 87    | 2          | 7
[7/18](CalcGenus/adjacency_lists/3-9-cage.txt)  | 3   | 9   | 58   | 87    | 1          | 7
[8/18](CalcGenus/adjacency_lists/3-9-cage.txt)  | 3   | 9   | 58   | 87    | 2          | 7
[9/18](CalcGenus/adjacency_lists/3-9-cage.txt)  | 3   | 9   | 58   | 87    | 1          | 7
[10/18](CalcGenus/adjacency_lists/3-9-cage.txt) | 3   | 9   | 58   | 87    | 2          | 7
[11/18](CalcGenus/adjacency_lists/3-9-cage.txt) | 3   | 9   | 58   | 87    | 1          | 7
[12/18](CalcGenus/adjacency_lists/3-9-cage.txt) | 3   | 9   | 58   | 87    | 2          | 7
[13/18](CalcGenus/adjacency_lists/3-9-cage.txt) | 3   | 9   | 58   | 87    | 1          | 7
[14/18](CalcGenus/adjacency_lists/3-9-cage.txt) | 3   | 9   | 58   | 87    | 12         | 7
[15/18](CalcGenus/adjacency_lists/3-9-cage.txt) | 3   | 9   | 58   | 87    | 8          | 7
[16/18](CalcGenus/adjacency_lists/3-9-cage.txt) | 3   | 9   | 58   | 87    | 2          | 7
[17/18](CalcGenus/adjacency_lists/3-9-cage.txt) | 3   | 9   | 58   | 87    | 6          | 7
[18/18](CalcGenus/adjacency_lists/3-9-cage.txt) | 3   | 9   | 58   | 87    | 6          | 7
[1/3](CalcGenus/adjacency_lists/3-10-cage1.txt) | 3   | 10  | 70   | 105   | 120        | 9
[2/3](CalcGenus/adjacency_lists/3-10-cage2.txt) | 3   | 10  | 70   | 105   | 24         | 9
[3/3](CalcGenus/adjacency_lists/3-10-cage3.txt) | 3   | 10  | 70   | 105   | 80         | 9
[1/1](CalcGenus/adjacency_lists/3-11-cage.txt)  | 3   | 11  | 112  | 168   | 64         | [14, 18]
[1/1](CalcGenus/adjacency_lists/3-12-cage.txt)  | 3   | 12  | 126  | 189   | 12096      | [17, 32]
[1/1](CalcGenus/adjacency_lists/4-5-cage.txt)   | 4   | 5   | 19   | 38    | 24         | -----
[1/1](CalcGenus/adjacency_lists/4-6-cage.txt)   | 4   | 6   | 26   | 52    | 11232      | -----
[1/?](CalcGenus/adjacency_lists/4-7-cage.txt)   | 4   | 7   | 67   | 134   | 4          | -----
[1/1](CalcGenus/adjacency_lists/4-8-cage.txt)   | 4   | 8   | 80   | 160   | 51840      | -----
[1/?](CalcGenus/adjacency_lists/4-12-cage.txt)  | 4   | 12  | 728  | 1456  | 8491392    | -----
[1/4](CalcGenus/adjacency_lists/5-5-cage1.txt)  | 5   | 5   | 30   | 75    | 120        | -----
[2/4](CalcGenus/adjacency_lists/5-5-cage2.txt)  | 5   | 5   | 30   | 75    | 20         | -----
[3/4](CalcGenus/adjacency_lists/5-5-cage3.txt)  | 5   | 5   | 30   | 75    | 30         | -----
[4/4](CalcGenus/adjacency_lists/5-5-cage4.txt)  | 5   | 5   | 30   | 75    | 96         | -----
[1/1](CalcGenus/adjacency_lists/5-6-cage.txt)   | 5   | 6   | 42   | 105   | 241920     | -----
[1/1](CalcGenus/adjacency_lists/5-8-cage.txt)   | 5   | 8   | 170  | 425   | 3916800    | -----
[1/?](CalcGenus/adjacency_lists/5-12-cage.txt)  | 5   | 12  | 2730 | 6825  | 503193600  | -----
[1/1](CalcGenus/adjacency_lists/6-5-cage.txt)   | 6   | 5   | 40   | 120   | 480        | -----
[1/1](CalcGenus/adjacency_lists/6-6-cage.txt)   | 6   | 6   | 62   | 186   | 744000     | -----
[1/1](CalcGenus/adjacency_lists/6-8-cage.txt)   | 6   | 8   | 312  | 936   | 9360000    | -----
[1/?](CalcGenus/adjacency_lists/6-12-cage.txt)  | 6   | 12  | 7812 | 23436 | 5859000000 | -----
[1/1](CalcGenus/adjacency_lists/7-5-cage.txt)   | 7   | 5   | 50   | 175   | 252000     | -----
[1/1](CalcGenus/adjacency_lists/7-6-cage.txt)   | 7   | 6   | 90   | 315   | 15120      | -----
