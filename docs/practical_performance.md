<!--
    SPDX-FileCopyrightText: 2026 Alexander Metzger
    SPDX-License-Identifier: GPL-2.0-only
-->

# Practical Performance
The genus for various cage graphs using the adjacency lists from [win.tue.nl](https://www.win.tue.nl/~aeb/graphs/cages/cages.html). Number (\# links to adjacency list), valency (k), girth (g), vertices (v), edges (e), size of the automorphism group (\|G\|), genus, computation time for the genus (time), computation time for the genus using SageMath (SM time), and computation time using multi_genus.c (MG time).
\#                                              | k   | g   | v    | e     | \|G\|      | genus      | time (s) | SM time (s) | MG time (s)
----------------------------------------------- | --- | --- | ---- | ----- | ---------- | ---------- | -------- | ----------- | -----------
[1/1](../PAGE/adjacency_lists/3-3-cage.txt)     | 3   | 3   | 4    | 6     | 24         | 0          | 0.004    | 0.004       | 0.006
[1/1](../PAGE/adjacency_lists/3-4-cage.txt)     | 3   | 4   | 6    | 9     | 72         | 1          | 0.003    | 0.039       | 0.006
[1/1](../PAGE/adjacency_lists/3-5-cage.txt)     | 3   | 5   | 10   | 15    | 120        | 1          | 0.005    | 0.027       | 0.006
[1/1](../PAGE/adjacency_lists/3-6-cage.txt)     | 3   | 6   | 14   | 21    | 336        | 1          | 0.005    | 0.010       | 0.006
[1/1](../PAGE/adjacency_lists/3-7-cage.txt)     | 3   | 7   | 24   | 36    | 32         | 2          | 0.005    | 1.737       | 0.006
[1/1](../PAGE/adjacency_lists/3-8-cage.txt)     | 3   | 8   | 30   | 45    | 1440       | 4          | 0.016    | 118.958     | 0.012
[1/18](../PAGE/adjacency_lists/3-9-cage1.txt)   | 3   | 9   | 58   | 87    | 4          | 7          | 0.222    | days        | 29.084
[2/18](../PAGE/adjacency_lists/3-9-cage2.txt)   | 3   | 9   | 58   | 87    | 2          | 7          | 1.018    | days        | 30.909
[3/18](../PAGE/adjacency_lists/3-9-cage3.txt)   | 3   | 9   | 58   | 87    | 24         | 7          | 1.851    | days        | 25.993
[4/18](../PAGE/adjacency_lists/3-9-cage4.txt)   | 3   | 9   | 58   | 87    | 4          | 7          | 0.301    | days        | 54.396
[5/18](../PAGE/adjacency_lists/3-9-cage5.txt)   | 3   | 9   | 58   | 87    | 4          | 7          | 0.380    | days        | 67.89
[6/18](../PAGE/adjacency_lists/3-9-cage6.txt)   | 3   | 9   | 58   | 87    | 2          | 7          | 0.330    | days        | 45.310
[7/18](../PAGE/adjacency_lists/3-9-cage7.txt)   | 3   | 9   | 58   | 87    | 1          | 7          | 0.639    | days        | 37.257
[8/18](../PAGE/adjacency_lists/3-9-cage8.txt)   | 3   | 9   | 58   | 87    | 2          | 7          | 1.024    | days        | 42.843
[9/18](../PAGE/adjacency_lists/3-9-cage9.txt)   | 3   | 9   | 58   | 87    | 1          | 7          | 0.903    | days        | 34.437
[10/18](../PAGE/adjacency_lists/3-9-cage10.txt) | 3   | 9   | 58   | 87    | 2          | 7          | 0.215    | days        | 86.54
[11/18](../PAGE/adjacency_lists/3-9-cage11.txt) | 3   | 9   | 58   | 87    | 1          | 7          | 0.204    | days        | 54.990
[12/18](../PAGE/adjacency_lists/3-9-cage12.txt) | 3   | 9   | 58   | 87    | 2          | 7          | 1.273    | days        | 51.589
[13/18](../PAGE/adjacency_lists/3-9-cage13.txt) | 3   | 9   | 58   | 87    | 1          | 7          | 0.839    | days        | 32.340
[14/18](../PAGE/adjacency_lists/3-9-cage14.txt) | 3   | 9   | 58   | 87    | 12         | 7          | 1.056    | days        | 30.824
[15/18](../PAGE/adjacency_lists/3-9-cage15.txt) | 3   | 9   | 58   | 87    | 8          | 7          | 0.530    | days        | 44.888
[16/18](../PAGE/adjacency_lists/3-9-cage16.txt) | 3   | 9   | 58   | 87    | 2          | 7          | 0.208    | days        | 57.890
[17/18](../PAGE/adjacency_lists/3-9-cage17.txt) | 3   | 9   | 58   | 87    | 6          | 7          | 0.879    | days        | 140.50
[18/18](../PAGE/adjacency_lists/3-9-cage18.txt) | 3   | 9   | 58   | 87    | 6          | 7          | 0.849    | days        | 47.737
[1/3](../PAGE/adjacency_lists/3-10-cage1.txt)   | 3   | 10  | 70   | 105   | 120        | 9          | 0.547    | DNF         | 9354.14
[2/3](../PAGE/adjacency_lists/3-10-cage2.txt)   | 3   | 10  | 70   | 105   | 24         | 9          | 0.694    | DNF         | 9556.13
[3/3](../PAGE/adjacency_lists/3-10-cage3.txt)   | 3   | 10  | 70   | 105   | 80         | 9          | 0.418    | DNF         | 10680.89
[1/1](../PAGE/adjacency_lists/3-11-cage.txt)    | 3   | 11  | 112  | 168   | 64         | [15, 17]   | days     | DNF         | days
[1/1](../PAGE/adjacency_lists/3-12-cage.txt)    | 3   | 12  | 126  | 189   | 12096      | 17         | 0.427    | DNF         | days
[1/1](../PAGE/adjacency_lists/4-5-cage.txt)     | 4   | 5   | 19   | 38    | 24         | 4          | 0.064    | days        | 0.019
[1/1](../PAGE/adjacency_lists/4-6-cage.txt)     | 4   | 6   | 26   | 52    | 11232      | 6          | 0.016    | DNF         | 0.013
[1/?](../PAGE/adjacency_lists/4-7-cage1.txt)    | 4   | 7   | 67   | 134   | 4          | [16, 21]   | days     | DNF         | days
[1/1](../PAGE/adjacency_lists/4-8-cage.txt)     | 4   | 8   | 80   | 160   | 51840      | [21, 27]   | days     | DNF         | days
[1/?](../PAGE/adjacency_lists/4-12-cage1.txt)   | 4   | 12  | 728  | 1456  | 8491392    | [244, 363] | DNF      | DNF         | too big for bit operations
[1/4](../PAGE/adjacency_lists/5-5-cage1.txt)    | 5   | 5   | 30   | 75    | 120        | [9, 10]    | days     | DNF         | days
[2/4](../PAGE/adjacency_lists/5-5-cage2.txt)    | 5   | 5   | 30   | 75    | 20         | [9, 13]    | days     | DNF         | days
[3/4](../PAGE/adjacency_lists/5-5-cage3.txt)    | 5   | 5   | 30   | 75    | 30         | [9, 14]    | days     | DNF         | days
[4/4](../PAGE/adjacency_lists/5-5-cage4.txt)    | 5   | 5   | 30   | 75    | 96         | [9, 14]    | days     | DNF         | days
[1/1](../PAGE/adjacency_lists/5-6-cage.txt)     | 5   | 6   | 42   | 105   | 241920     | [15, 17]   | days     | DNF         | days
[1/1](../PAGE/adjacency_lists/5-8-cage.txt)     | 5   | 8   | 170  | 425   | 3916800    | [76, 126]  | DNF      | DNF         | too big for bit operations
[1/?](../PAGE/adjacency_lists/5-12-cage1.txt)   | 5   | 12  | 2730 | 6825  | 503193600  |[1480, 2048]| OOM      | DNF         | too big for bit operations
[1/1](../PAGE/adjacency_lists/6-5-cage.txt)     | 6   | 5   | 40   | 120   | 480        | [17, 22]   | days     | DNF         | days
[1/1](../PAGE/adjacency_lists/6-6-cage.txt)     | 6   | 6   | 62   | 186   | 744000     | [32, 60]   | DNF      | DNF         | DNF
[1/1](../PAGE/adjacency_lists/6-8-cage.txt)     | 6   | 8   | 312  | 936   | 9360000    | [196, 310] | DNF      | DNF         | too big for bit operations
[1/?](../PAGE/adjacency_lists/6-12-cage1.txt)   | 6   | 12  | 7812 | 23436 | 5859000000 |[5860, 7810]| OOM      | DNF         | too big for bit operations
[1/1](../PAGE/adjacency_lists/7-5-cage.txt)     | 7   | 5   | 50   | 175   | 252000     | [29, 39]   | DNF      | DNF         | DNF
[1/1](../PAGE/adjacency_lists/7-6-cage.txt)     | 7   | 6   | 90   | 315   | 15120      | [61, 110]  | DNF      | DNF         | DNF
  
The genus for various complete graphs generated using the `CompleteGraph` function in SageMath follows. 
\#                                     | k   | g   | v    | e     | \|G\|              | genus    | time (s) | SM time (s) | MG time (s)
-------------------------------------- | --- | --- | ---- | ----- | ------------------ | -------- | -------- | ----------- | -----------
[k2](../PAGE/adjacency_lists/k2.txt)   | 1   | Inf | 2    | 1     | 2                  | 0        | ---      | 0.004       | ---
[k3](../PAGE/adjacency_lists/k3.txt)   | 2   | 3   | 3    | 3     | 6                  | 0        | 0.004    | 0.004       | 0.008
[k4](../PAGE/adjacency_lists/k4.txt)   | 3   | 3   | 4    | 6     | 24                 | 0        | 0.004    | 0.003       | 0.008
[k5](../PAGE/adjacency_lists/k5.txt)   | 4   | 3   | 5    | 10    | 120                | 1        | 0.004    | 0.005       | 0.008
[k6](../PAGE/adjacency_lists/k6.txt)   | 5   | 3   | 6    | 15    | 720                | 1        | 0.004    | 0.023       | 0.008
[k7](../PAGE/adjacency_lists/k7.txt)   | 6   | 3   | 7    | 21    | 5040               | 1        | 0.004    | days        | 0.009
[k8](../PAGE/adjacency_lists/k8.txt)   | 7   | 3   | 8    | 28    | 40320              | 2        | 0.004    | DNF         | 0.008
[k9](../PAGE/adjacency_lists/k9.txt)   | 8   | 3   | 9    | 36    | 362880             | 3        | 0.004    | DNF         | 0.008

The genus for various complete bipartite graphs generated using the `CompleteBipartiteGraph` function in SageMath follows. Number (\# links to adjacency list), valency (k), girth (g), vertices (v), edges (e), size of the automorphism group (\|G\|), genus, computation time for the genus (time), and computation time for the genus using SageMath (SM time).
\#                                       | k   | g   | v    | e     | \|G\|        | genus    | time (s) | SM time (s) | MG time (s)
---------------------------------------- | --- | --- | ---- | ----- | ------------ | -------- | -------- | ----------- | -----------
[k3-3](../PAGE/adjacency_lists/k3-3.txt) | 3   | 4   | 6    | 9     | 72           | 1        | 0.004    | 0.047       | 0.006
[k4-4](../PAGE/adjacency_lists/k4-4.txt) | 4   | 4   | 8    | 16    | 1152         | 1        | 0.004    | 0.010       | 0.010
[k5-5](../PAGE/adjacency_lists/k5-5.txt) | 5   | 4   | 10   | 25    | 28800        | 3        | 0.008    | DNF         | 0.008
[k6-6](../PAGE/adjacency_lists/k6-6.txt) | 6   | 4   | 12   | 36    | 1036800      | 4        | 0.005    | DNF         | 0.009

The genus for various complete n-partite graphs generated using the `CompleteMultipartiteGraph` function in SageMath follows.
\#                                                                             | v    | e     | genus    | time (s) | MG time (s)
------------------------------------------------------------------------------ | ---- | ----- | -------- | -------- | -----------
[k2-2](../PAGE/adjacency_lists/k2-2.txt)                                       | 4    | 4     | 0        | 0.004    | 0.008
[k2-2-2](../PAGE/adjacency_lists/k2-2-2.txt)                                   | 6    | 12    | 0        | 0.004    | 0.009
[k2-2-2-2](../PAGE/adjacency_lists/k2-2-2-2.txt)                               | 8    | 24    | 1        | 0.004    | 0.009
[k2-2-2-2-2](../PAGE/adjacency_lists/k2-2-2-2-2.txt)                           | 10   | 40    | 3        | 0.006    | 0.009

The genus for various Johnson graphs generated using Mathematica follows.
\#                                                                             | v    | e     | genus      | time (s) | MG time (s)
------------------------------------------------------------------------------ | ---- | ----- | ---------- | -------- | -----------
[Johnson (5, 2)](../PAGE/adjacency_lists/Johnson5-2.txt)                       | 10   | 30    | 2          | 0.004    | 0.009
[Johnson (6, 2)](../PAGE/adjacency_lists/Johnson6-2.txt)                       | 15   | 60    | 5          | 23.101   | hours
[Johnson (6, 3)](../PAGE/adjacency_lists/Johnson6-3.txt)                       | 20   | 90    | 7          | 19.374   | hours
[Johnson (8, 4)](../PAGE/adjacency_lists/Johnson8-4.txt)                       | 70   | 560   | [60,238]   | days     | too big for bit operations
[Johnson (9, 4)](../PAGE/adjacency_lists/Johnson9-4.txt)                       | 70   | 560   | [148,558]  | days     | too big for bit operations

The genus for various Circulant graphs generated using Mathematica follows.
\#                                                                  | v    | e     | genus    | time (s) | MG time (s)
------------------------------------------------------------------- | ---- | ----- | -------- | -------- | -----------
[C10_1,2,5](../PAGE/adjacency_lists/Circulant10_1-2-5.txt)          | 10   | 25    | 1        | 0.005    | 0.007
[C10_1,2,4,5](../PAGE/adjacency_lists/Circulant10_1-2-4-5.txt)      | 10   | 35    | 3        | 0.009    | 0.023
[C14_1,2,3,6](../PAGE/adjacency_lists/Circulant14_1-2-3-6.txt)      | 14   | 48    | 4        | 0.013    | 0.896
[C15_1,5](../PAGE/adjacency_lists/Circulant15_1-5.txt)              | 15   | 30    | 1        | 0.008    | 0.006
[C16_1,7](../PAGE/adjacency_lists/Circulant16_1-7.txt)              | 16   | 32    | 1        | 0.005    | 0.014
[C18_1,3,9](../PAGE/adjacency_lists/Circulant18_1-3-9.txt)          | 18   | 45    | 4        | 0.579   | 0.021
[C20_1,3,5](../PAGE/adjacency_lists/Circulant20_1-3-5.txt)          | 20   | 60    | 6        | 0.010    | 13.698
[C20_1,6,9](../PAGE/adjacency_lists/Circulant20_1-6-9.txt)          | 20   | 60    | 6        | 0.009    | 20.637
[C21_1,4,5](../PAGE/adjacency_lists/Circulant21_1-4-5.txt)          | 21   | 63    | 1        | 0.011    | 0.008
[C26_1,3,9](../PAGE/adjacency_lists/Circulant26_1-3-9.txt)          | 26   | 78    | [8, 27]  | hours    | hours
[C30_1,9,11](../PAGE/adjacency_lists/Circulant30_1-9-11.txt)        | 30   | 90    | [9, 31]  | hours    | hours
[C30_1,4,11,14](../PAGE/adjacency_lists/Circulant30_1-4-11-14.txt)  | 30   | 120   | [16, 20] | hours    | hours
[C31_1,5,6](../PAGE/adjacency_lists/Circulant31_1-5-6.txt)          | 31   | 93    | 1        | 0.021    | 0.006
[C20_*](../PAGE/adjacency_lists/Circulant20_1-3-5-7-9-10.txt)       | 20   | 110   | [10, 17] | hours    | hours

The genus for various Cyclotomic graphs generated using Mathematica follows.
\#                                                                  | v    | e     | genus    | time (s) | MG time (s)
------------------------------------------------------------------- | ---- | ----- | -------- | -------- | -----------
[16](../PAGE/adjacency_lists/Cyclotomic16.txt)                      | 16   | 40    | 4        | 0.117    | 0.042
[19](../PAGE/adjacency_lists/Cyclotomic19.txt)                      | 19   | 57    | 1        | 0.009    | 0.010
[31](../PAGE/adjacency_lists/Cyclotomic31.txt)                      | 31   | 155   | [12,58]  | hours    | hours
[61](../PAGE/adjacency_lists/Cyclotomic61.txt)                      | 61   | 610   | [73,265] | days     | too big for bit operations
[67](../PAGE/adjacency_lists/Cyclotomic67.txt)                      | 67   | 737   | [91,325] | days     | too big for bit operations

The genus for various DifferenceSetIncidence graphs generated using Mathematica follows.
\#                                                                             | v    | e     | genus    | time (s) | MG time (s)
------------------------------------------------------------------------------ | ---- | ----- | -------- | -------- | -----------
[11,5,2](../PAGE/adjacency_lists/DifferenceSetIncidence11-5-2.txt)             | 22   | 55    | 5        | 0.914    | 1.770
[40,13,4](../PAGE/adjacency_lists/DifferenceSetIncidence40-13-4.txt)           | 80   | 520   | [91,214] | hours    | too big for bit operations

The genus for various Bipartite Kneser graphs generated using Mathematica follows.
\#                                                                             | v    | e     | genus     | time (s)                         | MG time (s)
------------------------------------------------------------------------------ | ---- | ----- | --------- | -------------------------------- | -----------
[Bipartite Kneser (6, 2)](../PAGE/adjacency_lists/bipartite-kneser6-2.txt)     | 30   | 90    | [9,28]    | days                             | days
[Bipartite Kneser (7, 2)](../PAGE/adjacency_lists/bipartite-kneser7-2.txt)     | 42   | 210   | [33,80]   | days                             | days
[Bipartite Kneser (8, 2)](../PAGE/adjacency_lists/bipartite-kneser8-2.txt)     | 56   | 420   | [78,175]  | days                             | days
[Bipartite Kneser (8, 3)](../PAGE/adjacency_lists/bipartite-kneser8-3.txt)     | 112  | 560   | [85,143]  | days                             | too big for bit operations
[Bipartite Kneser (9, 2)](../PAGE/adjacency_lists/bipartite-kneser9-2.txt)     | 72   | 756   | [154,332] | days                             | too big for bit operations
[Bipartite Kneser (9, 3)](../PAGE/adjacency_lists/bipartite-kneser9-3.txt)     | 168  | 1680  | [337,338] | days                             | too big for bit operations
[Bipartite Kneser (10, 2)](../PAGE/adjacency_lists/bipartite-kneser10-2.txt)   | 90   | 1260  | [271,572] | days                             | too big for bit operations
[Bipartite Kneser (10, 3)](../PAGE/adjacency_lists/bipartite-kneser10-3.txt)   | 240  | 4200  | [931,1963]| days                             | too big for bit operations
[Bipartite Kneser (10, 4)](../PAGE/adjacency_lists/bipartite-kneser10-4.txt)   | 420  | 3150  | [579,1358]| days                             | too big for bit operations
[Bipartite Kneser (11, 2)](../PAGE/adjacency_lists/bipartite-kneser11-2.txt)   | 110  | 1980  | [441,918] | days                             | too big for bit operations
[Bipartite Kneser (11, 3)](../PAGE/adjacency_lists/bipartite-kneser11-3.txt)   | 330  | 9240  |[2146,4428]| days                             | too big for bit operations
[Bipartite Kneser (11, 4)](../PAGE/adjacency_lists/bipartite-kneser11-4.txt)   | 660  | 11550 |[2558,5428]| days                             | too big for bit operations
[Bipartite Kneser (12, 2)](../PAGE/adjacency_lists/bipartite-kneser12-2.txt)   | 132  | 2970  | [677,1397]| days                             | too big for bit operations
[Bipartite Kneser (12, 3)](../PAGE/adjacency_lists/bipartite-kneser12-3.txt)   | 440  | 18480 |[4401,8979]| days                             | too big for bit operations
[Bipartite Kneser (12, 4)](../PAGE/adjacency_lists/bipartite-kneser12-4.txt)   | 990  | 34650 | ?         | adjacency list too large to load | too big for bit operations

The genus for various miscellaneous graphs generated using Mathematica follows.
\#                                                                             | v    | e     | genus    | time (s) | MG time (s)
------------------------------------------------------------------------------ | ---- | ----- | -------- | -------- | -----------
[Klein Bottle](../PAGE/adjacency_lists/KleinBottleTriangulation9-1.txt)        | 9    | 27    | 2        | 0.005    | 0.006
[TRC](../PAGE/adjacency_lists/TriangleReplacedCoxeterGraph.txt)                | 84   | 126   | 3        | hours    | 0.006
[Fan (3, 6)](../PAGE/adjacency_lists/Fan3-6.txt)                               | 9    | 23    | 1        | 0.004    | 0.006
[Co-Herschel](../PAGE/adjacency_lists/coHerschel.txt)                          | 11   | 37    | 2        | 0.004    | 0.006
