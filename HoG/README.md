<!--
    SPDX-FileCopyrightText: 2026 Alexander Metzger
    SPDX-License-Identifier: GPL-2.0-only
-->

# Minimum Genus for House of Graphs

This subfolder contains a simplified C program for computing the minimum genus that is compatible with House of Graph formats like graph6 and multicode.

## Usage

It takes the graph via stdin and outputs a single number, the minimum genus to stdout for easy parsing.

Compile with `make`, then run with `./genus < 3-8-cage.g6` or run directly with `make run < 3-8-cage.g6`. 

Use multicode format with `./genus --multicode < 3-8-cage.mc` or `make run_multicode < 3-8-cage.mc`.

Since the [PAGE algorithm](../PAGE/README.md) (by myself and Austin) excels at some graphs (particularly those with tight lower bounds or high girth) and [multi_genus](../MultiGenus/README.md) (by Brinkmann) excels at others, by default, the program races both against each other and returns the fastest result. To run only PAGE, use `./genus --page-only < 3-8-cage.g6` or `make run_page < 3-8-cage.g6`. To run only multi_genus, use `./genus --multi_genus-only < 3-8-cage.g6` or `make run_multi_genus < 3-8-cage.g6`.

## Performance Benchmarks
For full performance benchmarks, check [here](../docs/practical_performance.md). Some highlights include: 

- With a 30 second compute budget, PAGE completes up to K31 where multi_genus times out on K14.
- In 37 seconds, PAGE can compute the minimum genus of the 2K edge Bipartite Kneser (11, 2) to be 441 whereas multi_genus times out.
- PAGE completes the (3, 12)-cage in less than a second whereas multi_genus takes nearly 3 hours on each (3, 10)-cage and times out on anything larger.
- multi_genus completes the Triangle Replaced Coxeter Graph in less than a second whereas PAGE takes days.

Note that PAGE is built to scale very well with the number of cores. Use the `-j <number>` flag to run it with more CPU cores for extra tricky graphs. multi_genus [can also be modified to run in parallel](MultiGenus/multi_genus_parallel.c), but it does not work as well (yet). 

## License
This project is licensed under the terms of the **GNU General Public License v2.0** (GPLv2). 
See the [LICENSE](../LICENSE) file for the full text.

## Citation
If you use this, please cite our paper:
```bibtex
@article{Metzger_2026,
   title={An efficient genus algorithm based on graph rotations},
   volume={349},
   ISSN={0012-365X},
   url={http://doi.org/10.1016/j.disc.2026.115308},
   DOI={10.1016/j.disc.2026.115308},
   number={12},
   journal={Discrete Mathematics},
   publisher={Elsevier BV},
   author={Metzger, Alexander and Ulrigg, Austin},
   year={2026},
   month=Dec, pages={115308}
}
```
and Brinkmann's paper:
```bibtex
@article{article,
    author = {Brinkmann, Gunnar},
    year = {2022},
    month = {07},
    pages = {#P4.01},
    title = {A practical algorithm for the computation of the genus},
    volume = {22},
    journal = {Ars Mathematica Contemporanea},
    doi = {10.26493/1855-3974.2320.c2d}
}
```
