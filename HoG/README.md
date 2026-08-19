<!--
    SPDX-FileCopyrightText: 2026 Alexander Metzger
    SPDX-License-Identifier: GPL-2.0-only
-->

# Minimum Genus for House of Graphs

This subfolder contains a simplified C program for computing the minimum genus 
that is compatible with House of Graph formats like graph6 and multicode.

## Usage

It takes one or more graphs via stdin. Successful records are printed as
`Graph N has genus G`, followed by a summary containing the number of processed
graphs and total runtime. Per-graph errors are written to stderr, processing
continues with the next record, and the program exits nonzero if any graph
failed.

Compile with `make`, then run with `./genus < 3-8-cage.g6` 
or run directly with `make run < 3-8-cage.g6`.

Use multicode format with `./genus --multicode < 3-8-cage.mc` 
or `make run_multicode < 3-8-cage.mc`.

Since the [PAGE algorithm](../PAGE/README.md) (by myself and Austin) excels at
some graphs (particularly those with tight lower bounds or high girth) 
and [multi_genus](../MultiGenus/README.md) (by Brinkmann) excels at others, 
by default, the program races both against each other and returns the fastest 
result. To run only PAGE, use `./genus --page-only < 3-8-cage.g6` 
or `make run_page < 3-8-cage.mc`. To run only multi_genus, use 
`./genus --multi_genus-only < 3-8-cage.g6` or `make run_multi_genus < 3-8-cage.mc`.

By default, PAGE limits candidate-cycle storage to 1024 MiB and checks all
cycle-storage size arithmetic before allocation. If you have a lot of memory
available, you can change this safety limit by rebuilding with 
`make -B CC='gcc -DHOG_PAGE_MAX_CYCLE_MEMORY_MB=4096'`. Make sure you do not
set the limit higher than `SIZE_MAX / (1024 * 1024)` (so 17,592,186,044,415 on
64-bit systems and 4095 on 32-bit systems). Note that higher limits may use
several times that amount of total RAM, so it is usually safer to run in low
memory mode for large cycle sets which you can do as follows:

Use `--low-mem` to replace PAGE's materialized cycle search with its serial,
lazy facial-walk search. It avoids precomputing and storing every candidate
cycle, so it is particularly useful for large dense graphs such as bipartite
Kneser graphs. `./genus --page-only --low-mem` runs it directly, while
`./genus --low-mem` races it against MultiGenus when MultiGenus supports the
input. The low-memory engine is currently single-threaded, so `-j` does not
change its search; `--low-mem` and `--multi_genus-only` are mutually exclusive.
Unlike materialized PAGE, the lazy engine handles bridge facial walks directly.
For searches with many faces, it raises the process's soft stack limit as needed
without exceeding the operating system's hard limit. On linux, you can configure 
the hard limit using `ulimit -s`. On MacOS, you'll want to compile the program 
with a larger stack size using compiler flags, e.g., `-Wl,-stack_size,<stack_size>`.

Use `--auto-low-mem` to begin with materialized PAGE and automatically restart
with low-memory PAGE if the candidate-cycle safety limit is reached. It works
in PAGE-only mode and in the normal PAGE/MultiGenus race. It cannot be combined 
with `--low-mem` or `--multi_genus-only`. The preliminary materialized search is
discarded, so this mode can waste substantial time and memory before restarting.

The current algorithms require connected simple graphs. Disconnected inputs are
reported as unsupported rather than being assigned a misleading genus.
Materialized PAGE supports bridges by decomposing the graph into biconnected
blocks, ignoring
bridge-only blocks, computing every nontrivial block independently, and summing
their genera. This is exact by the
[Battle-Harary-Kodama-Youngs genus additivity theorem](https://doi.org/10.1090/S0002-9904-1962-10847-7).

If you want to race PAGE and multi_genus without using multiple cores, you can use
your operating system to limit the number of CPU cores:
- Linux: `taskset --cpu-list 0 ./genus -j 2 < graphs.g6` (pins to CPU 0)
- Windows: `start "" /b /wait /affinity 1 cmd /c ".\genus.exe -j 2 < graphs.g6"` (1 is a hexidecimal mask that selects CPU zero, use 2 for CPU 1, 4 for CPU 2, [and so on](https://learn.microsoft.com/en-us/windows-server/administration/windows-commands/start))
- MacOS approx: `brew install cpulimit` then `cpulimit --limit 100 -- ./genus -j 2 < graphs.g6`
- Docker: `docker run --rm -i --cpuset-cpus=0 -v "$PWD":/src -w /src gcc:14 sh -c 'make genus && exec ./genus -j 2' < graphs.g6`

This will take roughly twice as long as running with two cores (or just choosing the right algorithm with one core).

Run the test suite with `make test`.

## Performance Benchmarks

For full performance benchmarks, check [here](../docs/practical_performance.md). 
Some highlights include:

- With a 30 second compute budget, PAGE completes up to K31 where multi_genus times out on K14.
- In 37 seconds (0.7 seconds with `--low-mem`), PAGE can compute the minimum genus of the 2K edge Bipartite Kneser (11, 2) to be 441 whereas multi_genus times out.
- PAGE completes the (3, 12)-cage in less than a second whereas multi_genus takes nearly 3 hours on each (3, 10)-cage and times out on anything larger.
- multi_genus completes the Triangle Replaced Coxeter Graph in less than a second whereas PAGE takes days.

Note that PAGE is built to scale very well with the number of cores.
Use the `-j <number>` flag to run it with more CPU cores for extra tricky graphs. 
multi_genus [can also be modified to run in parallel](MultiGenus/multi_genus_parallel.c), 
but it does not work as well (yet).

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
