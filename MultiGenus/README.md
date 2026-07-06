<!--
    SPDX-FileCopyrightText: 2026 Alexander Metzger
    SPDX-License-Identifier: GPL-2.0-only
-->

# Multi Genus
The original code in this subfolder has been written by [Gunnar Brinkmann](https://research.ugent.be/web/person/gunnar-brinkmann-0/en)
and is included under a GPLv2 license with permission.

If you use this code, make sure to cite Brinkmann's genus computation paper (for multi_genus):
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

And his graph drawing paper (for planar_draw): 
```bibtex
@misc{brinkmann2025drawingmapsorientedsurfaces,
    title={Drawing maps on oriented surfaces}, 
    author={Gunnar Brinkmann},
    year={2025},
    eprint={2505.01480},
    archivePrefix={arXiv},
    primaryClass={cs.CG},
    url={https://arxiv.org/abs/2505.01480}, 
}
```

The code has been modified for bundling as a python package and to support extra features such as 3D drawings. If you use those, please also cite this repository:
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
 
You can find Brinkmann's original code [here](https://caagt.ugent.be/cubic-bip-nonham/).

## Usage
To use the version included in this repository, use `make run ADJ=graphs/k3-3.mc` to run the algorithm and `make draw ADJ=graphs/k3-3.mc` to also generate a LaTeX visualization of the embedding. Optionally, you can run an experimental multi-threaded version with `make run_parallel ADJ=graphs/k3-3.mc` though it is not yet faster for all graphs since it depends heavily on the choice of `MULTI_GENUS_SPLIT_DEPTH` due to multi_genus not being built for per-graph parallelism like PAGE. This algorithm is better used for computing many graphs in parallel. 

You can read more about the multi code binary graph format on [House of Graphs](https://houseofgraphs.org/help) under supported graph formats.

## License
This project is licensed under the terms of the **GNU General Public License v2.0** (GPLv2). 
See the [LICENSE](../LICENSE) file for the full text.
