<!--
    SPDX-FileCopyrightText: 2026 Alexander Metzger
    SPDX-License-Identifier: GPL-2.0-only
-->

<p align="center">
  <img src="https://github.com/SanderGi/Genus/blob/main/app/static/apple-touch-icon.png?raw=true" alt="K3,3 embedding: logo for graph genus repo" width="120">
</p>

# Graph Genus
[![DOI](https://img.shields.io/badge/DOI-10.1016/j.disc.2026.115308-blue)](http://doi.org/10.1016/j.disc.2026.115308)
[![arXiv](https://img.shields.io/badge/arXiv-2411.07347-b31b1b.svg)](https://arxiv.org/abs/2411.07347)
![PyPI Version](https://img.shields.io/pypi/v/graph-genus)
[![maintenance-status](https://img.shields.io/badge/maintenance-actively--developed-brightgreen.svg)](https://gist.github.com/taiki-e/ad73eaea17e2e0372efb76ef6b38f17b)

State of the art practical algorithms for computing the minimum genus of graphs and the corresponding embeddings. Contains standalone C programs, python bindings, and a [web version](https://genus.sandergi.com) with 2D and 3D visualizations.

## Motivation
A famous problem at the intersection of topology and combinatorial graph theory is the [Utility Problem](https://www.youtube.com/watch?v=VvCytJvd4H0). Say you have three houses and three utilities and you need to connect each house to each utility via a wire. Is there a way to do this without the wires crossing? In terms of graph theory, this is asking whether K3,3 is _planar_. It is known that it is not. In fact K3,3 is _toroidal_ meaning while it cannot be embedded on a plane without edges crossing, it can be embedded on a torus:

[![K3,3 Torus Embedding](https://github.com/SanderGi/Genus/blob/main/assets/k3-3torus.png?raw=true)](https://github.com/SanderGi/Genus/blob/main/assets/k3-3torus.png)

The characterizing property of a torus that allows us to embed K3,3 is that it has a hole (unlike surfaces such as a plane or a sphere). This motivates classifying surfaces by their number of holes, that is, their genus g. The genus of a graph G is then simply the genus of the minimum genus surface on which G can be embedded without edges crossing. For genus zero we use the special name _planar_ and for genus one we use _toroidal_. Calculating the genus of a graph has a number of applications, particularly in the design of integrated circuits, study of graph minors, VLSI design, infrastructure planning, and more. For an interactive visualization of graph embedding [check here](https://genus.sandergi.com/k33_rotation_animation.html).

## Usage

The easiest way is to use the [web version](https://genus.sandergi.com/). This won't be as fast as running it locally and I can't guarantee it will always be up, but it should allow you to explore the algorithm. You can also self-host the web application by [installing docker](https://docs.docker.com/get-docker/) and running `cd app` followed by `. ./run-dev.sh`. This will start the web application on `localhost:8080`.

The easiest way to run locally, is with the `graph-genus` Python package. Make sure you have [Python 3](https://www.python.org/downloads/). Then `pip install graph-genus` and you can use the Python API:
```python
import graph_genus as gg

adjacency_list = [[3, 4, 5], [3, 4, 5], [3, 4, 5],
                  [0, 1, 2], [0, 1, 2], [0, 1, 2]]
genus, rotation_system = gg.embed(adjacency_list)
```
- As an optional parameter to `embed`, you can use `algorithm="page"` (default), `algorithm="multi_genus"`, and `algorithm="none"`.       ``"page"`` is especially fast for high girth graphs and scales well in general too. ``"multi_genus"`` is included with permission from Gunnar Brinkmann, is faster for some graph families, and uses less resources, but handles at most 128 vertices and 512 undirected edges. ``"none"`` treats ``adjacency_list`` as an already chosen rotation system.
- You can also use `output_format="rotation_system"` (default), `output_format="drawing"` for TikZ/LaTeX output of [the fundamental polygon](https://en.wikipedia.org/wiki/Fundamental_polygon), and `output_format="3D"` for OBJ output of the 3D surface with the graph drawn on it.
- Use `gg.cite(algorithm, output_format)` to retrieve the relevant BibTeX entries.

For local development, install with `make -C PAGE all && make -C MultiGenus all && pip install -e .` then test with `python tests/test_graph_genus_package.py` (should take ~2 minutes). Build with `source build_wheels.sh`, check with `source build_wheels_test.sh`, and upload with `pipx run twine upload dist/*`.

To run the algorithms directly without the Python bindings, take a look at the instructions for [PAGE](https://github.com/SanderGi/Genus/blob/main/PAGE/README.md) and [MultiGenus](https://github.com/SanderGi/Genus/blob/main/MultiGenus/README.md).

## Acknowledgements
[Austin](https://austinulrigg.github.io/) contributed equally to the ideas behind PAGE. [Professor Steinerberger](https://faculty.washington.edu/steinerb/) provided guidance on the PAGE publication. [Professor Brinkmann](https://scholar.google.be/citations?user=yaEBOB4AAAAJ&hl=nl) provided a fast alternative algorithm, multi_genus, and useful code for visualizing embeddings.

## License
This project is licensed under the terms of the **GNU General Public License v2.0** (GPLv2). 
See the [LICENSE](https://github.com/SanderGi/Genus/blob/main/LICENSE) file for the full text.

## Citation
If you use the PAGE algorithm or other code/visualizations from this repository, python package, or webapp, please cite:
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
If you use multi_genus, please cite
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
And if you use the fundamental polygon drawings or 3D visualizations, please additionally cite
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

You may also want to check out [the literature](https://github.com/SanderGi/Genus/blob/main/docs/references.md) this work is based on.
