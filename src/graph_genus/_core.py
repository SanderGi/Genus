# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Public Python API for the bundled graph genus tools."""

from __future__ import annotations

import os
import platform
import re
import subprocess
import tempfile
from io import BytesIO
from pathlib import Path
from typing import Literal, Sequence

Algorithm = Literal["page", "multi_genus", "none"]
OutputFormat = Literal["rotation_system", "drawing", "3D"]


class GraphGenusError(RuntimeError):
    """Raised when a bundled graph genus tool cannot produce the requested output."""


PAGE_GENUS_RE = re.compile(r"genus\s+(\d+)", re.IGNORECASE)
PAGE_GENUS_FOUND_RE = re.compile(r"Genus found:\s*(\d+)", re.IGNORECASE)
MULTIGENUS_RE = re.compile(r"graphs with genus\s+(\d+):", re.IGNORECASE)

PAGE_BIBTEX = """@article{Metzger_2026,
    title={An efficient genus algorithm based on graph rotations},
    number={12}, volume={349}, ISSN={0012-365X},
    url={http://doi.org/10.1016/j.disc.2026.115308},
    DOI={10.1016/j.disc.2026.115308},
    journal={Discrete Mathematics},
    publisher={Elsevier BV},
    author={Metzger, Alexander and Ulrigg, Austin},
    year={2026}, month=Dec, pages={115308}
}"""

MULTI_GENUS_BIBTEX = """@article{article,
    title = {A practical algorithm for the computation of the genus},
    author = {Brinkmann, Gunnar},
    year = {2022}, month = {07},
    pages = {#P4.01}, volume = {22},
    journal = {Ars Mathematica Contemporanea},
    doi = {10.26493/1855-3974.2320.c2d}
}"""

PLANAR_DRAW_BIBTEX = """@misc{brinkmann2025drawingmapsorientedsurfaces,
    title={Drawing maps on oriented surfaces},
    author={Gunnar Brinkmann},
    year={2025},
    eprint={2505.01480},
    archivePrefix={arXiv},
    primaryClass={cs.CG},
    url={https://arxiv.org/abs/2505.01480},
}"""


def embed(
    adjacency_list: Sequence[Sequence[int]],
    *,
    algorithm: Algorithm = "page",
    output_format: OutputFormat = "rotation_system",
) -> tuple[int, list[list[int]] | str]:
    """Embed a graph and return its genus plus the requested artifact.

    INPUT:

    - ``adjacency_list`` -- zero-indexed adjacency list.  Each sublist contains
      the neighbors of the vertex with the same index.
    - ``algorithm`` -- ``"page"`` (default), ``"multi_genus"``, or ``"none"``.
      ``"page"`` is especially fast for high girth graphs and scales well in general too.
      ``"multi_genus"`` is included with permission from Gunnar Brinkmann, is faster for some graph families, and uses less resources, but handles at most 128 vertices and 512 undirected edges.
      ``"none"`` treats ``adjacency_list`` as an already chosen rotation system.
    - ``output_format`` -- ``"rotation_system"`` (default), ``"drawing"`` for
      TikZ/LaTeX output from ``planar_draw``, or ``"3D"`` for OBJ output.

    OUTPUT:

    A pair ``(genus, artifact)``.  For ``"rotation_system"``, the artifact is a
    list of cyclically ordered neighbor lists.  For ``"drawing"``, it is the
    TikZ/LaTeX string emitted by ``planar_draw``.  For ``"3D"``, it is the OBJ
    file text emitted by ``planar_draw``.
    """

    graph = _validate_adjacency_list(adjacency_list)
    algorithm = _normalize_algorithm(algorithm)
    output_format = _normalize_output_format(output_format)

    if algorithm == "none":
        rotation_system = graph
        genus = genus_from_rotation(rotation_system)
    elif algorithm == "page":
        genus, rotation_system = _run_page(graph)
    else:
        genus, rotation_system = _run_multi_genus(graph)

    if output_format == "rotation_system":
        return genus, rotation_system
    if output_format == "drawing":
        return genus, _run_planar_draw(rotation_system)
    if genus > 1:
        raise GraphGenusError(
            "3D output is currently supported only for genus 0 and genus 1 embeddings."
        )
    return genus, _run_planar_draw_obj(rotation_system)


def cite(
    algorithm: Algorithm = "page",
    output_format: OutputFormat = "rotation_system",
) -> str:
    """Return BibTeX entries for the selected algorithm and output format."""

    algorithm = _normalize_algorithm(algorithm)
    output_format = _normalize_output_format(output_format)
    entries: list[str] = []
    if algorithm == "multi_genus":
        entries.append(MULTI_GENUS_BIBTEX)
    entries.append(PAGE_BIBTEX)
    if output_format in {"drawing", "3D"}:
        entries.append(PLANAR_DRAW_BIBTEX)
    return "\n".join(entries)


def genus_from_rotation(rotation_system: Sequence[Sequence[int]]) -> int:
    """Compute the orientable genus of a zero-indexed rotation system."""

    rotation = _validate_adjacency_list(rotation_system)
    n = len(rotation)
    directed_edges: set[tuple[int, int]] = set()
    next_dart: dict[tuple[int, int], tuple[int, int]] = {}

    for vertex, neighbors in enumerate(rotation):
        if not neighbors:
            continue
        for neighbor in neighbors:
            directed_edges.add((vertex, neighbor))
        for i, incoming in enumerate(neighbors):
            outgoing = neighbors[(i + 1) % len(neighbors)]
            next_dart[(incoming, vertex)] = (vertex, outgoing)

    for dart in directed_edges:
        if (dart[1], dart[0]) not in directed_edges:
            raise GraphGenusError(
                f"Rotation contains edge {dart[0]}-{dart[1]} only once"
            )
        if dart not in next_dart:
            raise GraphGenusError(
                f"Rotation is missing a successor for dart {dart[0]}->{dart[1]}"
            )

    visited: set[tuple[int, int]] = set()
    faces = 0
    for dart in directed_edges:
        if dart in visited:
            continue
        faces += 1
        current = dart
        while current not in visited:
            visited.add(current)
            current = next_dart[current]

    edges = len(directed_edges) // 2
    two_g = 2 - (n - edges + faces)
    if two_g < 0 or two_g % 2 != 0:
        raise GraphGenusError("Rotation system does not define an orientable embedding")
    return two_g // 2


def _validate_adjacency_list(
    adjacency_list: Sequence[Sequence[int]],
) -> list[list[int]]:
    if not isinstance(adjacency_list, Sequence):
        raise TypeError("adjacency_list must be a sequence of neighbor sequences")

    graph: list[list[int]] = []
    n = len(adjacency_list)
    for vertex, neighbors in enumerate(adjacency_list):
        if not isinstance(neighbors, Sequence):
            raise TypeError(f"neighbors for vertex {vertex} must be a sequence")
        converted: list[int] = []
        seen: set[int] = set()
        for neighbor in neighbors:
            if not isinstance(neighbor, int):
                raise TypeError("neighbors must be integers")
            if neighbor < 0 or neighbor >= n:
                raise ValueError(
                    f"neighbor {neighbor} at vertex {vertex} is outside 0..{n - 1}"
                )
            if neighbor == vertex:
                raise ValueError(f"loops are not supported: vertex {vertex}")
            if neighbor in seen:
                raise ValueError(f"duplicate neighbor {neighbor} at vertex {vertex}")
            seen.add(neighbor)
            converted.append(neighbor)
        graph.append(converted)

    for vertex, neighbors in enumerate(graph):
        for neighbor in neighbors:
            if vertex not in graph[neighbor]:
                raise ValueError(f"edge {vertex}-{neighbor} appears only once")
    return graph


def _normalize_algorithm(algorithm: str) -> Algorithm:
    if algorithm not in {"page", "multi_genus", "none"}:
        raise ValueError("algorithm must be 'page', 'multi_genus', or 'none'")
    return algorithm  # type: ignore[return-value]


def _normalize_output_format(output_format: str) -> OutputFormat:
    normalized = "3D" if output_format.lower() == "3d" else output_format
    if normalized not in {"rotation_system", "drawing", "3D"}:
        raise ValueError("output_format must be 'rotation_system', 'drawing', or '3D'")
    return normalized  # type: ignore[return-value]


def _run_page(graph: list[list[int]]) -> tuple[int, list[list[int]]]:
    max_degree = max((len(neighbors) for neighbors in graph), default=0)
    if max_degree < 2:
        return genus_from_rotation(graph), graph

    with tempfile.TemporaryDirectory() as tmp:
        adjacency_file = Path(tmp) / "graph.adj"
        _write_page_adjacency_file(graph, adjacency_file, max_degree)
        env = os.environ.copy()
        env.update(
            {
                "STDOUT": "1",
                "PBN": "1",
                "S": "0",
                "DEG": str(max_degree),
                "ADJ": str(adjacency_file),
            }
        )
        proc = subprocess.run(
            [_tool_path("page")],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
            check=False,
        )
    stdout = proc.stdout.decode("utf-8", errors="replace")
    stderr = proc.stderr.decode("utf-8", errors="replace")
    if proc.returncode != 0:
        raise GraphGenusError(f"PAGE exited with status {proc.returncode}:\n{stderr}")
    return _parse_page_solution(stdout, stderr, graph)


def _run_multi_genus(graph: list[list[int]]) -> tuple[int, list[list[int]]]:
    proc = subprocess.run(
        [_tool_path("multi_genus"), "w"],
        input=_graph_to_multicode(graph, upper_triangle_only=True),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    stderr = proc.stderr.decode("utf-8", errors="replace")
    if proc.returncode != 0:
        raise GraphGenusError(
            f"multi_genus exited with status {proc.returncode}:\n{stderr}"
        )
    rotation = _decode_multicode_rotation(proc.stdout)
    genus_match = MULTIGENUS_RE.search(stderr)
    genus = (
        int(genus_match.group(1))
        if genus_match is not None
        else genus_from_rotation(rotation)
    )
    return genus, rotation


def _run_planar_draw(rotation_system: list[list[int]]) -> str:
    proc = subprocess.run(
        [_tool_path("planar_draw"), "f", "l"],
        input=_graph_to_multicode(rotation_system, upper_triangle_only=False),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        stderr = proc.stderr.decode("utf-8", errors="replace")
        raise GraphGenusError(
            f"planar_draw exited with status {proc.returncode}:\n{stderr}"
        )
    return proc.stdout.decode("utf-8", errors="replace")


def _run_planar_draw_obj(rotation_system: list[list[int]]) -> str:
    with tempfile.TemporaryDirectory() as tmp:
        prefix = Path(tmp) / "surface"
        proc = subprocess.run(
            [_tool_path("planar_draw"), "f", "l", "o", str(prefix)],
            input=_graph_to_multicode(rotation_system, upper_triangle_only=False),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if proc.returncode != 0:
            stderr = proc.stderr.decode("utf-8", errors="replace")
            raise GraphGenusError(
                f"planar_draw exited with status {proc.returncode}:\n{stderr}"
            )
        obj_path = prefix.with_suffix(".obj")
        if not obj_path.exists():
            raise GraphGenusError("planar_draw did not write the expected OBJ file")
        return obj_path.read_text(encoding="utf-8", errors="replace")


def _write_page_adjacency_file(
    graph: list[list[int]], path: Path, max_degree: int
) -> None:
    edges = sum(len(neighbors) for neighbors in graph) // 2
    lines = [f"{len(graph)} {edges}"]
    for neighbors in graph:
        padded = neighbors + [65535] * (max_degree - len(neighbors))
        lines.append(" ".join(str(neighbor) for neighbor in padded))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _parse_page_solution(
    stdout: str, stderr: str, graph: list[list[int]]
) -> tuple[int, list[list[int]]]:
    genus_match = PAGE_GENUS_RE.search(stdout) or PAGE_GENUS_FOUND_RE.search(stdout)
    if genus_match is None:
        genus_match = PAGE_GENUS_RE.search(stderr)
    if genus_match is None:
        raise GraphGenusError("PAGE did not report a genus")
    genus = int(genus_match.group(1))

    n = len(graph)
    next_neighbor: list[dict[int, int]] = [dict() for _ in graph]
    cycle_count = 0

    for line in stdout.splitlines():
        if not re.fullmatch(r"\s*\d+(?:\s+\d+)*\s*", line):
            continue
        cycle = [int(value) for value in line.split()]
        if len(cycle) < 4 or cycle[0] != cycle[-1]:
            continue
        cycle = cycle[:-1]
        cycle_count += 1
        for i, vertex in enumerate(cycle):
            incoming = cycle[i - 1]
            outgoing = cycle[(i + 1) % len(cycle)]
            if vertex < 0 or vertex >= n or incoming < 0 or outgoing < 0:
                raise GraphGenusError("PAGE output contains an unexpected vertex label")
            next_neighbor[vertex][incoming] = outgoing

    if cycle_count == 0:
        raise GraphGenusError("PAGE did not write a rotation system for this graph")

    rotation: list[list[int]] = []
    for vertex, neighbors in enumerate(graph):
        if not neighbors:
            rotation.append([])
            continue
        first = neighbors[0]
        ordered = [first]
        current = first
        for _ in range(1, len(neighbors)):
            if current not in next_neighbor[vertex]:
                raise GraphGenusError(
                    f"Could not reconstruct rotation at vertex {vertex}"
                )
            current = next_neighbor[vertex][current]
            ordered.append(current)
        if next_neighbor[vertex].get(current) != first:
            raise GraphGenusError(f"Rotation at vertex {vertex} is not cyclic")
        if set(ordered) != set(neighbors):
            raise GraphGenusError(f"Rotation at vertex {vertex} does not match input")
        rotation.append(ordered)

    return genus, rotation


def _graph_to_multicode(graph: list[list[int]], *, upper_triangle_only: bool) -> bytes:
    if len(graph) > 255:
        raise GraphGenusError(
            "The bundled multicode path currently supports at most 255 vertices"
        )
    out = BytesIO()
    out.write(bytes([len(graph)]))
    for vertex, neighbors in enumerate(graph):
        for neighbor in neighbors:
            if not upper_triangle_only or neighbor > vertex:
                out.write(bytes([neighbor + 1]))
        out.write(b"\0")
    return out.getvalue()


def _decode_multicode_rotation(data: bytes) -> list[list[int]]:
    if not data:
        raise GraphGenusError("No embedding was written")
    if data[0] == 0:
        raise GraphGenusError("Two-byte multicode output is not supported yet")

    n = data[0]
    pos = 1
    rotation: list[list[int]] = []
    for _ in range(n):
        neighbors: list[int] = []
        while True:
            if pos >= len(data):
                raise GraphGenusError("Truncated embedding code")
            value = data[pos]
            pos += 1
            if value == 0:
                break
            neighbors.append(value - 1)
        rotation.append(neighbors)
    return rotation


def _tool_path(name: str) -> str:
    exe_name = name + (".exe" if platform.system() == "Windows" else "")
    package_tool = Path(__file__).resolve().parent / "bin" / exe_name
    if package_tool.is_file():
        return str(package_tool)

    repo_root = Path(__file__).resolve().parents[2]
    fallback_candidates = [
        repo_root / "PAGE" / exe_name,
        repo_root / "MultiGenus" / exe_name,
        repo_root / "app" / exe_name,
        repo_root / exe_name,
    ]
    for candidate in fallback_candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate)
    raise GraphGenusError(
        f"Could not find bundled tool {exe_name!r}. Reinstall graph-genus from a built wheel "
        "or run a normal package build first."
    )
