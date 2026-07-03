#!/usr/bin/env sage
# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Run PAGE against the ROME dataset (https://visdunneright.github.io/gd_benchmark_sets/#moveToRome-Lib)."""

import tarfile
import networkx as nx  # type: ignore
import os, signal
import subprocess, threading
from sage.all import Graph  # type: ignore
from tqdm import tqdm


class Command(object):
    def __init__(self, cmd):
        self.cmd = cmd
        self.process: subprocess.Popen | None = None

        self.stdout: str | None = None
        self.stderr: str | None = None

    def run(self, timeout, hide_output=True):
        def target():
            if hide_output:
                self.process = subprocess.Popen(
                    self.cmd,
                    shell=True,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    preexec_fn=os.setsid,
                )
            else:
                self.process = subprocess.Popen(
                    self.cmd,
                    shell=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    preexec_fn=os.setsid,
                )
            self.stdout, self.stderr = self.process.communicate()

        thread = threading.Thread(target=target)
        thread.start()

        thread.join(timeout)
        if thread.is_alive() and self.process:
            os.killpg(self.process.pid, signal.SIGTERM)
            thread.join()

        return self.process and self.process.returncode


# command = Command("echo 'Process started'; sleep 2; echo 'Process finished'")
# print(command.run(timeout=3))
# print(command.run(timeout=1))

valid = 0
successfull = 0
try:
    with tarfile.open("adjacency_lists/rome-graphml.tgz", "r:gz") as tar:
        for name in tqdm(tar.getnames()):
            if not name.endswith(".graphml"):
                continue

            f = tar.extractfile(name)

            # load as sage graph
            g = Graph(nx.read_graphml(f))
            obscure = int(name.split(".")[1]) != g.num_verts()

            # print("Obscure:", obscure)
            # print("Connected:", g.is_connected())
            # print("Planar:", g.is_planar())
            # print("Regular:", g.is_regular())
            # print("Max Degree:", max(g.degree()))

            if not obscure and g.is_connected() and not g.is_planar():
                valid += 1

                while min(g.degree()) <= 1:
                    g.delete_vertices(
                        [v for v in g.vertices() if g.degree(v) <= 1]
                    )  # remove nodes with only one edge
                for v in g.vertices():
                    if g.degree(v) == 2:
                        # replace with a single edge
                        g.add_edge(g.neighbors(v))
                        g.delete_vertex(v)
                g.relabel()  # relabel edges to numbers
                adjacency_list = [[] for j in range(len(g.vertices()))]
                for e in g.edges():
                    adjacency_list[e[0]].append(e[1])
                    adjacency_list[e[1]].append(e[0])
                max_degree = max(g.degree())
                for i in range(len(g.vertices())):  # pad adjacency list
                    while len(adjacency_list[i]) < max_degree:
                        adjacency_list[i].append(65535)
                with open("adjacency_lists/rome_temp.txt", "w") as f:
                    f.write(f"{len(g.vertices())} {len(g.edges())}\n")
                    for i in range(len(g.vertices())):
                        f.write(f'{" ".join(map(str, adjacency_list[i]))}\n')

                command = Command(
                    f'S="0" DEG="{max_degree}" ADJ="adjacency_lists/rome_temp.txt" make run'
                )
                terminated = command.run(timeout=10) == -15
                if not terminated:
                    successfull += 1
finally:
    print(valid, successfull)
