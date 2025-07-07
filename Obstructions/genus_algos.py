import re
from run_shell import Command
from adj_format import to_adj_list, to_multi_code


def run_page(g, max_degree, filename, timeout=100):
    command = Command(
        f'cd ../CalcGenus && S="0" DEG="{max_degree}" ADJ="{filename}" make run'
    )
    returncode = command.run(timeout=timeout, hide_output=False)
    if returncode != 0:
        raise Exception(
            f"Error with {g}: " + "\n".join(command.stderr.decode().split("\n")[-3:])  # type: ignore
        )
    else:
        reg = re.search(r"The genus is (\d+)", command.stderr.decode())  # type: ignore
        genus = None
        if reg:
            genus = int(reg.group(1))
        return genus


def run_multi_genus(g, filename, timeout=100):
    command = Command(f"cat {filename} | ../MultiGenus/multi_genus_longtype_128 w")
    returncode = command.run(timeout=timeout, hide_output=False)
    if returncode != 0:
        raise Exception(f"Error with {g}: " + command.stderr.decode())  # type: ignore
    else:
        reg = re.search(r"with genus (\d+)", command.stderr.decode())  # type: ignore
        genus = None
        if reg:
            genus = int(reg.group(1))
        return genus


def run_algorithm(graph, algorithm="MULTI", timeout=100):
    graph = graph.copy()
    graph.relabel()

    genus = 0
    for g in graph.connected_components_subgraphs():
        if algorithm == "PAGE":
            filename = "../CalcGenus/adjacency_lists/nauty_temp.txt"
            _, max_degree = to_adj_list(g, filename)
            genus += run_page(g, max_degree, filename, timeout=timeout)  # type: ignore
        elif algorithm == "MULTI":
            filename = "../CalcGenus/adjacency_lists/nauty_temp.txt"
            adjacency_list, max_degree = to_adj_list(g, filename)
            multi_filename = "../MultiGenus/graphs/nauty_temp.mc"
            to_multi_code(adjacency_list, multi_filename)
            genus += run_multi_genus(g, multi_filename, timeout=timeout)  # type: ignore
        elif algorithm == "SAGE":
            genus += g.genus()
        else:
            raise Exception("Invalid algorithm")

    return genus
