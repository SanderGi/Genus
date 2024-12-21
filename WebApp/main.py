import os
import subprocess
import tempfile
import time
from io import StringIO, BytesIO

from flask import Flask, send_from_directory
from flask_sock import Sock
import json

# Initialize Flask app
app = Flask(__name__)
sock = Sock(app)


@app.route("/")
def index():
    return send_from_directory("static", "index.html")


@app.route("/<path:path>")
def send_static(path):
    return send_from_directory("static", path)


@app.route("/adjacency_lists")
def send_list_of_adjlist_names():
    return json.dumps([n for n in os.listdir("adjacency_lists") if n.endswith(".txt")])


@app.route("/adjacency_lists/<path:path>")
def send_adjlist(path):
    return send_from_directory("adjacency_lists", path)


def setup_page(adj_list, file_name):
    file = StringIO()

    num_vertices = len(adj_list)
    num_edges = sum(len(neighbors) for neighbors in adj_list) // 2
    max_degree = max(len(neighbors) for neighbors in adj_list)
    min_vertex_id = min(min(neighbors) for neighbors in adj_list)
    file.write(f"{num_vertices} {num_edges}\n")
    for neighbors in adj_list:
        padded_neighbors = neighbors + [65536] * (max_degree - len(neighbors))
        file.write(" ".join(str(n) for n in padded_neighbors) + "\n")
    file.flush()

    env = os.environ.copy()
    env["STDOUT"] = "1"
    env["PBN"] = "1"
    env["S"] = str(min_vertex_id)
    env["DEG"] = str(max_degree)
    env["ADJ"] = file_name

    return env, file, "FILE"


def setup_multi_genus(adj_list):
    file = BytesIO()

    num_vertices = len(adj_list)
    min_vertex_id = min(min(neighbors) for neighbors in adj_list)
    num_bytes = 1 if num_vertices < 256 else 2
    file.write(num_vertices.to_bytes(num_bytes, byteorder="little"))
    for v in range(num_vertices):
        for u in adj_list[v]:
            u = u - min_vertex_id
            if u > v:
                file.write((u + 1).to_bytes(num_bytes, byteorder="little"))
        if v < num_vertices - 1:
            file.write((0).to_bytes(num_bytes, byteorder="little"))
    file.flush()

    return os.environ.copy(), file, "STDIN"


def calc_genus(algorithm, adj_list: list[list[int]]):
    with tempfile.NamedTemporaryFile(mode="w") as f:
        if algorithm == "page":
            env, adj_file, inp_type = setup_page(adj_list, f.name)
            cmd = ["./CalcGenus"]
        elif algorithm == "page_sc":
            env, adj_file, inp_type = setup_page(adj_list, f.name)
            cmd = ["./CalcGenusSC"]
        elif algorithm == "multi_genus":
            env, adj_file, inp_type = setup_multi_genus(adj_list)
            cmd = ["./multi_genus_128"]
        else:
            raise ValueError("Invalid algorithm")

        if inp_type == "FILE":
            assert isinstance(adj_file, StringIO)
            adj_file.seek(0)
            f.write(adj_file.read())
            f.flush()

        start_time = time.perf_counter()
        with subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE if inp_type == "STDIN" else None,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
        ) as proc:
            if inp_type == "STDIN":
                assert isinstance(adj_file, BytesIO)
                assert proc.stdin is not None
                adj_file.seek(0)
                proc.stdin.write(adj_file.read())
                proc.stdin.close()

            assert proc.stderr is not None
            for line in proc.stderr:
                yield line.decode("utf-8"), "STDERR"

            assert proc.stdout is not None
            for line in proc.stdout:
                yield line.decode("utf-8"), "STDOUT"
        end_time = time.perf_counter()
        yield f"{end_time - start_time} seconds", "TIME"


@sock.route("/stream_calc_genus")
def stream(ws):
    data = ws.receive()
    if not data:
        return
    inp = json.loads(data)
    algorithm = inp["alg"]
    adj_list = inp["adj"]

    for out, msg_type in calc_genus(algorithm, adj_list):
        ws.send(msg_type + ":" + out)

    time.sleep(1)

    ws.close()


if __name__ == "__main__":
    app.run(debug=True, host="0.0.0.0", port=8080)
