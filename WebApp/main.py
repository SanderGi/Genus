import os
import subprocess
import tempfile

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
    return json.dumps(os.listdir("adjacency_lists"))


@app.route("/adjacency_lists/<path:path>")
def send_adjlist(path):
    return send_from_directory("adjacency_lists", path)


def calc_genus(adj_list: list[list[int]]):
    with tempfile.NamedTemporaryFile(mode="w") as f:
        num_vertices = len(adj_list)
        num_edges = sum(len(neighbors) for neighbors in adj_list) // 2
        max_degree = max(len(neighbors) for neighbors in adj_list)
        min_vertex_id = min(min(neighbors) for neighbors in adj_list)
        f.write(f"{num_vertices} {num_edges}\n")
        for neighbors in adj_list:
            padded_neighbors = neighbors + [65536] * (max_degree - len(neighbors))
            f.write(" ".join(str(n) for n in padded_neighbors) + "\n")
        f.flush()

        env = os.environ.copy()
        env["STDOUT"] = "1"
        env["PBN"] = "1"
        env["S"] = str(min_vertex_id)
        env["DEG"] = str(max_degree)
        env["ADJ"] = f.name
        with subprocess.Popen(
            ["./CalcGenus"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
        ) as proc:
            assert proc.stderr is not None
            for line in proc.stderr:
                yield line.decode("utf-8"), False

            assert proc.stdout is not None
            for line in proc.stdout:
                yield line.decode("utf-8"), True


@sock.route("/stream_calc_genus")
def stream(ws):
    data = ws.receive()
    if not data:
        return
    adj_list = json.loads(data)

    for out, is_stdout in calc_genus(adj_list):
        if is_stdout:
            ws.send("STDOUT:" + out)
        else:
            ws.send("STDERR:" + out)

    ws.close()


if __name__ == "__main__":
    app.run(debug=True, host="0.0.0.0", port=8080)
