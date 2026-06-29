import os
import subprocess
import threading
import tempfile
import time
import base64
import binascii
import re
import struct
import zlib
from io import StringIO, BytesIO
from pathlib import Path

from flask import Flask, send_from_directory
from flask_sock import Sock
import json

# Initialize Flask app
app = Flask(__name__)
sock = Sock(app)
APP_DIR = Path(__file__).resolve().parent
REPO_DIR = APP_DIR.parent


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


PAGE_GENUS_RE = re.compile(r"genus\s+(\d+)", re.IGNORECASE)
PAGE_GENUS_FOUND_RE = re.compile(r"Genus found:\s*(\d+)", re.IGNORECASE)
MULTIGENUS_RE = re.compile(r"graphs with genus\s+(\d+):", re.IGNORECASE)


def find_executable(*candidates):
    for candidate in candidates:
        paths = [Path(candidate)]
        if not Path(candidate).is_absolute():
            paths.extend([APP_DIR / candidate, REPO_DIR / candidate])
        for path in paths:
            path = path.resolve()
            if path.is_file() and os.access(path, os.X_OK):
                return str(path)
    return candidates[0]


def graph_label_start(adj_list):
    labels = [neighbor for neighbors in adj_list for neighbor in neighbors]
    if not labels:
        return 0
    return min(labels)


def normalize_rotation(adj_list):
    start = graph_label_start(adj_list)
    n = len(adj_list)
    rotation = []
    for vertex, neighbors in enumerate(adj_list):
        normalized = []
        for neighbor in neighbors:
            converted = neighbor - start
            if converted < 0 or converted >= n:
                raise ValueError(
                    f"Neighbor {neighbor} on line {vertex + 1} is outside the vertex range"
                )
            normalized.append(converted)
        rotation.append(normalized)
    return rotation, start


def rotation_to_multicode(adj_list):
    rotation, start = normalize_rotation(adj_list)
    n = len(rotation)
    if n > 255:
        raise ValueError("Drawing currently supports at most 255 vertices")

    out = BytesIO()
    out.write(bytes([n]))
    for neighbors in rotation:
        for neighbor in neighbors:
            out.write(bytes([neighbor + 1]))
        out.write(b"\0")
    return out.getvalue(), start


def decode_multicode_rotation(data, label_start=1):
    if not data:
        raise ValueError("No embedding was written")
    if data[0] == 0:
        raise ValueError("Two-byte multicode output is not supported yet")

    n = data[0]
    pos = 1
    rotation = []
    for _ in range(n):
        neighbors = []
        while True:
            if pos >= len(data):
                raise ValueError("Truncated embedding code")
            value = data[pos]
            pos += 1
            if value == 0:
                break
            neighbors.append(value - 1 + label_start)
        rotation.append(neighbors)
    return rotation


def genus_from_rotation(adj_list):
    rotation, _ = normalize_rotation(adj_list)
    n = len(rotation)
    directed_edges = set()
    next_dart = {}

    for vertex, neighbors in enumerate(rotation):
        if not neighbors:
            continue
        seen = set()
        for neighbor in neighbors:
            if neighbor in seen:
                raise ValueError(f"Duplicate neighbor at vertex {vertex}")
            seen.add(neighbor)
            directed_edges.add((vertex, neighbor))
        for i, incoming in enumerate(neighbors):
            outgoing = neighbors[(i + 1) % len(neighbors)]
            next_dart[(incoming, vertex)] = (vertex, outgoing)

    for u, v in directed_edges:
        if (v, u) not in directed_edges:
            raise ValueError(f"Rotation contains edge {u}-{v} only once")
        if (u, v) not in next_dart:
            raise ValueError(f"Rotation is missing a successor for dart {u}->{v}")

    visited = set()
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
        raise ValueError("Rotation system does not define an orientable embedding")
    return two_g // 2


def parse_page_solution(stdout_text, stderr_text, adj_list):
    genus_match = PAGE_GENUS_RE.search(stdout_text) or PAGE_GENUS_FOUND_RE.search(
        stdout_text
    )
    if not genus_match:
        genus_match = PAGE_GENUS_RE.search(stderr_text)
    if not genus_match:
        raise ValueError("PAGE did not report a genus")
    genus = int(genus_match.group(1))

    start = graph_label_start(adj_list)
    n = len(adj_list)
    next_neighbor = [dict() for _ in range(n)]
    cycle_count = 0

    for line in stdout_text.splitlines():
        if not re.fullmatch(r"\s*\d+(?:\s+\d+)*\s*", line):
            continue
        cycle = [int(value) - start for value in line.split()]
        if len(cycle) < 4 or cycle[0] != cycle[-1]:
            continue
        cycle = cycle[:-1]
        cycle_count += 1
        for i, vertex in enumerate(cycle):
            incoming = cycle[i - 1]
            outgoing = cycle[(i + 1) % len(cycle)]
            if vertex < 0 or vertex >= n or incoming < 0 or outgoing < 0:
                raise ValueError("PAGE output contains an unexpected vertex label")
            next_neighbor[vertex][incoming] = outgoing

    if cycle_count == 0:
        raise ValueError("PAGE did not write a rotation system for this graph")

    rotation = []
    for vertex, input_neighbors in enumerate(adj_list):
        normalized_neighbors = [neighbor - start for neighbor in input_neighbors]
        if not normalized_neighbors:
            rotation.append([])
            continue
        first = normalized_neighbors[0]
        ordered = [first]
        current = first
        for _ in range(1, len(normalized_neighbors)):
            if current not in next_neighbor[vertex]:
                raise ValueError(
                    f"Could not reconstruct rotation at vertex {vertex + start}"
                )
            current = next_neighbor[vertex][current]
            ordered.append(current)
        if next_neighbor[vertex].get(current) != first:
            raise ValueError(f"Rotation at vertex {vertex + start} is not cyclic")
        if set(ordered) != set(normalized_neighbors):
            raise ValueError(
                f"Rotation at vertex {vertex + start} does not match input"
            )
        rotation.append([neighbor + start for neighbor in ordered])

    return genus, rotation


def setup_page(adj_list, file_name):
    file = StringIO()

    num_vertices = len(adj_list)
    num_edges = sum(len(neighbors) for neighbors in adj_list) // 2
    max_degree = max(len(neighbors) for neighbors in adj_list)
    min_vertex_id = min(min(neighbors) for neighbors in adj_list)
    file.write(f"{num_vertices} {num_edges}\n")
    for neighbors in adj_list:
        padded_neighbors = neighbors + [65535] * (max_degree - len(neighbors))
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
            cmd = [find_executable("./CalcGenus", "../CalcGenus/CalcGenus")]
        elif algorithm == "page_sc":
            env, adj_file, inp_type = setup_page(adj_list, f.name)
            cmd = [find_executable("./CalcGenusSC", "../CalcGenus/CalcGenus")]
        elif algorithm == "multi_genus":
            env, adj_file, inp_type = setup_multi_genus(adj_list)
            cmd = [
                find_executable(
                    "./multi_genus_128",
                    "./multi_genus_longtype_128",
                    "../MultiGenus/multi_genus_longtype_128",
                )
            ]
        elif algorithm == "none":
            genus = genus_from_rotation(adj_list)
            yield f"Genus found: {genus}\n", "STDOUT"
            yield "Rotation system:\n", "STDOUT"
            for neighbors in adj_list:
                yield " ".join(str(n) for n in neighbors) + "\n", "STDOUT"
            return
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


def run_algorithm_capture(algorithm, adj_list, status_callback=None):
    if algorithm == "none":
        start_time = time.perf_counter()
        genus = genus_from_rotation(adj_list)
        return (
            {
                "genus": genus,
                "rotation_system": adj_list,
            },
            rotation_to_multicode(adj_list)[0],
            "",
            "",
            time.perf_counter() - start_time,
        )

    with tempfile.NamedTemporaryFile(mode="w") as f:
        if algorithm == "page":
            env, adj_file, inp_type = setup_page(adj_list, f.name)
            cmd = [find_executable("./CalcGenus", "../CalcGenus/CalcGenus")]
        elif algorithm == "page_sc":
            env, adj_file, inp_type = setup_page(adj_list, f.name)
            cmd = [find_executable("./CalcGenusSC", "../CalcGenus/CalcGenus")]
        elif algorithm == "multi_genus":
            env, adj_file, inp_type = setup_multi_genus(adj_list)
            cmd = [
                find_executable(
                    "./multi_genus_128",
                    "./multi_genus_longtype_128",
                    "../MultiGenus/multi_genus_longtype_128",
                )
            ]
            cmd.append("w")
        else:
            raise ValueError("Invalid algorithm")

        if inp_type == "FILE":
            assert isinstance(adj_file, StringIO)
            adj_file.seek(0)
            f.write(adj_file.read())
            f.flush()

        input_bytes = None
        if inp_type == "STDIN":
            assert isinstance(adj_file, BytesIO)
            adj_file.seek(0)
            input_bytes = adj_file.read()

        start_time = time.perf_counter()
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE if input_bytes is not None else None,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
        )
        assert proc.stdout is not None
        assert proc.stderr is not None

        if input_bytes is not None:
            assert proc.stdin is not None
            proc.stdin.write(input_bytes)
            proc.stdin.close()

        stdout_chunks = []

        def read_stdout():
            while True:
                chunk = proc.stdout.read(8192)
                if not chunk:
                    break
                stdout_chunks.append(chunk)

        stdout_thread = threading.Thread(target=read_stdout)
        stdout_thread.start()

        stderr_chunks = []
        for raw_line in proc.stderr:
            stderr_chunks.append(raw_line)
            if status_callback is not None:
                status_callback(raw_line.decode("utf-8", errors="replace"))

        returncode = proc.wait()
        stdout_thread.join()
        runtime = time.perf_counter() - start_time

    stdout_bytes = b"".join(stdout_chunks)
    stderr_text = b"".join(stderr_chunks).decode("utf-8", errors="replace")
    stdout_text = stdout_bytes.decode("utf-8", errors="replace")
    if returncode != 0:
        return (
            {
                "error": f"{algorithm} exited with status {returncode}",
                "stderr": stderr_text,
            },
            None,
            stdout_text,
            stderr_text,
            runtime,
        )

    if algorithm == "multi_genus":
        genus_match = MULTIGENUS_RE.search(stderr_text)
        if not genus_match:
            return (
                {
                    "error": "MULTI_GENUS did not report a genus",
                    "stderr": stderr_text,
                },
                None,
                stdout_text,
                stderr_text,
                runtime,
            )
        start = graph_label_start(adj_list)
        rotation = decode_multicode_rotation(stdout_bytes, label_start=start)
        result = {
            "genus": int(genus_match.group(1)),
            "rotation_system": rotation,
        }
        return result, stdout_bytes, stdout_text, stderr_text, runtime

    try:
        genus, rotation = parse_page_solution(stdout_text, stderr_text, adj_list)
    except ValueError as exc:
        return (
            {
                "error": str(exc),
                "stdout": stdout_text,
                "stderr": stderr_text,
            },
            None,
            stdout_text,
            stderr_text,
            runtime,
        )

    multicode, _ = rotation_to_multicode(rotation)
    return (
        {
            "genus": genus,
            "rotation_system": rotation,
        },
        multicode,
        stdout_text,
        stderr_text,
        runtime,
    )


def render_multicode_png(multicode):
    draw_cmd = find_executable(
        "./planar_cutthroughedges_draw",
        "../MultiGenus/planar_cutthroughedges_draw",
    )
    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir = Path(tmpdir)
        draw = subprocess.run(
            [draw_cmd, "f", "l"],
            input=multicode,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if draw.returncode != 0:
            raise RuntimeError(draw.stderr.decode("utf-8", errors="replace"))

        tex_path = tmpdir / "embedding.tex"
        tex_path.write_text(suppress_latex_page_numbers(draw.stdout), encoding="utf-8")
        latex = subprocess.run(
            [
                "pdflatex",
                "-interaction=nonstopmode",
                "-halt-on-error",
                tex_path.name,
            ],
            cwd=tmpdir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if latex.returncode != 0:
            raise RuntimeError(summarize_latex_error(latex.stdout))

        pdf_path = tmpdir / "embedding.pdf"
        png_base = tmpdir / "embedding"
        convert = subprocess.run(
            [
                "pdftoppm",
                "-png",
                "-singlefile",
                "-r",
                "180",
                str(pdf_path),
                str(png_base),
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if convert.returncode != 0:
            raise RuntimeError(convert.stderr.decode("utf-8", errors="replace"))
        return crop_png((tmpdir / "embedding.png").read_bytes())


def render_multicode_obj(multicode):
    draw_cmd = find_executable(
        "./planar_cutthroughedges_draw",
        "../MultiGenus/planar_cutthroughedges_draw",
    )
    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir = Path(tmpdir)
        prefix = tmpdir / "surface"
        draw = subprocess.run(
            [draw_cmd, "f", "l", "o", str(prefix)],
            input=multicode,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if draw.returncode != 0:
            raise RuntimeError(draw.stderr.decode("utf-8", errors="replace"))

        obj_path = tmpdir / "surface.obj"
        mtl_path = tmpdir / "surface.mtl"
        if not obj_path.exists():
            raise RuntimeError("3D exporter did not write the expected OBJ file")

        return {
            "obj": obj_path.read_text(encoding="utf-8", errors="replace"),
            "mtl": (
                mtl_path.read_text(encoding="utf-8", errors="replace")
                if mtl_path.exists()
                else ""
            ),
        }


def suppress_latex_page_numbers(output):
    text = output.decode("utf-8", errors="replace")
    if "\\pagestyle{empty}" in text:
        return text
    return text.replace("\\begin{document}", "\\pagestyle{empty}\n\\begin{document}", 1)


def crop_png(png, background_threshold=250, margin=24):
    signature = b"\x89PNG\r\n\x1a\n"
    if not png.startswith(signature):
        return png

    pos = len(signature)
    chunks = []
    ihdr = None
    idat = []
    palette = None
    transparency = None

    while pos + 8 <= len(png):
        length = struct.unpack(">I", png[pos : pos + 4])[0]
        chunk_type = png[pos + 4 : pos + 8]
        data = png[pos + 8 : pos + 8 + length]
        pos += 12 + length
        chunks.append((chunk_type, data))
        if chunk_type == b"IHDR":
            ihdr = data
        elif chunk_type == b"IDAT":
            idat.append(data)
        elif chunk_type == b"PLTE":
            palette = data
        elif chunk_type == b"tRNS":
            transparency = data
        elif chunk_type == b"IEND":
            break

    if ihdr is None or not idat:
        return png

    width, height, bit_depth, color_type, compression, filter_method, interlace = (
        struct.unpack(">IIBBBBB", ihdr)
    )
    if compression != 0 or filter_method != 0 or interlace != 0 or bit_depth != 8:
        return png

    try:
        raw = zlib.decompress(b"".join(idat))
        rgba_rows = decode_png_rows(
            raw, width, height, color_type, palette, transparency
        )
    except (IndexError, ValueError, zlib.error):
        return png

    left, top, right, bottom = width, height, -1, -1
    for y, row in enumerate(rgba_rows):
        for x in range(width):
            r, g, b, a = row[x * 4 : x * 4 + 4]
            if a > 0 and (
                r < background_threshold
                or g < background_threshold
                or b < background_threshold
            ):
                left = min(left, x)
                top = min(top, y)
                right = max(right, x)
                bottom = max(bottom, y)

    if right < left or bottom < top:
        return png

    left = max(0, left - margin)
    top = max(0, top - margin)
    right = min(width - 1, right + margin)
    bottom = min(height - 1, bottom + margin)
    cropped_width = right - left + 1
    cropped_height = bottom - top + 1

    scanlines = []
    for y in range(top, bottom + 1):
        row = rgba_rows[y]
        scanlines.append(b"\0" + row[left * 4 : (right + 1) * 4])

    return encode_rgba_png(cropped_width, cropped_height, b"".join(scanlines))


def decode_png_rows(raw, width, height, color_type, palette, transparency):
    channels_by_type = {0: 1, 2: 3, 3: 1, 4: 2, 6: 4}
    if color_type not in channels_by_type:
        raise ValueError("Unsupported PNG color type")

    channels = channels_by_type[color_type]
    stride = width * channels
    rows = []
    previous = bytearray(stride)
    pos = 0

    for _ in range(height):
        filter_type = raw[pos]
        pos += 1
        current = bytearray(raw[pos : pos + stride])
        pos += stride
        unfilter_row(current, previous, channels, filter_type)
        rows.append(row_to_rgba(current, width, color_type, palette, transparency))
        previous = current

    return rows


def unfilter_row(current, previous, bpp, filter_type):
    for i in range(len(current)):
        left = current[i - bpp] if i >= bpp else 0
        up = previous[i]
        upper_left = previous[i - bpp] if i >= bpp else 0
        if filter_type == 0:
            prediction = 0
        elif filter_type == 1:
            prediction = left
        elif filter_type == 2:
            prediction = up
        elif filter_type == 3:
            prediction = (left + up) // 2
        elif filter_type == 4:
            prediction = paeth(left, up, upper_left)
        else:
            raise ValueError("Unsupported PNG filter")
        current[i] = (current[i] + prediction) & 0xFF


def paeth(left, up, upper_left):
    p = left + up - upper_left
    pa = abs(p - left)
    pb = abs(p - up)
    pc = abs(p - upper_left)
    if pa <= pb and pa <= pc:
        return left
    if pb <= pc:
        return up
    return upper_left


def row_to_rgba(row, width, color_type, palette, transparency):
    out = bytearray(width * 4)
    for x in range(width):
        if color_type == 0:
            gray = row[x]
            rgba = (gray, gray, gray, 255)
        elif color_type == 2:
            i = x * 3
            rgba = (row[i], row[i + 1], row[i + 2], 255)
        elif color_type == 3:
            if palette is None:
                raise ValueError("Palette PNG is missing PLTE")
            index = row[x]
            p = index * 3
            alpha = (
                transparency[index]
                if transparency and index < len(transparency)
                else 255
            )
            rgba = (palette[p], palette[p + 1], palette[p + 2], alpha)
        elif color_type == 4:
            i = x * 2
            gray = row[i]
            rgba = (gray, gray, gray, row[i + 1])
        else:
            i = x * 4
            rgba = (row[i], row[i + 1], row[i + 2], row[i + 3])
        out[x * 4 : x * 4 + 4] = bytes(rgba)
    return bytes(out)


def encode_rgba_png(width, height, scanlines):
    def chunk(chunk_type, data):
        checksum = binascii.crc32(chunk_type + data) & 0xFFFFFFFF
        return (
            struct.pack(">I", len(data))
            + chunk_type
            + data
            + struct.pack(">I", checksum)
        )

    ihdr = struct.pack(">IIBBBBB", width, height, 8, 6, 0, 0, 0)
    return b"".join(
        [
            b"\x89PNG\r\n\x1a\n",
            chunk(b"IHDR", ihdr),
            chunk(b"IDAT", zlib.compress(scanlines)),
            chunk(b"IEND", b""),
        ]
    )


def summarize_latex_error(output):
    text = output.decode("utf-8", errors="replace")
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("! "):
            context = lines[i : i + 6]
            return "\n".join(context)
    return text[-2000:]


@sock.route("/stream_calc_genus")
def stream(ws):
    data = ws.receive()
    if not data:
        return
    inp = json.loads(data)
    algorithm = inp["alg"]
    adj_list = inp["adj"]
    output_format = inp.get("outputFormat", "text")

    if output_format == "text":
        for out, msg_type in calc_genus(algorithm, adj_list):
            ws.send(msg_type + ":" + out)
    elif output_format == "json":
        runtime = None

        def send_status(line):
            ws.send("STDERR:" + line)

        try:
            result, _, _, _, runtime = run_algorithm_capture(
                algorithm, adj_list, status_callback=send_status
            )
        except Exception as exc:
            result = {"error": str(exc)}
        ws.send("JSON:" + json.dumps(result, sort_keys=True))
        if runtime is not None:
            ws.send("TIME:" + f"{runtime} seconds")
    elif output_format == "drawing":
        runtime = None

        def send_status(line):
            ws.send("STDERR:" + line)

        try:
            result, multicode, _, _, runtime = run_algorithm_capture(
                algorithm, adj_list, status_callback=send_status
            )
        except Exception as exc:
            result = {"error": str(exc)}
            multicode = None
        if multicode is None:
            ws.send("JSON:" + json.dumps(result, sort_keys=True))
        else:
            try:
                png = render_multicode_png(multicode)
            except Exception as exc:
                ws.send("JSON:" + json.dumps({"error": str(exc)}, sort_keys=True))
            else:
                ws.send(
                    "IMAGE:data:image/png;base64,"
                    + base64.b64encode(png).decode("ascii")
                )
        if runtime is not None:
            ws.send("TIME:" + f"{runtime} seconds")
    elif output_format in ("3d", "3d_raw"):
        runtime = None

        def send_status(line):
            ws.send("STDERR:" + line)

        try:
            result, multicode, _, _, runtime = run_algorithm_capture(
                algorithm, adj_list, status_callback=send_status
            )
        except Exception as exc:
            result = {"error": str(exc)}
            multicode = None
        if multicode is None:
            ws.send("JSON:" + json.dumps(result, sort_keys=True))
        elif output_format == "3d" and result.get("genus", 0) > 1:
            ws.send(
                "JSON:"
                + json.dumps(
                    {
                        "error": (
                            "3D output is currently supported only for genus 0 "
                            "and genus 1 embeddings."
                        ),
                        "genus": result["genus"],
                    },
                    sort_keys=True,
                )
            )
        else:
            try:
                model = render_multicode_obj(multicode)
            except Exception as exc:
                ws.send("JSON:" + json.dumps({"error": str(exc)}, sort_keys=True))
            else:
                if "genus" in result:
                    model["genus"] = result["genus"]
                ws.send("MODEL:" + json.dumps(model))
        if runtime is not None:
            ws.send("TIME:" + f"{runtime} seconds")
    else:
        ws.send("JSON:" + json.dumps({"error": "Invalid output format"}))

    time.sleep(1)

    ws.close()


if __name__ == "__main__":
    app.run(debug=True, host="0.0.0.0", port=8080)
