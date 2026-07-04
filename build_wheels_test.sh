python3 -m venv /tmp/gg-macos-test
/tmp/gg-macos-test/bin/python -m pip install -U pip
/tmp/gg-macos-test/bin/python -m pip install dist/graph_genus-*-macosx_*.whl
/tmp/gg-macos-test/bin/python - <<'PY'
import graph_genus as gg

k33 = [[3,4,5], [3,4,5], [3,4,5], [0,1,2], [0,1,2], [0,1,2]]
print(gg.embed(k33))
print("drawing:", "\\begin{tikzpicture}" in gg.embed(k33, output_format="drawing")[1])
print("obj:", gg.embed(k33, output_format="3D")[1][:20])
PY

docker run --rm --platform linux/amd64 \
  -v "$PWD:/io" \
  python:3.12-slim \
  bash -lc '
    python -m venv /tmp/gg-linux-test
    /tmp/gg-linux-test/bin/python -m pip install -U pip
    /tmp/gg-linux-test/bin/python -m pip install /io/dist/graph_genus-*-manylinux*_x86_64.whl
    /tmp/gg-linux-test/bin/python - <<'"'"'PY'"'"'
import graph_genus as gg

k33 = [[3,4,5], [3,4,5], [3,4,5], [0,1,2], [0,1,2], [0,1,2]]
print(gg.embed(k33))
print("drawing:", "\\begin{tikzpicture}" in gg.embed(k33, output_format="drawing")[1])
print("obj:", gg.embed(k33, output_format="3D")[1][:20])
PY
  '
  
export WINEDEBUG=-all
alias wine_python="wine python-3.8.6-embed-amd64/python.exe"

wine_python -m pip install --upgrade pip
wine_python -m pip install dist/graph_genus-*-win_amd64.whl

wine_python - <<'PY'
import graph_genus as gg

k33 = [[3,4,5], [3,4,5], [3,4,5], [0,1,2], [0,1,2], [0,1,2]]
print(gg.embed(k33))
print("drawing:", "\\begin{tikzpicture}" in gg.embed(k33, output_format="drawing")[1])
print("obj:", gg.embed(k33, output_format="3D")[1][:20])
PY
