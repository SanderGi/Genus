#!/usr/bin/env bash
# set -euo pipefail

rm -rf dist build src/*.egg-info

pipx run build --sdist

pipx run build --wheel

rm -rf build

if command -v x86_64-w64-mingw32-gcc >/dev/null; then
  GRAPH_GENUS_TARGET_PLATFORM=win32 \
  CC=x86_64-w64-mingw32-gcc \
  python setup.py bdist_wheel --plat-name win_amd64
fi

rm -rf build

if command -v docker >/dev/null; then
  docker run --rm --platform linux/amd64 \
    -v "$PWD:/io" \
    quay.io/pypa/manylinux2014_x86_64 \
    bash -lc '
      cd /io
      /opt/python/cp312-cp312/bin/python -m pip install -U build wheel auditwheel
      /opt/python/cp312-cp312/bin/python -m build --wheel --outdir /tmp/wheelhouse
      auditwheel repair /tmp/wheelhouse/*.whl -w /io/dist
    '
fi

rm -rf build

pipx run twine check dist/*
