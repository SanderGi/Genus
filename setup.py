# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Build native helper programs bundled with graph_genus."""

from __future__ import annotations

import os
import shlex
import subprocess
import sys
import sysconfig
from pathlib import Path
import shutil

from setuptools import find_packages, setup, Distribution
from setuptools.command.build_py import build_py
from setuptools.command.bdist_wheel import bdist_wheel as _bdist_wheel


class BinaryDistribution(Distribution):
    def has_ext_modules(self):
        return True


class bdist_wheel(_bdist_wheel):
    def finalize_options(self):
        super().finalize_options()
        self.root_is_pure = False

    def get_tag(self):
        _, _, plat = super().get_tag()
        return "py3", "none", plat


class build_py_with_native_tools(build_py):
    """Compile the bundled C command-line tools into package data."""

    def run(self) -> None:
        super().run()
        self._build_native_tools()

    def _build_native_tools(self) -> None:
        source_root = Path(__file__).resolve().parent
        package_dir = Path(self.build_lib) / "graph_genus"
        bin_dir = package_dir / "bin"
        if bin_dir.exists():
            shutil.rmtree(bin_dir)
        bin_dir.mkdir(parents=True, exist_ok=True)
        page_source = source_root / "PAGE" / "page.c"
        multi_genus_source = source_root / "MultiGenus" / "multi_genus.c"
        planar_draw_source = source_root / "MultiGenus" / "planar_draw.c"

        for source in (page_source, multi_genus_source, planar_draw_source):
            if not source.is_file():
                raise FileNotFoundError(
                    f"Required native source file is missing from the package: {source}"
                )

        target_platform = os.environ.get("GRAPH_GENUS_TARGET_PLATFORM", sys.platform)
        is_windows_target = target_platform.startswith("win")
        exe = ".exe" if is_windows_target else ""
        cc = os.environ.get("CC") or sysconfig.get_config_var("CC") or "cc"
        cc_parts = shlex.split(cc)

        commands = [
            cc_parts
            + [
                "-O3",
                "-std=c17",
                "-o",
                str(bin_dir / f"page{exe}"),
                str(page_source),
            ],
            cc_parts
            + [
                "-O3",
                "-DLONG",
                "-o",
                str(bin_dir / f"multi_genus{exe}"),
                str(multi_genus_source),
                "-lm",
            ],
            cc_parts
            + [
                "-O3",
                "-std=gnu89",
                "-o",
                str(bin_dir / f"planar_draw{exe}"),
                str(planar_draw_source),
                "-lm",
            ],
        ]

        if not is_windows_target:
            commands[0].append("-pthread")

        for command in commands:
            output = Path(command[command.index("-o") + 1]).name
            self.announce("building " + output, level=3)
            subprocess.check_call(command)


setup(
    name="graph-genus",
    version="0.1.1",
    description="Python bindings for various graph genus and embedding tools",
    long_description=Path("README.md").read_text(encoding="utf-8"),
    long_description_content_type="text/markdown",
    url="https://github.com/SanderGi/Genus",
    author="Alexander Metzger, Austin Ulrigg, Gunnar Brinkmann",
    author_email="alex@sandergi.com",
    license="GPL-2.0-only",
    python_requires=">=3.8",
    project_urls={
        "Homepage": "https://genus.sandergi.com",
        "Repository": "https://github.com/SanderGi/Genus",
    },
    package_dir={"": "src"},
    packages=find_packages("src"),
    package_data={"graph_genus": ["bin/*"]},
    distclass=BinaryDistribution,
    cmdclass={
        "build_py": build_py_with_native_tools,
        "bdist_wheel": bdist_wheel,
    },
)
