#!/usr/bin/env python3

import json
import os
from pathlib import Path
from typing import Generator

OUTFILE = Path(os.environ["OUTPUT_FILE"])


def output_result(
    topic: str,
    category: str,
    value: float,
    unit: str | None = None,
) -> None:
    data = {"metric": f"{topic}//{category}", "value": value}
    if unit is not None:
        data["unit"] = unit
    with open(OUTFILE, "a") as f:
        f.write(f"{json.dumps(data)}\n")


def find_lean_files() -> Generator[Path, None, None]:
    for p in Path().iterdir():
        if p.name.startswith("."):
            continue
        elif p.is_dir():
            yield from p.glob("**/*.lean")
        elif p.name.endswith(".lean"):
            yield p


def measure_lines(topic: str, *paths: Path) -> None:
    for path in paths:
        if path.is_file():
            lines = len(path.read_text().splitlines())
            output_result(topic, "lines", lines)
            output_result(topic, "files", 1)


def measure_bytes(topic: str, *paths: Path) -> None:
    for path in paths:
        if path.is_file():
            bytes = path.stat().st_size
            output_result(topic, "bytes", bytes, "B")
            output_result(topic, "files", 1)


if __name__ == "__main__":
    measure_lines("size/.lean", *find_lean_files())
    measure_bytes("size/.olean", *Path().glob(".lake/build/**/*.olean"))
    measure_bytes("size/.olean.server", *Path().glob(".lake/build/**/*.olean.server"))
    measure_bytes("size/.olean.private", *Path().glob(".lake/build/**/*.olean.private"))
