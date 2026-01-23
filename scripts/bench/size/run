#!/usr/bin/env python3

import json
from pathlib import Path

OUTFILE = Path() / "measurements.jsonl"


def output_result(metric: str, value: float, unit: str | None = None) -> None:
    data = {"metric": metric, "value": value}
    if unit is not None:
        data["unit"] = unit
    with open(OUTFILE, "a") as f:
        f.write(f"{json.dumps(data)}\n")


def measure_leans() -> None:
    lean_files = 0
    lean_lines = 0
    for path in Path().glob("Mathlib/**/*.lean"):
        lean_files += 1
        with open(path) as f:
            lean_lines += sum(1 for _ in f)
    output_result("size/.lean//files", lean_files)
    output_result("size/.lean//lines", lean_lines)


def measure_oleans() -> None:
    olean_files = 0
    olean_bytes = 0
    for path in Path().glob(".lake/build/**/*.olean"):
        olean_files += 1
        olean_bytes += path.stat().st_size
    output_result("size/.olean//files", olean_files)
    output_result("size/.olean//bytes", olean_bytes, "B")


if __name__ == "__main__":
    measure_leans()
    measure_oleans()
