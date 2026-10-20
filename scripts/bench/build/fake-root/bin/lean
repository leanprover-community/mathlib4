#!/usr/bin/env python3

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

# Global paths
BENCH_DIR = Path(os.environ["BENCH_DIR"])
WRAPPER_OUT = Path(os.environ["WRAPPER_OUT"])
WRAPPER_PREFIX = Path(os.environ["WRAPPER_PREFIX"])

# Other config
BENCHMARK = "build"

sys.path.append(str(BENCH_DIR))
import measure  # noqa: E402


def save_measurement(metric: str, value: float, unit: str | None = None) -> None:
    data = {"metric": metric, "value": value}
    if unit is not None:
        data["unit"] = unit
    with open(WRAPPER_OUT, "a") as f:
        f.write(f"{json.dumps(data)}\n")


def run(*command: str) -> None:
    result = subprocess.run(command)
    if result.returncode != 0:
        sys.exit(result.returncode)


def get_module(setup: Path) -> str:
    with open(setup) as f:
        return json.load(f)["name"]


def count_lines(module: str, path: Path) -> None:
    with open(path) as f:
        lines = sum(1 for _ in f)
    save_measurement(f"{BENCHMARK}/module/{module}//lines", lines)


def run_lean(module: str) -> None:
    _, stderr = measure.main(
        cmd=["lean", "--profile", "-Dprofiler.threshold=9999999", *sys.argv[1:]],
        output=WRAPPER_OUT,
        topics=[f"{BENCHMARK}/module/{module}"],
        metrics={"instructions"},
        append=True,
        capture=True,
    )

    # Output of `lean --profile`
    # See timeit.cpp for the time format
    for line in stderr.splitlines():
        if match := re.fullmatch(r"\t(.*) ([\d.]+)(m?s)", line):
            name = match.group(1)
            seconds = float(match.group(2))
            if match.group(3) == "ms":
                seconds = seconds / 1000
            save_measurement(f"{BENCHMARK}/profile/{name}//wall-clock", seconds, "s")


def main() -> None:
    if sys.argv[1:] == ["--print-prefix"]:
        print(WRAPPER_PREFIX)
        return

    if sys.argv[1:] == ["--githash"]:
        run("lean", "--githash")
        return

    parser = argparse.ArgumentParser()
    parser.add_argument("lean", type=Path)
    parser.add_argument("--setup", type=Path)
    args, _ = parser.parse_known_args()

    lean: Path = args.lean
    setup: Path = args.setup

    module = get_module(setup)
    count_lines(module, lean)
    run_lean(module)


if __name__ == "__main__":
    main()
