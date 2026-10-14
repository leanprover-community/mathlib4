"""Compare clean Mathlib builds with two pinned Lean toolchains on one CI runner."""

import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import time


ROOT = Path.cwd()
OUT = ROOT / "benchmark-results"
TOOLCHAINS = Path(os.environ["BENCH_TOOLCHAINS"])
COMMITS = {
    "baseline": "daa56019e0ab113c164f5e13e6c9dae9d994c21b",
    "patched": "f6b1bccef618e92ed1dfb68b1ded48a8f441386f",
}
ORDER = os.environ["BENCH_ORDER"].split("-")
assert sorted(ORDER) == ["baseline", "patched"]
OUT.mkdir(exist_ok=True)
MANIFEST = (ROOT / "lake-manifest.json").read_bytes()
PACKAGES = json.loads(MANIFEST)["packages"]
SOURCE_DIFFS = {p["name"]: "" for p in PACKAGES}
ADAPTATION = ROOT / ".github/benchmarks/batteries-compat.patch"
DEPENDENCY_TARGETS = ["Batteries", "Qq", "Aesop", "ProofWidgets", "ImportGraph",
                      "LeanSearchClient", "Plausible", "Cli"]


def save(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + "\n")


def output(args, **kwargs):
    return subprocess.check_output(args, text=True, **kwargs).strip()


def environment(variant):
    toolchain = TOOLCHAINS / f"lean-{variant}"
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN", "LAKE", "LAKE_HOME", "LEAN_GITHASH"):
        env.pop(key, None)
    env.update(
        PATH=f"{toolchain / 'bin'}:{env['PATH']}",
        LEAN_SYSROOT=str(toolchain),
        LAKE_OVERRIDE_LEAN="true",
        LAKE_NO_CACHE="true",
        LAKE_ARTIFACT_CACHE="false",
        LAKE_RESTORE_ARTIFACTS="false",
        MATHLIB_NO_CACHE_ON_UPDATE="1",
        LEAN_ABORT_ON_PANIC="1",
        TMPDIR=str(ROOT / ".lake/tmp"),
    )
    return env


def lake(variant, args):
    return [str(TOOLCHAINS / f"lean-{variant}" / "bin/lake"), "-KCI", "--fail-fast", *args]


def clear_builds():
    # These are only build directories in this job's fresh checkout.
    paths = [ROOT / ".lake/build"]
    paths += [ROOT / ".lake/packages" / p["name"] / ".lake/build" for p in PACKAGES]
    for path in paths:
        if path.exists():
            shutil.rmtree(path)


def check_sources():
    assert (ROOT / "lake-manifest.json").read_bytes() == MANIFEST
    for package in PACKAGES:
        path = ROOT / ".lake/packages" / package["name"]
        assert output(["git", "rev-parse", "HEAD"], cwd=path) == package["rev"]
        assert output(["git", "diff", "HEAD"], cwd=path) == SOURCE_DIFFS[package["name"]]


def run_logged(variant, args, name, timed=False):
    command = lake(variant, args)
    env = environment(variant)
    (ROOT / ".lake/tmp").mkdir(parents=True, exist_ok=True)
    if os.environ.get("BENCH_LANDRUN") == "1":
        # Only dependency materialization has network access. Lake and Lean run
        # without credentials and can only write job-local outputs and .lake.
        sandbox = ["landrun"]
        if name == "fetch-dependencies":
            sandbox += ["--unrestricted-network", "--rox", "/etc"]
        else:
            sandbox += ["--ro", "/etc/timezone"]
        sandbox += ["--rox", "/usr", "--rw", "/dev", "--rox", str(ROOT),
                    "--rox", str(TOOLCHAINS / f"lean-{variant}"),
                    "--rw", str(ROOT / ".lake"), "--rw", str(OUT)]
        for key in ("PATH", "HOME", "CI", "LEAN_SYSROOT", "LEAN_NUM_THREADS", "LAKE_OVERRIDE_LEAN",
                    "LAKE_NO_CACHE", "LAKE_ARTIFACT_CACHE", "LAKE_RESTORE_ARTIFACTS",
                    "MATHLIB_NO_CACHE_ON_UPDATE", "LEAN_ABORT_ON_PANIC", "TMPDIR"):
            if key in env:
                sandbox += ["--env", key]
        command = [*sandbox, "--", *command]
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.monotonic()
    with (OUT / f"{name}.log").open("w") as log:
        process = subprocess.Popen(command, env=env, stdout=log, stderr=log)
        while True:
            try:
                code = process.wait(timeout=60)
                break
            except subprocess.TimeoutExpired:
                count = len(list((ROOT / ".lake/build/lib/lean/Mathlib").rglob("*.olean")))
                print(f"{name}: {time.monotonic() - started:.0f} seconds, {count} Mathlib modules", flush=True)
    seconds = time.monotonic() - started
    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    if code:
        log_text = (OUT / f"{name}.log").read_text()
        lines = log_text.splitlines()
        context = set()
        for i, line in enumerate(lines):
            if line.startswith(("error:", "warning:", "✖")):
                context.update(range(max(0, i - 1), min(len(lines), i + 20)))
        print("\n".join(lines[i] for i in sorted(context))[:20000], flush=True)
        print(log_text[-4000:], flush=True)
        raise RuntimeError(f"{name} failed with exit code {code}; exclude its timing")
    if timed:
        save(f"{name}.resources.json", {
            "user_seconds": usage_after.ru_utime - usage_before.ru_utime,
            "system_seconds": usage_after.ru_stime - usage_before.ru_stime,
        })
    return seconds


def prepare():
    versions = {}
    for variant, commit in COMMITS.items():
        executable = TOOLCHAINS / f"lean-{variant}" / "bin/lean"
        actual = output([str(executable), "--githash"])
        assert actual == commit, (variant, actual, commit)
        versions[variant] = output([str(executable), "--version"])
    save("metadata.json", {
        "mathlib_commit": output(["git", "rev-parse", "HEAD"]),
        "lean_commits": COMMITS, "lean_versions": versions, "order": ORDER,
        "manifest_sha256": hashlib.sha256(MANIFEST).hexdigest(),
        "batteries_adaptation_sha256": hashlib.sha256(ADAPTATION.read_bytes()).hexdigest(),
        "dependencies": PACKAGES, "threads": os.environ.get("LEAN_NUM_THREADS", "Lean default"),
        "uname": output(["uname", "-a"]), "cpu": output(["lscpu"]),
        "memory": Path("/proc/meminfo").read_text(),
        "runner_name": os.environ.get("RUNNER_NAME"),
        "cpu_limit": Path("/sys/fs/cgroup/cpu.max").read_text()
        if Path("/sys/fs/cgroup/cpu.max").exists() else None,
    })
    run_logged(ORDER[0], ["env", "true"], "fetch-dependencies")
    check_sources()
    batteries = ROOT / ".lake/packages/batteries"
    subprocess.run(["git", "apply", "--check", str(ADAPTATION)], cwd=batteries, check=True)
    subprocess.run(["git", "apply", str(ADAPTATION)], cwd=batteries, check=True)
    SOURCE_DIFFS["batteries"] = output(["git", "diff", "HEAD"], cwd=batteries)
    (OUT / "batteries-adaptation.diff").write_text(SOURCE_DIFFS["batteries"] + "\n")
    for variant in ORDER:
        # Materialize the manifest pins and compile configuration outside the timer.
        run_logged(variant, ["env", "true"], f"prepare-{variant}")
        check_sources()
        clear_builds()
        # Check all dependency libraries before either full Mathlib build.
        run_logged(variant, ["build", "--no-cache", "--no-ansi", "--wfail", *DEPENDENCY_TARGETS],
                   f"preflight-{variant}")
        print(f"All dependency libraries pass with {variant}", flush=True)
    check_sources()
    save("preflight.json", {"lean_commits": COMMITS,
                            "manifest_sha256": hashlib.sha256(MANIFEST).hexdigest(),
                            "adaptation_sha256": hashlib.sha256(ADAPTATION.read_bytes()).hexdigest()})


def measure():
    preflight = json.loads((OUT / "preflight.json").read_text())
    assert preflight == {"lean_commits": COMMITS,
                         "manifest_sha256": hashlib.sha256(MANIFEST).hexdigest(),
                         "adaptation_sha256": hashlib.sha256(ADAPTATION.read_bytes()).hexdigest()}
    SOURCE_DIFFS["batteries"] = (OUT / "batteries-adaptation.diff").read_text().strip()
    check_sources()
    rows = []
    outputs = None
    for index, variant in enumerate(ORDER):
        clear_builds()
        run_logged(variant, ["env", "true"], f"configure-{variant}")
        check_sources()
        name = f"{index}-{variant}"
        print(f"Starting clean full Mathlib build: {name}", flush=True)
        save("status.json", {"status": "running", "variant": variant, "index": index})
        seconds = run_logged(variant, ["build", "--no-cache", "--no-ansi", "--wfail", "Mathlib"], name, timed=True)
        check_sources()
        build = ROOT / ".lake/build/lib/lean"
        modules = sorted(str(p.relative_to(build)) for p in build.rglob("*.olean"))
        assert "Mathlib.olean" in modules and len(modules) > 8000, "Incomplete Mathlib build"
        save(f"{name}.modules.json", modules)
        if outputs is not None:
            assert modules == outputs, "The builds cover different modules"
        outputs = modules
        row = {"variant": variant, "wall_seconds": seconds, "modules": len(modules),
               **json.loads((OUT / f"{name}.resources.json").read_text())}
        rows.append(row)
        save("results.json", rows)
        print(json.dumps(row), flush=True)

    baseline = next(r for r in rows if r["variant"] == "baseline")
    patched = next(r for r in rows if r["variant"] == "patched")
    reduction = 100 * (1 - patched["wall_seconds"] / baseline["wall_seconds"])
    summary = "Both clean full Mathlib builds pass. Dependencies rebuild in each run.\n\n"
    summary += "| Version | Wall seconds | User CPU seconds | System CPU seconds | Modules |\n"
    summary += "| --- | ---: | ---: | ---: | ---: |\n"
    for r in rows:
        summary += (f"| {r['variant']} | {r['wall_seconds']:.2f} | {r['user_seconds']:.2f} "
                    f"| {r['system_seconds']:.2f} | {r['modules']} |\n")
    summary += f"\nWall time reduction: {reduction:.2f}%. Order: {' then '.join(ORDER)}.\n"
    summary += "This pair runs on one runner. Repeat with the reverse order to check run-order effects.\n"
    (OUT / "summary.md").write_text(summary)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as handle:
            handle.write(summary)
    save("status.json", {"status": "complete", "reduction_percent": reduction})


if __name__ == "__main__":
    try:
        phase = sys.argv[1] if len(sys.argv) == 2 else "all"
        assert phase in ("prepare", "measure", "all"), "Expected prepare or measure"
        if phase in ("prepare", "all"):
            prepare()
        if phase in ("measure", "all"):
            measure()
    except Exception as error:
        save("status.json", {"status": "failed", "error": str(error)})
        raise
