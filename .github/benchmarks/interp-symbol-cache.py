"""Measure full Mathlib builds in a dedicated checkout with two pinned toolchains."""

import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import shlex
import shutil
import statistics
import subprocess
import sys
import time

ROOT = Path.cwd().resolve()
OUT = Path(os.environ["BENCH_OUTPUT"]).resolve()
TOOLCHAINS = Path(os.environ["BENCH_TOOLCHAINS"]).resolve()
COMMITS = {
    "baseline": "baeedf0cbafeff325f77b76e540f09d291f6f038",
    "patched": "8001cf3a43a2de1350f6d1dcc0a51cd7e8f469ee",
}
MATHLIB = "9151b29138f46990b9502c758ed0567ea14843e6"
ORDER = os.environ.get("BENCH_ORDER", "baseline-patched").split("-")
MODE = os.environ.get("BENCH_MODE", "timings")
PAIRS = int(os.environ.get("BENCH_PAIRS", "2"))
if sorted(ORDER) != ["baseline", "patched"] or MODE not in ("timings", "profile"):
    raise ValueError("Invalid benchmark order or mode")
if not 1 <= PAIRS <= 5:
    raise ValueError("BENCH_PAIRS must be between 1 and 5")
OUT.mkdir(parents=True, exist_ok=True)
MANIFEST = (ROOT / "lake-manifest.json").read_bytes()
PACKAGES = json.loads(MANIFEST)["packages"]
COMPAT_PATCH = Path(__file__).with_name("batteries-compat.patch").resolve()
COMPAT_FILE = "Batteries/Data/Float/Lemmas.lean"
COMPAT_FILE_SHA256 = "23b9e136777efacf960b138bc9a9010acdebb6d3b4248d355043cbd672f366b3"


def save(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + "\n")


def output(args, **kwargs):
    return subprocess.check_output(args, text=True, **kwargs).strip()


def optional_file(name):
    path = Path(name)
    return path.read_text() if path.exists() else None


def install(variant, profile=False):
    return TOOLCHAINS / (f"profile-{variant}" if profile else f"lean-{variant}")


def environment(variant, profile=False):
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN", "LAKE", "LAKE_HOME", "LEAN_GITHASH"):
        env.pop(key, None)
    env.update(
        PATH=f"{install(variant, profile) / 'bin'}:{env['PATH']}",
        LEAN_SYSROOT=str(install(variant, profile)),
        LAKE_OVERRIDE_LEAN="true", LAKE_NO_CACHE="true",
        LAKE_ARTIFACT_CACHE="false", LAKE_RESTORE_ARTIFACTS="false",
        MATHLIB_NO_CACHE_ON_UPDATE="1", LEAN_ABORT_ON_PANIC="1",
        TMPDIR=str(ROOT / ".lake/tmp"),
    )
    return env


def clear_builds():
    # The workflow provides a fresh, dedicated source checkout for this experiment.
    paths = [ROOT / ".lake/build"]
    paths += [ROOT / ".lake/packages" / p["name"] / ".lake/build" for p in PACKAGES]
    for path in paths:
        if path.exists():
            if path.is_symlink():
                raise RuntimeError(f"Refuse to clean a symlink: {path}")
            shutil.rmtree(path)


def check_sources(dependencies=True, compatibility=True):
    if output(["git", "rev-parse", "HEAD"], cwd=ROOT) != MATHLIB:
        raise RuntimeError("Wrong Mathlib revision")
    if output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=ROOT):
        raise RuntimeError("Tracked Mathlib source changed")
    if (ROOT / "lake-manifest.json").read_bytes() != MANIFEST:
        raise RuntimeError("Manifest changed")
    if dependencies:
        for package in PACKAGES:
            path = ROOT / ".lake/packages" / package["name"]
            if output(["git", "rev-parse", "HEAD"], cwd=path) != package["rev"]:
                raise RuntimeError(f"Wrong dependency revision: {package['name']}")
            if package["name"] == "batteries" and compatibility:
                changed = output(["git", "diff", "--name-only", "HEAD"], cwd=path)
                digest = hashlib.sha256((path / COMPAT_FILE).read_bytes()).hexdigest()
                if changed != COMPAT_FILE or digest != COMPAT_FILE_SHA256:
                    raise RuntimeError("Batteries compatibility patch changed")
            elif output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=path):
                raise RuntimeError(f"Dependency source changed: {package['name']}")


def apply_compatibility_patch():
    path = ROOT / ".lake/packages/batteries"
    subprocess.run(["git", "apply", "--check", str(COMPAT_PATCH)], cwd=path, check=True)
    subprocess.run(["git", "apply", str(COMPAT_PATCH)], cwd=path, check=True)
    shutil.copyfile(COMPAT_PATCH, OUT / COMPAT_PATCH.name)
    check_sources()


def run_logged(variant, args, name, network=False, profile=False):
    command = [str(install(variant) / "bin/lake"), "-KCI", "--fail-fast", *args]
    env = environment(variant, profile)
    (ROOT / ".lake/tmp").mkdir(parents=True, exist_ok=True)
    if os.environ.get("BENCH_LANDRUN") == "1":
        sandbox = ["landrun"]
        sandbox += (["--unrestricted-network", "--rox", "/etc"] if network
                    else ["--ro", "/etc/timezone"])
        sandbox += ["--rox", "/usr", "--rw", "/dev", "--rox", str(ROOT),
                    "--rox", str(TOOLCHAINS), "--rw", str(ROOT / ".lake"), "--rw", str(OUT)]
        for key in ("PATH", "HOME", "CI", "LEAN_SYSROOT", "LEAN_NUM_THREADS", "LAKE_OVERRIDE_LEAN",
                    "LAKE_NO_CACHE", "LAKE_ARTIFACT_CACHE", "LAKE_RESTORE_ARTIFACTS",
                    "MATHLIB_NO_CACHE_ON_UPDATE", "LEAN_ABORT_ON_PANIC", "TMPDIR"):
            if key in env:
                sandbox += ["--env", key]
        command = [*sandbox, "--", *command]
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.monotonic()
    load_before = os.getloadavg()
    with (OUT / f"{name}.log").open("w") as log:
        process = subprocess.Popen(command, env=env, stdout=log, stderr=log)
        while True:
            try:
                process.wait(timeout=60)
                break
            except subprocess.TimeoutExpired:
                print(f"{name}: {time.monotonic() - started:.0f}s elapsed", flush=True)
    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    metrics = {
        "wall_seconds": time.monotonic() - started,
        "user_seconds": usage_after.ru_utime - usage_before.ru_utime,
        "system_seconds": usage_after.ru_stime - usage_before.ru_stime,
        "load_before": load_before, "load_after": os.getloadavg(), "exit_code": process.returncode,
    }
    metrics["cpu_seconds"] = metrics["user_seconds"] + metrics["system_seconds"]
    save(f"{name}.resources.json", metrics)
    if process.returncode:
        print((OUT / f"{name}.log").read_text()[-10000:], flush=True)
        raise RuntimeError(f"{name} failed; its timing is invalid")
    return metrics


def make_profile_install(variant):
    original, target = install(variant), install(variant, True)
    target.mkdir()
    for entry in original.iterdir():
        if entry.name != "bin":
            (target / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
    (target / "bin").mkdir()
    for entry in (original / "bin").iterdir():
        if entry.name != "lean":
            (target / "bin" / entry.name).symlink_to(entry)
    wrapper = target / "bin/lean"
    wrapper.write_text(f"#!/bin/sh\nexec {shlex.quote(str(original / 'bin/lean'))} --profile \"$@\"\n")
    wrapper.chmod(0o755)


def main():
    check_sources(dependencies=False)
    versions = {}
    for variant, commit in COMMITS.items():
        binary = install(variant) / "bin/lean"
        if output([str(binary), "--githash"]) != commit:
            raise RuntimeError(f"Wrong {variant} Lean revision")
        versions[variant] = output([str(binary), "--version"])
    save("metadata.json", {
        "mathlib_commit": MATHLIB, "lean_commits": COMMITS, "lean_versions": versions,
        "manifest_sha256": hashlib.sha256(MANIFEST).hexdigest(), "dependencies": PACKAGES,
        "compatibility_patch_sha256": hashlib.sha256(COMPAT_PATCH.read_bytes()).hexdigest(),
        "compatibility_file": COMPAT_FILE, "compatibility_file_sha256": COMPAT_FILE_SHA256,
        "mode": MODE, "first_order": ORDER, "pairs": PAIRS,
        "threads": os.environ.get("LEAN_NUM_THREADS", "Lean default"),
        "platform": platform.platform(), "cpu_count": os.cpu_count(),
        "cpu": output(["lscpu"]) if shutil.which("lscpu") else output(["sysctl", "-n", "machdep.cpu.brand_string"]),
        "memory": optional_file("/proc/meminfo"), "runner": os.environ.get("RUNNER_NAME"),
        "cpu_limit": optional_file("/sys/fs/cgroup/cpu.max"),
        "affinity": sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None,
    })
    run_logged(ORDER[0], ["env", "true"], "fetch-dependencies", network=True)
    check_sources(compatibility=False)
    apply_compatibility_patch()
    # Dependency compatibility fails early, before either full-build measurement.
    for variant in ORDER:
        clear_builds()
        run_logged(variant, ["env", "true"], f"configure-preflight-{variant}")
        run_logged(variant, ["build", "--no-cache", "--no-ansi", "Batteries", "Mathlib.Data.String.Basic"],
                   f"preflight-{variant}")
        check_sources()
    if MODE == "profile":
        for variant in ORDER:
            make_profile_install(variant)
    rows, modules_before = [], None
    # A profile pair is diagnostic; it never contributes to the speedup table.
    for pair in range(PAIRS if MODE == "timings" else 1):
        for variant in (ORDER if pair % 2 == 0 else ORDER[::-1]):
            clear_builds()
            run_logged(variant, ["env", "true"], f"configure-{pair}-{variant}")
            check_sources()
            name = f"{MODE}-{pair}-{variant}"
            print(f"Starting {name}", flush=True)
            metrics = run_logged(variant, ["build", "--no-cache", "--no-ansi", "Mathlib"], name,
                                 profile=MODE == "profile")
            check_sources()
            build = ROOT / ".lake/build/lib/lean"
            modules = sorted(str(p.relative_to(build)) for p in build.rglob("*.olean"))
            if "Mathlib.olean" not in modules:
                raise RuntimeError("Incomplete Mathlib build")
            if modules_before is not None and modules != modules_before:
                raise RuntimeError("Builds cover different modules")
            modules_before = modules
            save(f"{name}.modules.json", modules)
            rows.append({"pair": pair, "variant": variant, "modules": len(modules), **metrics})
            save("results.json", rows)
    if MODE == "timings":
        reductions = []
        for pair in range(PAIRS):
            by_variant = {r["variant"]: r for r in rows if r["pair"] == pair}
            reductions.append({metric: 100 * (1 - by_variant["patched"][metric] / by_variant["baseline"][metric])
                               for metric in ("wall_seconds", "cpu_seconds", "user_seconds", "system_seconds")
                               if by_variant["baseline"][metric] > 0})
        save("paired-reductions-percent.json", reductions)
        print("Paired reductions (%):", json.dumps(reductions), flush=True)
        summary = {metric: {
            "median_reduction_percent": statistics.median(r[metric] for r in reductions),
            "minimum_reduction_percent": min(r[metric] for r in reductions),
            "maximum_reduction_percent": max(r[metric] for r in reductions),
        } for metric in ("wall_seconds", "cpu_seconds")}
        save("summary.json", summary)
        print("Summary:", json.dumps(summary), flush=True)
    save("status.json", {"status": "complete", "mode": MODE})


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        save("status.json", {"status": "failed", "error": str(error)})
        raise
