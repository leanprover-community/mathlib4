#!/usr/bin/env python3
"""
Part of the `@[expose]` removal-candidate reporting pipeline
(see `scripts/expose_enumerate.lean` and `scripts/build_with_diagnostics.py`).

Joins the enumeration of exposed decls (from `lake exe expose_enumerate`)
with per-file unfold diagnostics (from `build_with_diagnostics.py`) and
produces:

  scripts/.expose_report/report.jsonl   — one record per exposed decl
  scripts/.expose_report/report.tsv     — sorted TSV, zero-usage rows first
  scripts/.expose_report/summary.md     — aggregate counts

Each report record carries:
  name, kind, module, file, line, col, effect
  downstream_usage    — total cross-module unfold count observed
  num_using_files     — count of distinct files that unfolded the decl
  top_using_files     — up to 5 (file, count) pairs sorted descending

"Downstream" means files other than the module that declared the decl.
Same-module unfolds are filtered out (a file can always unfold its own
locally-visible defs, regardless of `@[expose]`).

Zero-`downstream_usage` rows with `effect = "exposed"` are the primary
actionable output: decls where `@[expose]` can be removed without affecting
any observed downstream unfold. `effect = "noop-always-exported"` zero-usage
rows (abbrevs) are also safe to un-expose, but trivially so.

Limitations inherited from the signal:
  * Unfold-based only; metaprograms inspecting `ConstantInfo.value?` don't
    appear. A zero-usage row may still be load-bearing via metaprogramming.
  * Lean's threshold is strictly `>`, so single-unfold events still count.

Usage:
  python3 scripts/expose_report.py
"""

import argparse
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
OUTPUT_DIR = REPO_ROOT / "scripts" / ".expose_report"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--exposed", type=Path,
                    default=OUTPUT_DIR / "exposed.jsonl",
                    help="enumeration JSONL from `lake exe expose_enumerate`")
    ap.add_argument("--diagnostics", type=Path,
                    default=OUTPUT_DIR / "diagnostics.jsonl",
                    help="per-unfold JSONL from build_with_diagnostics.py")
    ap.add_argument("--static-refs", type=Path,
                    default=OUTPUT_DIR / "static_refs.jsonl",
                    help="static-reference JSONL from `lake exe expose_static_refs`. "
                         "Optional but recommended: catches typeclass-projection "
                         "sources that diagnostics misses. Use --no-static-refs "
                         "to disable.")
    ap.add_argument("--no-static-refs", action="store_true",
                    help="ignore static_refs.jsonl even if present")
    ap.add_argument("--decl-refs", type=Path,
                    default=OUTPUT_DIR / "decl_refs.jsonl",
                    help="per-decl reference list from "
                         "`lake exe expose_static_refs decl`. Used for "
                         "one-hop transitive-closure: a downstream use of "
                         "decl `K` propagates to mark every decl in `K`'s "
                         "body as also used (catches typeclass-projection "
                         "chains like `instLattice → instSemilatticeSup`).")
    ap.add_argument("--no-transitive", action="store_true",
                    help="don't apply one-hop transitive closure on static refs")
    ap.add_argument("--out-jsonl", type=Path,
                    default=OUTPUT_DIR / "report.jsonl")
    ap.add_argument("--out-tsv", type=Path,
                    default=OUTPUT_DIR / "report.tsv")
    ap.add_argument("--out-summary", type=Path,
                    default=OUTPUT_DIR / "summary.md")
    args = ap.parse_args()

    if not args.exposed.exists():
        print(f"error: exposed JSONL missing: {args.exposed}", file=sys.stderr)
        return 2
    if not args.diagnostics.exists():
        print(f"error: diagnostics JSONL missing: {args.diagnostics}", file=sys.stderr)
        return 2

    # Load enumeration: name -> record.
    exposed: dict[str, dict] = {}
    for raw in open(args.exposed):
        r = json.loads(raw)
        exposed[r["name"]] = r

    # Aggregate cross-module uses from both signals:
    #   diagnostics.jsonl  - unfold-based use captured by `set_option diagnostics true`
    #   static_refs.jsonl  - literal `Expr.const` references in elaborated bodies
    # Both sources have the same record shape; we sum counts.
    usage: Counter = Counter()
    using_file_counts: dict[str, Counter] = defaultdict(Counter)

    def absorb(path: Path) -> int:
        n = 0
        for raw in open(path):
            d = json.loads(raw)
            decl = d["decl"]
            rec = exposed.get(decl)
            if rec is None:
                continue
            if d["file"] == rec["file"]:
                continue  # same-module use, not a downstream signal
            usage[decl] += d["count"]
            using_file_counts[decl][d["file"]] += d["count"]
            n += 1
        return n

    diag_n = absorb(args.diagnostics)
    print(f"[expose_report] absorbed {diag_n} diagnostics records",
          file=sys.stderr)
    if not args.no_static_refs and args.static_refs.exists():
        sref_n = absorb(args.static_refs)
        print(f"[expose_report] absorbed {sref_n} static-reference records",
              file=sys.stderr)
    elif args.no_static_refs:
        print(f"[expose_report] static refs disabled by --no-static-refs",
              file=sys.stderr)
    else:
        print(f"[expose_report] static_refs.jsonl not found; using diagnostics only",
              file=sys.stderr)

    # One-hop transitive closure: if downstream module M uses decl K, also
    # mark every decl K's body references as used by M. Captures cases like
    # `M` uses `instLattice`, whose body anonymous-constructs from
    # `instSemilatticeSup`/`instSemilatticeInf`, which then need to be exposed
    # for downstream projection to find their fields.
    if not args.no_transitive and args.decl_refs.exists():
        decl_refs: dict[str, list[str]] = {}
        for raw in open(args.decl_refs):
            d = json.loads(raw)
            decl_refs[d["decl"]] = d["refs"]
        # For each used (decl, file) pair, propagate to (ref, file) for ref ∈ decl_refs[decl].
        propagated = 0
        # snapshot the current using_file_counts so iteration is stable
        snapshot = [(decl, dict(files)) for decl, files in using_file_counts.items()]
        for decl, files in snapshot:
            for ref in decl_refs.get(decl, []):
                rec = exposed.get(ref)
                if rec is None:
                    continue
                for file, count in files.items():
                    if file == rec["file"]:
                        continue  # same-module
                    usage[ref] += count
                    using_file_counts[ref][file] += count
                    propagated += 1
        print(f"[expose_report] one-hop transitive: propagated {propagated} extra (ref,file) edges",
              file=sys.stderr)

    # Build and sort report records.
    records: list[dict] = []
    for name, rec in exposed.items():
        u = usage.get(name, 0)
        top5 = using_file_counts.get(name, Counter()).most_common(5)
        records.append({
            **rec,
            "downstream_usage": u,
            "num_using_files": len(using_file_counts.get(name, {})),
            "top_using_files": [
                {"file": f, "count": c} for f, c in top5
            ],
        })
    records.sort(key=lambda r: (r["downstream_usage"], r["module"], r["line"]))

    args.out_jsonl.parent.mkdir(parents=True, exist_ok=True)
    with open(args.out_jsonl, "w") as f:
        for r in records:
            f.write(json.dumps(r, separators=(",", ":")) + "\n")

    with open(args.out_tsv, "w") as f:
        f.write("name\tkind\teffect\tmodule\tsource\tdownstream_usage"
                "\tnum_using_files\ttop_using_files\n")
        for r in records:
            top = ";".join(f"{x['file']}:{x['count']}"
                           for x in r["top_using_files"])
            f.write(
                f"{r['name']}\t{r['kind']}\t{r['effect']}\t{r['module']}\t"
                f"{r['file']}:{r['line']}\t{r['downstream_usage']}\t"
                f"{r['num_using_files']}\t{top}\n"
            )

    total = len(records)
    zero = sum(1 for r in records if r["downstream_usage"] == 0)
    zero_noop = sum(1 for r in records
                    if r["downstream_usage"] == 0
                    and r["effect"] == "noop-always-exported")
    zero_exp = zero - zero_noop
    low = sum(1 for r in records if 1 <= r["downstream_usage"] <= 5)
    high = sum(1 for r in records if r["downstream_usage"] > 5)

    with open(args.out_summary, "w") as f:
        f.write(
            f"# `@[expose]` removal-candidate report\n\n"
            f"- Total decls tracked: **{total}**\n"
            f"- Zero downstream usage: **{zero}** (candidates for un-exposing)\n"
            f"    - `effect = exposed` (meaningful removals): **{zero_exp}**\n"
            f"    - `effect = noop-always-exported` (trivial no-ops): **{zero_noop}**\n"
            f"- Low usage (1–5 unfolds): **{low}**\n"
            f"- High usage (>5 unfolds): **{high}**\n\n"
            f"Sorted report: `report.tsv`\n"
            f"Full records:  `report.jsonl`\n"
            f"\n"
            f"Caveat: the signal is unfold-based. Decls inspected by\n"
            f"metaprograms without a WHNF unfold will not appear in any\n"
            f"category, so a zero-usage row may still be load-bearing in\n"
            f"practice. Verify by temporarily un-exposing a candidate and\n"
            f"checking the build.\n"
        )

    print(f"[expose_report] {total} rows, {zero} zero-usage "
          f"({zero_exp} meaningful, {zero_noop} noop-always-exported)",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
