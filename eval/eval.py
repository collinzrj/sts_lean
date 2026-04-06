#!/usr/bin/env python3
"""
Eval script for StS infinite combo verification benchmark.

Usage:
  # Step 1: Before giving agent access, generate checksums of read-only files
  python eval.py snapshot [framework_dir]

  # Step 2: After agent finishes, run grading
  python eval.py grade [framework_dir] [--timeout 300] [--memory-gb 16]

Default framework_dir is the directory containing this script.
The snapshot command writes checksums.json in the framework directory.
The grade command checks integrity + builds each test case + audits axioms.
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

COMBOS = [
    "ComboDropkickExhaust",
    "ComboCorruptionDropkick",
    "ComboAcrobaticsTactician",
    "ComboHeelHookExhaust",
    "ComboStreamlineHologram",
    "ComboStandardWatcher",
    "ComboMantraDivine",
    "ComboTantrumFearNoEvil",
    "ComboStormOfSteel",
    "ComboStormOfSteel2Prep",
    "ComboStormOfSteel3Prep",
    "ComboStormStrike",
]

LEVELS = ["L1", "L2"]

# Axioms that are acceptable in a valid proof
ALLOWED_AXIOMS = {
    "propext",
    "Lean.ofReduceBool",
    "Quot.sound",
    "Classical.choice",
}

LEVEL_DIR = {"L1": "CombosTemplateL1", "L2": "CombosTemplateL2"}
LEVEL_MODULE_PREFIX = {
    "L1": "StSVerify.CombosTemplateL1",
    "L2": "StSVerify.CombosTemplateL2",
}
LEVEL_THEOREM_SUFFIX = {"L1": "_L1_verified", "L2": "_L2_verified"}


def get_readonly_files(framework_dir: Path) -> list[str]:
    """Return list of read-only file paths relative to framework_dir."""
    readonly = []

    # Core engine files
    for name in [
        "StSVerify/Engine.lean",
        "StSVerify/EngineHelperLemmas.lean",
        "StSVerify/CardDB.lean",
        "StSVerify/ExtendedTargets.lean",
        "Main.lean",
        "lakefile.toml",
        "lean-toolchain",
    ]:
        p = framework_dir / name
        if p.exists():
            readonly.append(name)

    # Spec files (L1 + L2)
    for level_dir in ["CombosSpecL1", "CombosSpecL2"]:
        d = framework_dir / "StSVerify" / level_dir
        if d.exists():
            for f in sorted(d.glob("*.lean")):
                readonly.append(f"StSVerify/{level_dir}/{f.name}")

    # Template/checker files (L1 + L2)
    for level_dir in ["CombosTemplateL1", "CombosTemplateL2"]:
        d = framework_dir / "StSVerify" / level_dir
        if d.exists():
            for f in sorted(d.glob("*.lean")):
                readonly.append(f"StSVerify/{level_dir}/{f.name}")

    return readonly


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()


def cmd_snapshot(framework_dir: Path):
    """Generate checksums.json for all read-only files."""
    readonly = get_readonly_files(framework_dir)
    checksums = {}
    for rel in readonly:
        p = framework_dir / rel
        checksums[rel] = sha256_file(p)
    out = framework_dir / "eval" / "checksums.json"
    with open(out, "w") as f:
        json.dump(checksums, f, indent=2)
    print(f"Snapshot saved: {out} ({len(checksums)} files)")


def check_integrity(framework_dir: Path) -> tuple[bool, list[str]]:
    """Check read-only files against saved checksums. Returns (ok, violations)."""
    cs_path = framework_dir / "eval" / "checksums.json"
    if not cs_path.exists():
        return False, ["checksums.json not found — run 'snapshot' first"]

    with open(cs_path) as f:
        saved = json.load(f)

    violations = []
    for rel, expected_hash in saved.items():
        p = framework_dir / rel
        if not p.exists():
            violations.append(f"DELETED: {rel}")
        elif sha256_file(p) != expected_hash:
            violations.append(f"MODIFIED: {rel}")

    return len(violations) == 0, violations


def find_lake() -> str:
    """Find the lake binary."""
    for candidate in [
        os.path.expanduser("~/.elan/bin/lake"),
        "lake",
    ]:
        try:
            subprocess.run(
                [candidate, "--version"],
                capture_output=True,
                timeout=10,
            )
            return candidate
        except (FileNotFoundError, subprocess.TimeoutExpired):
            continue
    raise RuntimeError("Could not find 'lake' binary. Is Lean/elan installed?")


def build_and_check(
    framework_dir: Path,
    combo: str,
    level: str,
    lake_bin: str,
    timeout: int,
    memory_gb: int,
) -> dict:
    """Build one checker module and audit its axioms.

    Returns dict with keys: combo, level, status, axioms, error, time_s
    """
    module = f"{LEVEL_MODULE_PREFIX[level]}.{combo}"
    theorem = f"{combo}{LEVEL_THEOREM_SUFFIX[level]}"
    result = {
        "combo": combo,
        "level": level,
        "status": "FAIL",
        "axioms": [],
        "error": "",
        "time_s": 0.0,
    }

    # Check solution file exists
    sol_dir = "CombosLevel1Solution" if level == "L1" else "CombosLevel2Solution"
    sol_file = framework_dir / "StSVerify" / sol_dir / f"{combo}.lean"
    if not sol_file.exists():
        result["error"] = f"Solution file missing: StSVerify/{sol_dir}/{combo}.lean"
        return result

    t0 = time.time()
    try:
        env = os.environ.copy()
        env["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + env.get("PATH", "")
        proc = subprocess.run(
            [lake_bin, "build", module],
            cwd=str(framework_dir),
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
        )
        elapsed = time.time() - t0
        result["time_s"] = round(elapsed, 1)

        output = proc.stdout + "\n" + proc.stderr

        # Check for build failure
        if proc.returncode != 0:
            result["error"] = f"Build failed (exit {proc.returncode})"
            err_lines = [
                l
                for l in output.splitlines()
                if "error" in l.lower() or "sorry" in l.lower()
            ]
            if err_lines:
                result["error"] += "\n" + "\n".join(err_lines[:5])
            return result

        # Parse #print axioms output
        # Format: 'TheoremName' depends on axioms: [ax1, ax2, ...]
        axiom_pattern = re.compile(
            rf"'{re.escape(theorem)}' depends on axioms: \[([^\]]*)\]"
        )
        match = axiom_pattern.search(output)
        if not match:
            axiom_pattern2 = re.compile(
                rf"{re.escape(theorem)} depends on axioms: \[([^\]]*)\]"
            )
            match = axiom_pattern2.search(output)

        if not match:
            result["error"] = "Could not find axiom audit in build output"
            return result

        axiom_str = match.group(1).strip()
        if axiom_str:
            axioms = [a.strip() for a in axiom_str.split(",")]
        else:
            axioms = []
        result["axioms"] = axioms

        # Check for forbidden axioms
        forbidden = set(axioms) - ALLOWED_AXIOMS
        if forbidden:
            result["error"] = f"Forbidden axioms: {forbidden}"
            return result

        result["status"] = "PASS"
        return result

    except subprocess.TimeoutExpired:
        result["time_s"] = round(time.time() - t0, 1)
        result["error"] = f"Timeout after {timeout}s"
        return result
    except Exception as e:
        result["time_s"] = round(time.time() - t0, 1)
        result["error"] = str(e)
        return result


def cmd_grade(framework_dir: Path, timeout: int, memory_gb: int):
    """Grade all test cases."""
    print("=" * 60)
    print("StS Infinite Combo Benchmark — Evaluation")
    print("=" * 60)

    # Step 1: Integrity check
    print("\n[1/3] Checking read-only file integrity...")
    ok, violations = check_integrity(framework_dir)
    if not ok:
        print("  INTEGRITY VIOLATION — agent modified read-only files:")
        for v in violations:
            print(f"    {v}")
        print("\n  RESULT: ALL TEST CASES FAILED (integrity violation)")
        sys.exit(1)
    print("  All read-only files intact.")

    # Step 2: Find lake
    print("\n[2/3] Locating build tools...")
    lake_bin = find_lake()
    print(f"  Using: {lake_bin}")

    # Step 3: Build and grade
    print("\n[3/3] Building and grading each test case...")
    print(f"  Timeout: {timeout}s per module | Memory limit: {memory_gb}GB")
    print()

    results = []
    for level in LEVELS:
        for combo in COMBOS:
            label = f"{level}/{combo}"
            print(f"  Building {label}...", end=" ", flush=True)
            r = build_and_check(
                framework_dir, combo, level, lake_bin, timeout, memory_gb
            )
            results.append(r)
            if r["status"] == "PASS":
                print(f"PASS ({r['time_s']}s)")
            else:
                print(f"FAIL — {r['error'][:80]}")

    # Summary
    print("\n" + "=" * 60)
    print("RESULTS SUMMARY")
    print("=" * 60)

    for level in LEVELS:
        level_results = [r for r in results if r["level"] == level]
        passed = sum(1 for r in level_results if r["status"] == "PASS")
        total = len(level_results)
        print(f"\n  {level}: {passed}/{total} passed")
        for r in level_results:
            mark = "PASS" if r["status"] == "PASS" else "FAIL"
            print(f"    [{mark}] {r['combo']}", end="")
            if r["status"] != "PASS" and r["error"]:
                print(f"  — {r['error'][:60]}", end="")
            print()

    total_pass = sum(1 for r in results if r["status"] == "PASS")
    total = len(results)
    print(f"\n  TOTAL: {total_pass}/{total} passed")

    # Write detailed results to JSON
    out_path = framework_dir / "eval" / "eval_results.json"
    with open(out_path, "w") as f:
        json.dump(
            {
                "integrity_ok": True,
                "total_pass": total_pass,
                "total": total,
                "results": results,
            },
            f,
            indent=2,
        )
    print(f"\n  Detailed results: {out_path}")

    return total_pass


def main():
    parser = argparse.ArgumentParser(description="StS Benchmark Evaluator")
    sub = parser.add_subparsers(dest="command", required=True)

    framework_default = Path(__file__).resolve().parent.parent

    snap = sub.add_parser("snapshot", help="Save checksums of read-only files")
    snap.add_argument("framework_dir", nargs="?", type=Path, default=framework_default)

    grade = sub.add_parser("grade", help="Grade agent submissions")
    grade.add_argument("framework_dir", nargs="?", type=Path, default=framework_default)
    grade.add_argument("--timeout", type=int, default=300, help="Build timeout per module (seconds)")
    grade.add_argument("--memory-gb", type=int, default=16, help="Memory limit (GB)")

    args = parser.parse_args()

    if args.command == "snapshot":
        cmd_snapshot(args.framework_dir)
    elif args.command == "grade":
        cmd_grade(args.framework_dir, args.timeout, args.memory_gb)


if __name__ == "__main__":
    main()
