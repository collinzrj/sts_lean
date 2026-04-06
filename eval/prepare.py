#!/usr/bin/env python3
"""
Prepare the benchmark for an agent run.

After cloning the repo, run this script to:
  1. Replace all solution files with sorry stubs
  2. Remove non-benchmark files (legacy/, data/, generate_*.py, READMEs, tar.gz, etc.)
  3. Remove .git/
  4. Snapshot read-only file checksums for integrity checking

Usage:
  python eval/prepare.py [--keep-git] [--keep-solutions]
"""

import argparse
import shutil
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

# Files/dirs to remove (relative to framework_dir)
REMOVE_PATHS = [
    "legacy",
    "data",
    "generate_cards.py",
    "generate_templates.py",
    "README.md",
    "README_en.md",
    "sts_benchmark.tar.gz",
]


def make_stub_l1(combo: str) -> str:
    namespace = f"{combo}_L1"
    return f"""/-
  {combo} — Level 1 Solution
  Prove: InfiniteCombo cardDB cards enemy

  Write your proof here. You may add any helper definitions/lemmas you need.
  The checker will verify that `proof` has type `InfiniteCombo cardDB cards enemy`
  and does not use sorry or custom axioms.
-/
import StSVerify.CombosSpecL1.{combo}

open CardName Action

namespace {namespace}

-- Your proof goes here.
-- You must provide a theorem named `proof` with this exact type:
theorem proof : InfiniteCombo cardDB cards enemy := by
  sorry

end {namespace}
"""


def make_stub_l2(combo: str) -> str:
    namespace = f"{combo}_L2"
    return f"""/-
  {combo} — Level 2 Solution
  Prove: GuaranteedInfiniteCombo cardDB cards enemy

  Write your proof here. You may add any helper definitions/lemmas you need.
  The checker will verify that `proof` has type `GuaranteedInfiniteCombo cardDB cards enemy`
  and does not use sorry or custom axioms.
-/
import StSVerify.CombosSpecL2.{combo}
import StSVerify.EngineHelperLemmas

open CardName Action

namespace {namespace}

-- Your proof goes here.
-- You must provide a theorem named `proof` with this exact type:
theorem proof : GuaranteedInfiniteCombo cardDB cards enemy := by
  sorry

end {namespace}
"""


def prepare(framework_dir: Path, keep_git: bool, keep_solutions: bool):
    print(f"Preparing benchmark in: {framework_dir}")

    # Step 1: Replace solution files with stubs
    if not keep_solutions:
        print("\n[1/4] Replacing solution files with sorry stubs...")
        for combo in COMBOS:
            # L1
            l1_path = framework_dir / "StSVerify" / "CombosLevel1Solution" / f"{combo}.lean"
            l1_path.write_text(make_stub_l1(combo))
            print(f"  Stubbed: StSVerify/CombosLevel1Solution/{combo}.lean")

            # L2
            l2_path = framework_dir / "StSVerify" / "CombosLevel2Solution" / f"{combo}.lean"
            l2_path.write_text(make_stub_l2(combo))
            print(f"  Stubbed: StSVerify/CombosLevel2Solution/{combo}.lean")
        print(f"  {len(COMBOS) * 2} solution files replaced with stubs.")
    else:
        print("\n[1/4] Skipping solution replacement (--keep-solutions).")

    # Step 2: Remove non-benchmark files
    print("\n[2/4] Removing non-benchmark files...")
    for rel in REMOVE_PATHS:
        p = framework_dir / rel
        if p.is_dir():
            shutil.rmtree(p)
            print(f"  Removed directory: {rel}/")
        elif p.is_file():
            p.unlink()
            print(f"  Removed file: {rel}")

    # Step 3: Remove .git
    if not keep_git:
        git_dir = framework_dir / ".git"
        if git_dir.exists():
            print("\n[3/4] Removing .git/...")
            shutil.rmtree(git_dir)
            print("  Removed .git/")
        else:
            print("\n[3/4] No .git/ found, skipping.")
    else:
        print("\n[3/4] Skipping .git removal (--keep-git).")

    # Step 4: Snapshot checksums
    print("\n[4/4] Generating read-only file checksums...")
    # Import eval.py's snapshot logic
    import importlib.util
    eval_path = framework_dir / "eval" / "eval.py"
    spec = importlib.util.spec_from_file_location("eval_module", eval_path)
    eval_mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(eval_mod)
    eval_mod.cmd_snapshot(framework_dir)

    # Step 5: Clean lake build cache so agent starts fresh
    print("\n[5/5] Cleaning build cache...")
    lake_build = framework_dir / ".lake" / "build"
    if lake_build.exists():
        shutil.rmtree(lake_build)
        print("  Removed .lake/build/")
    else:
        print("  No build cache found.")

    print("\n" + "=" * 50)
    print("Benchmark prepared successfully!")
    print("=" * 50)
    print(f"\nAgent should edit files in:")
    print(f"  StSVerify/CombosLevel1Solution/*.lean  (12 L1 proofs)")
    print(f"  StSVerify/CombosLevel2Solution/*.lean  (12 L2 proofs)")
    print(f"\nAfter agent finishes, grade with:")
    print(f"  python eval/eval.py grade")


def main():
    parser = argparse.ArgumentParser(description="Prepare StS benchmark for agent run")
    framework_default = Path(__file__).resolve().parent.parent
    parser.add_argument("framework_dir", nargs="?", type=Path, default=framework_default)
    parser.add_argument("--keep-git", action="store_true", help="Don't remove .git/")
    parser.add_argument("--keep-solutions", action="store_true", help="Don't replace solution files")
    args = parser.parse_args()
    prepare(args.framework_dir, args.keep_git, args.keep_solutions)


if __name__ == "__main__":
    main()
