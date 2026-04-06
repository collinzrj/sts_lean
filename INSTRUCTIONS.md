# Slay the Spire Infinite Combo Verification Benchmark

## Task

You are given a Lean 4 formalization of a Slay the Spire game engine and 12 card combos. Your task is to formally prove that each combo loops infinitely, dealing damage each iteration.

There are 24 test cases total: 12 combos × 2 levels. Each test case has a dedicated solution file that you must fill in.

## File Structure

```
StSVerify/
  Engine.lean                — Game engine (READ-ONLY)
  EngineHelperLemmas.lean    — Oracle bridge lemmas (READ-ONLY)
  CardId.lean                — Card name enum (READ-ONLY)
  Cards/                     — Card definitions (READ-ONLY)
  CardDB.lean                — Card lookup table (READ-ONLY)
  Demo.lean                  — Level 1 proof example (READ-ONLY)
  ExtendedTargets.lean       — Bonus challenges (READ-ONLY)
  CombosSpecL1/              — Level 1 specs: card lists + enemy (READ-ONLY)
  CombosSpecL2/              — Level 2 specs: card lists + enemy (READ-ONLY)
  CombosTemplateL1/          — Level 1 checkers (READ-ONLY)
  CombosTemplateL2/          — Level 2 checkers (READ-ONLY)
  CombosLevel1Solution/      — Level 1 solutions — EDIT THESE
  CombosLevel2Solution/      — Level 2 solutions — EDIT THESE
eval/
  eval.py                    — Grading script (READ-ONLY)
  prepare.py                 — Benchmark preparation (READ-ONLY)
```

**You may ONLY edit files under `CombosLevel1Solution/` and `CombosLevel2Solution/`.**
All other files are read-only and integrity-checked. Modifying them will fail the entire evaluation.

## Proof Levels

### Level 1 — Existence (`InfiniteCombo`)

Prove that there EXISTS some shuffle order where the combo loops.

- Edit the corresponding file under `StSVerify/CombosLevel1Solution/`
- You provide: `setupTrace`, `loopTrace`, `stateA`, `stateB`
- Lean verifies via `native_decide`: setup reaches stateA, loop reaches stateB, states match (`sameModAccum`), damage increases
- Your file must export `theorem proof : InfiniteCombo cardDB cards enemy`
- This is straightforward — just find a working trace

### Level 2 — Guaranteed Loop (`GuaranteedInfiniteCombo`)

Prove the combo loops despite ANY adversarial shuffle order.

- Edit the corresponding file under `StSVerify/CombosLevel2Solution/`
- Setup uses lucky draws (Level 1 style). The loop must handle ALL shuffles via `ShuffleOracle`
- You must prove: `∀ oracle, validOracle oracle → ∃ loopTrace stateB, ...`
- Your file must export `theorem proof : GuaranteedInfiniteCombo cardDB cards enemy`
- `native_decide` is allowed ONLY for engine computation helpers (single steps, state comparisons)
- `native_decide` is NOT allowed in the main proof body — oracle quantification must use real proof tactics

## How Grading Works

Each solution file is checked by a corresponding checker (template) file that:
1. Imports your solution file
2. Type-checks that your `proof` theorem matches the spec's `cards` and `enemy`
3. Audits axioms via `#print axioms` — only `propext`, `Lean.ofReduceBool`, `Quot.sound`, `Classical.choice` are allowed

A test case PASSES if and only if:
- The build succeeds (no type errors)
- No `sorryAx` or custom axioms appear in `#print axioms`
- No read-only files were modified

## Available Helper Lemmas

`StSVerify/EngineHelperLemmas.lean` provides oracle bridge lemmas:
- `drawCardL2_oracle_agree`: oracle agreement on discardPile → drawCardL2 agrees
- `drawCardL2_nonempty_irrel`: drawPile non-empty → oracle irrelevant
- `stepL2_oracle_cond`: drawPile non-empty OR oracle agrees → stepL2 agrees
- `executeL2_oraclesCond`: general oracle simulation

## Key Definitions

```
ShuffleOracle = Nat → List CardInstance → List CardInstance
validOracle oracle = ∀ n pile, (oracle n pile).Perm pile
executeL2: oracle-controlled execution (shuffles use oracle)
sameModAccum: state equivalence modulo accumulating fields (damage, block, exhaustPile)
              cards compared by (name, cost, damage) keys, sorted — so identical cards are interchangeable
              energy must not decrease (b.energy ≥ a.energy)
dealtDamage: after.damage > before.damage
```

## Working Example

`StSVerify/Demo.lean` contains a complete Level 1 proof for reference.

## Commands

```bash
# Build everything
export PATH="$HOME/.elan/bin:$PATH" && lake build

# Build a single test case
lake build StSVerify.CombosTemplateL1.ComboDropkickExhaust
lake build StSVerify.CombosTemplateL2.ComboDropkickExhaust
```

## Combos (12)

| Combo | Cards | Character | File |
|-------|-------|-----------|------|
| DropkickExhaust | 11 | Ironclad | ComboDropkickExhaust.lean |
| CorruptionDropkick | 13 | Ironclad | ComboCorruptionDropkick.lean |
| HeelHookExhaust | 10 | Silent | ComboHeelHookExhaust.lean |
| StreamlineHologram | 11 | Defect | ComboStreamlineHologram.lean |
| AcrobaticsTactician | 12 | Silent | ComboAcrobaticsTactician.lean |
| MantraDivine | 13 | Watcher | ComboMantraDivine.lean |
| StandardWatcher | 12 | Watcher | ComboStandardWatcher.lean |
| StormOfSteel | 4 | Silent | ComboStormOfSteel.lean |
| StormOfSteel2Prep | 5 | Silent | ComboStormOfSteel2Prep.lean |
| StormOfSteel3Prep | 6 | Silent | ComboStormOfSteel3Prep.lean |
| StormStrike | 5 | Silent | ComboStormStrike.lean |
| TantrumFearNoEvil | 11 | Watcher | ComboTantrumFearNoEvil.lean |

Each spec file (in `CombosSpecL1/` or `CombosSpecL2/`) contains the card list, card reference, and enemy state.

## Bonus Challenges

If you complete the main tasks, try these harder problems in `StSVerify/ExtendedTargets.lean`:

1. **`guaranteed_implies_robust`**: Prove that `GuaranteedInfiniteCombo → RobustInfinite`. If a combo can loop once back to the same state under any shuffle, show it can be repeated to form a fixed strategy that beats any damage target.

2. **`online_implies_unbounded`**: Prove that `OnlineUnboundedDamage → UnboundedDamage`. An adaptive strategy tree that works against all oracles can be instantiated with a specific oracle to produce a concrete trace.

3. **`OfflineOnlineGapStrict`**: Prove or disprove that oracle foreknowledge strictly helps. The proposition states `∃ cardDB cards enemy, UnboundedDamage cardDB cards enemy ∧ ¬ OnlineUnboundedDamage cardDB cards enemy`. Either construct a witness or prove its negation.
