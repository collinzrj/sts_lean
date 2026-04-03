# Slay the Spire Infinite Combo Verification Benchmark

## Task

You are given a Lean 4 formalization of a Slay the Spire game engine and 12 card combos. Your task is to formally prove that each combo loops infinitely, dealing damage each iteration.

## Proof Levels

### Level 1 — Existence (`InfiniteCombo`)

Prove that there EXISTS some shuffle order where the combo loops.

- Fill in `sorry` in each file under `StSVerify/CombosTemplateL1/`
- You provide: `setupTrace`, `loopTrace`, `stateA`, `stateB`
- Lean verifies via `native_decide`: setup reaches stateA, loop reaches stateB, states match (`sameModAccum`), damage increases
- This is straightforward — just find a working trace

### Level 2 — Guaranteed Loop (`GuaranteedInfiniteCombo`)

Prove the combo loops despite ANY adversarial shuffle order.

- Fill in `sorry` in each file under `StSVerify/CombosTemplateL2/`
- Setup uses lucky draws (Level 1 style). The loop must handle ALL shuffles via `ShuffleOracle`
- You must prove: `∀ oracle, validOracle oracle → ∃ loopTrace stateB, ...`
- `native_decide` is allowed ONLY for engine computation helpers (single steps, state comparisons)
- `native_decide` is NOT allowed in the main proof body — oracle quantification must use real proof tactics

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

# Build a single file
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

Each template file contains the card list, card reference, and available actions.

## Bonus Challenges

If you complete the main tasks, try these harder problems defined in `StSVerify/ExtendedTargets.lean`:

1. **Prove `GuaranteedInfiniteCombo → RobustInfinite`**: If a combo can loop once back to the same state under any shuffle, show it can be repeated to form a fixed strategy that beats any damage target. (Currently sorry.)

2. **Prove or disprove: `OnlineUnboundedDamage` is strictly stronger than `UnboundedDamage`**: Find a combo (or construct a theoretical example) where the player needs oracle foreknowledge to deal unbounded damage — i.e., no adaptive strategy (blind to future shuffles) suffices, but a trace chosen after seeing the oracle does.
