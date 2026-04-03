[中文版](README.md)

# StS Infinite Combo Lean 4 Verification Benchmark

Evaluates whether LLMs can formally prove that Slay the Spire card combos loop infinitely.

## Proof Levels

**Level 1 — Existence:** The player is "lucky" — there exists some shuffle order where the combo loops.
- LLM provides: `setupTrace`, `loopTrace`, `stateA`, `stateB`
- Lean verifies via `native_decide`: setup reaches stateA, loop reaches stateB, states match, damage increased
- Proposition: `InfiniteCombo`

**Level 2 — Guaranteed against adversarial shuffles.** Only the setup is lucky. The loop must work despite ANY shuffle order, controlled by a `ShuffleOracle`.
- `native_decide` allowed only for engine computation helpers (individual steps, state comparisons)
- `native_decide` NOT allowed in main proof body — oracle quantification must use real tactics
- Three proof targets of decreasing strength:

| Strength | Proposition | Quantifier structure | Meaning |
|----------|-------------|---------------------|---------|
| Strongest | `GuaranteedInfiniteCombo` | `∀oracle ∃trace, sameModAccum` | Period-1 loop: exact state recurrence |
| Medium | `RobustInfinite` | `∀oracle ∃strategy ∀N ∃K, damage > N` | Fixed strategy beats any HP |
| Weakest | `UnboundedDamage` | `∀oracle ∀N ∃trace, damage > N` | Each HP target gets own trace |

- `RobustInfinite → UnboundedDamage` is proved. `GuaranteedInfiniteCombo → RobustInfinite` is stated (sorry).

## Structure

```
StSVerify/
  Engine.lean                — Game engine: state, effects, actions, execute, executeL2
  EngineHelperLemmas.lean    — Oracle bridge lemmas (stepL2_oracle_cond, etc.)
  CardId.lean                — Global enum of 93 card names
  Cards/                     — One file per card definition (93 files)
  CardDB.lean                — CardName → CardDef lookup
  Demo.lean                  — Working Level 1 proof (Silent 5-card combo)
  CombosTemplateL1/          — Level 1 templates with sorry (12 combos)
  CombosTemplateL2/          — Level 2 templates with sorry (12 combos)
  CombosLevel1Solution/      — Level 1 reference solutions (12/12 verified)
  CombosLevel2Solution/      — Level 2 reference solutions (11/12 verified, 1 open)
data/
  combos_v2.jsonl            — Combo definitions (cards, enemy state, effects)
eval/
  eval_lean.py               — LLM evaluation harness
  prompt_template.txt        — Prompt template
generate_cards.py            — Generates Cards/*.lean and CardDB.lean
generate_templates.py        — Generates template files from combos_v2.jsonl
```

## Combos (12)

| Combo | Cards | Character | Shuffle Complexity | L1 | L2 |
|-------|-------|-----------|-------------------|----|----|
| DropkickExhaust | 11 | Ironclad | Singleton (deterministic) | ✅ | ✅ |
| CorruptionDropkick | 13 | Ironclad | Singleton (deterministic) | ✅ | ✅ |
| HeelHookExhaust | 10 | Silent | Singleton (deterministic) | ✅ | ✅ |
| StreamlineHologram | 11 | Defect | No shuffle in loop | ✅ | ✅ |
| AcrobaticsTactician | 12 | Silent | 4 shuffle points | ✅ | ✅ |
| MantraDivine | 13 | Watcher | 6 permutations | ✅ | ✅ |
| StandardWatcher | 12 | Watcher | 4 cases (2x2) | ✅ | ✅ |
| StormOfSteel | 4 | Silent | 12 cases (2x6) | ✅ | ✅ |
| StormOfSteel2Prep | 5 | Silent | 48 cases (24x2) | ✅ | ✅ |
| StormOfSteel3Prep | 6 | Silent | 720+ cases, cascading shuffles | ✅ | ⬚ |
| StormStrike | 5 | Silent | Adversary strands Prep | ✅ | ✅ |
| TantrumFearNoEvil | 11 | Watcher | 48 cases (24x2) | ✅ | ✅ |

- **L1**: 12/12 proved (single-turn loops, no endTurn)
- **L2**: 11/12 `GuaranteedInfiniteCombo` proved
   - StormOfSteel3Prep: NOT `GuaranteedInfiniteCombo` (6-card deck, adversary can strand Reflex breaking the period-1 loop). Conjectured `UnboundedDamage` (player can adaptively deal damage using Preps to recover). **OPEN — hardest benchmark challenge, no reference solution** — ⬚

## L2 Proof Techniques

The harder combos (StormStrike, TantrumFearNoEvil, StormOfSteel 2/3Prep) use the **drawCondBool bridge** pattern:

1. Define `drawCondBool fo p1 p2 si s trace : Bool` — steps through execution using a fixed oracle, checking at each draw step that either drawPile is non-empty or we're at a known shuffle point
2. Verify `drawCondBool` passes for all permutation pairs with a single `native_decide` (concrete engine computation)
3. Prove `drawCondBool_bridge`: if the check passes and the real oracle agrees at shuffle points, `executeL2` gives the same result (proved by induction with `stepL2_oracle_cond`)
4. Main theorem combines the bridge with permutation completeness

Simpler combos use direct step-chain proofs (`exL2_cons` + `perm_singleton_eq`/`perm_3_cases`).

### Hardest Challenge: Storm of Steel + 3 Prepared+ (6 cards)

**Combo**: Storm of Steel+ + Tactician+ + Reflex+ + 3x Prepared+ (6 cards)

**Why it's hard**: Unlike all other combos, the 6-card deck creates cascading oracle interactions that prevent a simple period-1 loop:
- After one loop: Reflex's draw 3 draws 2 of 3 from a sub-shuffle, stranding 1 card in drawPile
- State goes from (hand=6, draw=0) to (hand=5, draw=1) — `sameModAccum` fails
- The adversary can choose to strand Reflex itself, killing the draw-3 trigger in the next iteration
- When Reflex is stranded with empty discardPile, Prepared+ can't draw it back (draw fails)

**Proof target**: `UnboundedDamage` (not `GuaranteedInfiniteCombo`)

**Conjectured strategy**: The player can adaptively deal unbounded damage by:
1. Keeping Reflex in hand (don't discard via Prep) when the oracle is adversarial
2. Playing SoS with Reflex in hand → stormOfSteel discards Reflex → draw 3 trigger
3. Using the 3 Preps to cycle cards and recover SoS for the next damage cycle
4. Each SoS play creates at least 1 Shiv = 4 damage minimum

**Status**: OPEN — no reference solution. This requires proving a complex multi-iteration adaptive strategy, beyond what single-loop `native_decide` can verify.

### Example (proved): Storm of Steel + 2 Prepared+ (5 cards)

The 2-Prep variant IS `GuaranteedInfiniteCombo`. With 5 cards and 2 shuffle points (Oracle 0: 120 perms, Oracle 1: 6 perms = 720 total), the drawCondBool bridge pattern proves the loop for all cases:

1. **Computational verification** (`verifyAll_ok`): `native_decide` checks all 720 permutation pairs
2. **Oracle bridge** (`drawCondBool_bridge`): proved by induction on the trace using `stepL2_oracle_cond`
3. **Permutation completeness**: mathematical case analysis proves `List.Perm l pile → l ∈ allPerms` (Nodup + element membership)
4. **Main theorem**: introduces oracle, combines bridge with verification. **No `native_decide` in main proof body**

## Open Questions

The formalization surfaced several open questions (extended definitions in `ExtendedTargets.lean`):

1. **Can [Storm of Steel+, Tactician+, Reflex+, Prepared+×3] deal unbounded damage?**
   With 6 cards, the adversary can strand Reflex at the bottom of the draw pile, breaking the "draw 3" trigger and preventing a period-1 loop. But the player may be able to adapt — keeping Reflex in hand and using the 3 Prepared+ copies to cycle the deck. No reference solution.

2. **Does oracle foreknowledge strictly help the player?**
   Our `UnboundedDamage` lets the player see all future shuffle results before choosing actions (offline optimization). `OnlineUnboundedDamage` restricts the player to decisions based only on past shuffle results (online strategy, matching the real game). Is there a combo where the former holds but the latter doesn't?

3. **Period-1 loop → fixed strategy (`GuaranteedInfiniteCombo → RobustInfinite`)**
   If a combo can loop once back to the same state under any shuffle, can it be repeated N times to form a fixed infinite action sequence? Intuitively obvious, but the formal proof requires a simulation theorem showing sameModAccum-equivalent states produce identical engine behavior. Currently sorry.

## Soundness

The eval harness checks LLM submissions for:
- `sorry` — incomplete proof
- `axiom` — false assumptions
- `unsafe` — bypass kernel
- `instance` — unsound decidability instances
- Framework function redefinitions
- Unauthorized imports
- L2: `native_decide` not in main proof body (only engine helpers)

## Commands

```bash
# Build and verify all proofs
cd lean_framework && export PATH="$HOME/.elan/bin:$PATH" && lake build

# Verify a single solution
lake env lean StSVerify/CombosLevel1Solution/ComboDropkickExhaust.lean
lake env lean StSVerify/CombosLevel2Solution/ComboDropkickExhaust.lean

# Generate templates from combo data
python generate_templates.py

# Run LLM eval
python eval/eval_lean.py --model openai/gpt-5.4 --thinking --parallel 8
```

## Known Limitations

### Not Implemented
- **Relics** — Sundial, Unceasing Top, etc. 10 relic combos excluded from dataset.
- **Retain** — Cards staying in hand across turns (Miracle, Insight, Meditate+).
- **Burst/Double Tap** — "Next N skills/attacks play twice."
- **X-cost cards** — Variable cost not modeled.
- **HP tracking** — Engine doesn't track HP or death.
- **Enemy actions** — `endTurn` doesn't model enemy attacking or debuff decay.
- **Vulnerability/Weak decay** — Debuffs stay constant (real game: decrease by 1 each turn).
- **Strength** — Not tracked.

### Simplifications
- **Enemy state is static** — Vulnerable/weak set as initial parameters, never decay.
- **Block resets on endTurn** — Barricade (block persists) not modeled.
- **Orb passives** — Orbs channeled/evoked but per-turn effects not triggered.
- **Damage rounding** — Vulnerable 1.5× uses integer division (matches game).
