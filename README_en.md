[中文版](README.md)

# StS Infinite Combo Lean 4 Verification Benchmark

Evaluates whether LLMs can formally prove that Slay the Spire card combos loop infinitely.

## Proof Levels

**Level 1 — Existence:** The player is "lucky" — there exists some shuffle order where the combo loops.
- LLM provides: `setupTrace`, `loopTrace`, `stateA`, `stateB`
- Lean verifies via `native_decide`: setup reaches stateA, loop reaches stateB, states match, damage increased
- Proposition: `InfiniteCombo`

**Level 2 — Guaranteed Loop:** Only the setup is lucky. The loop works despite ANY adversarial shuffle order.
- Setup uses Level 1 (lucky draws). Loop must handle all shuffles via `ShuffleOracle`.
- LLM must prove `∀ oracle, validOracle oracle → ∃ loopTrace stateB, ...`
- `native_decide` allowed only for engine computation helpers (individual steps, state comparisons)
- `native_decide` NOT allowed in main proof body — oracle quantification must use real tactics
- Proposition: `GuaranteedInfiniteCombo`

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
  CombosLevel2Solution/      — Level 2 reference solutions (12/12 verified)
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
| StormOfSteel3Prep | 6 | Silent | 720 cases (120x6) | ✅ | ✅ |
| StormStrike | 5 | Silent | Adversary strands Prep | ✅ | ❌ |
| TantrumFearNoEvil | 11 | Watcher | 48 cases (24x2) | ✅ | ✅ |

- **L1**: 12/12 proved (single-turn loops, no endTurn)
- **L2**: 11/12 proved infinite, 1 (StormStrike) not L2-infinite (adversary hides the only Prep), negation proof in progress (sorry)

## L2 Proof Techniques

The harder combos (StormStrike, TantrumFearNoEvil, StormOfSteel 2/3Prep) use the **drawCondBool bridge** pattern:

1. Define `drawCondBool fo p1 p2 si s trace : Bool` — steps through execution using a fixed oracle, checking at each draw step that either drawPile is non-empty or we're at a known shuffle point
2. Verify `drawCondBool` passes for all permutation pairs with a single `native_decide` (concrete engine computation)
3. Prove `drawCondBool_bridge`: if the check passes and the real oracle agrees at shuffle points, `executeL2` gives the same result (proved by induction with `stepL2_oracle_cond`)
4. Main theorem combines the bridge with permutation completeness

Simpler combos use direct step-chain proofs (`exL2_cons` + `perm_singleton_eq`/`perm_3_cases`).

### Example: Storm of Steel + 3 Prepared+ (6 cards)

**Combo**: Storm of Steel+ + Tactician+ + Reflex+ + 3x Prepared+ (6 cards)

**Challenge**: 6 cards, 2 shuffle points. Oracle 0 shuffles 5 cards (120 perms), Oracle 1 shuffles 3 cards (6 perms), totaling 720 combinations.

**Anchor state**: hand = {SoS, Tact, Reflex, Prep2, Prep3} (5 cards), discardPile = {Prep1}, energy = 6

**Loop strategy** (single turn, no endTurn):

1. **Play Storm of Steel+** (1E) → discard 4 cards (Tact, Reflex, Prep2, Prep3), create 4 Shivs. Tact triggers +2E, Reflex triggers draw 3.
2. **Draw 3 from 5-card shuffle** (Oracle 0) — pile = {Tact, Reflex, Prep1, Prep2, Prep3}. **Pigeonhole: 3 Preps among 5 cards, drawing 3 guarantees at least 1 Prep.** 2 cards stranded in drawPile.
3. **Play 4 Shivs** (0E) → 16 damage, Shivs exhaust.
4. **Play a Prepared+** (0E) → draw 2 (retrieves the 2 stranded cards from drawPile), discard 2 (discard Tact + Reflex). Tact triggers +2E, Reflex triggers draw 3.
5. **Draw 3 from 3-card shuffle** (Oracle 1) — pile = {Reflex, Tact, SoS}. **All 3 drawn, oracle has no control.**
6. **Back to anchor state**: hand = {SoS, Tact, Reflex, Prep, Prep}, disc = {Prep}

**Why it works for ALL shuffles (mathematical argument)**:
- **Step 2 (pigeonhole)**: 5 cards with 3 Preps → draw 3 always includes at least 1 Prep, guaranteeing step 4 has a Prep to play.
- **Step 4 (Prep recovery)**: drawPile has exactly 2 stranded cards. Prep draws both back. Tact and Reflex are always in hand (they're not Preps, so the played Prep didn't remove them).
- **Step 5 (full draw)**: pile has exactly 3 cards = draw count. All recovered, oracle irrelevant.
- **`sameModAccum` interchangeability**: all Prep+ instances have identical (name, cost, damage). Regardless of which Prep is in which pile, sorted comparison matches.

**Proof structure** (4 layers):

```
                    ┌─────────────────────────────────┐
                    │   Main theorem (no native_decide)│
                    │   ∀ oracle → ∃ trace, loop ok    │
                    └──────────┬──────────────────────┘
                               │ uses
                    ┌──────────▼──────────────────────┐
                    │   case_handler                   │
                    │   combines bridge + verification  │
                    └──────┬────────────┬─────────────┘
                           │            │
              ┌────────────▼──┐   ┌─────▼──────────────────┐
              │ drawCondBool  │   │ verifyAll = true        │
              │ _bridge       │   │ (native_decide:         │
              │ (by induction)│   │  720 perms all pass)    │
              └───────────────┘   └────────────────────────┘
```

1. **Computational verification** (`verifyAll_ok`): `native_decide` checks all 720 permutation pairs
2. **Oracle bridge** (`drawCondBool_bridge`): proved by induction on the trace using `stepL2_oracle_cond`
3. **Permutation completeness**: mathematical case analysis proves `List.Perm l pile → l ∈ allPerms` (Nodup + element membership)
4. **Main theorem** (`loop_l2`): introduces oracle, uses `permsOf_complete` to find oracle outputs in enumeration, applies `case_handler`. **No `native_decide`**

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
