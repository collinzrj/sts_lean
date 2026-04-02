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

| Combo | Cards | Character | Shuffle Complexity |
|-------|-------|-----------|-------------------|
| DropkickExhaust | 11 | Ironclad | Singleton (deterministic) |
| CorruptionDropkick | 13 | Ironclad | Singleton (deterministic) |
| HeelHookExhaust | 10 | Silent | Singleton (deterministic) |
| StreamlineHologram | 11 | Defect | No shuffle in loop |
| AcrobaticsTactician | 12 | Silent | 4 shuffle points |
| MantraDivine | 13 | Watcher | 6 permutations |
| StandardWatcher | 12 | Watcher | 4 cases (2×2) |
| StormOfSteel | 4 | Silent | 6 permutations |
| StormOfSteel2Prep | 5 | Silent | 3 shuffle points |
| StormOfSteel3Prep | 6 | Silent | 3 shuffle points |
| StormStrike | 5 | Silent | 576 cases (24×24) |
| TantrumFearNoEvil | 11 | Watcher | 48 cases (24×2) |

## L2 Proof Techniques

The harder combos (StormStrike, TantrumFearNoEvil, StormOfSteel 2/3Prep) use the **drawCondBool bridge** pattern:

1. Define `drawCondBool fo p1 p2 si s trace : Bool` — steps through execution using a fixed oracle, checking at each draw step that either drawPile is non-empty or we're at a known shuffle point
2. Verify `drawCondBool` passes for all permutation pairs with a single `native_decide` (concrete engine computation)
3. Prove `drawCondBool_bridge`: if the check passes and the real oracle agrees at shuffle points, `executeL2` gives the same result (proved by induction with `stepL2_oracle_cond`)
4. Main theorem combines the bridge with permutation completeness

Simpler combos use direct step-chain proofs (`exL2_cons` + `perm_singleton_eq`/`perm_3_cases`).

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
