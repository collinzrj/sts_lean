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
- Why `RobustInfinite` ≠ `UnboundedDamage`:
  - `RobustInfinite`: `∃strategy ∀N` — the player commits to a **fixed infinite action sequence** without knowing the damage target N. The same strategy must work for all N.
  - `UnboundedDamage`: `∀N ∃trace` — the player can **choose a different trace for each N**. Each target gets a tailored strategy.
  - Concretely, `UnboundedDamage` allows the player to "charge up" (e.g., accumulate energy) then play a card that breaks the loop — as long as it reaches the target N. `RobustInfinite` requires the player to keep going indefinitely after dealing damage.
    - The game-theoretic consequence: against an enemy with unknown HP (where the player only sees "alive/dead" feedback), `UnboundedDamage` does NOT guarantee a win — the player can't know when to stop charging. `RobustInfinite` guarantees a win since damage grows without bound along a single execution path.

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

Simpler combos use direct step-chain proofs (`exL2_cons` + `perm_singleton_eq`/`perm_3_cases`).

Harder combos use the **drawCondBool bridge** pattern. Example below.

### Example: Storm of Steel+ + 2×Prepared+ (5 cards)

**Cards and effects**:
| Card | Cost | Effect |
|------|------|--------|
| Storm of Steel+ | 1E | Discard all hand cards, create one Shiv per card discarded (0-cost attack, 4 damage, exhaust on play) |
| Tactician+ | Unplayable | **On discard**: gain 2 energy |
| Reflex+ | Unplayable | **On discard**: draw 3 cards |
| Prepared+ ×2 | 0E | Draw 2 cards, then discard 2 cards |

**Loop strategy** (single turn, no endTurn):

1. **Play Storm of Steel+** (1E) → discard 4 hand cards, create 4 Shivs. Tactician+ triggers +2E, Reflex+ triggers draw 3
2. **Draw 3 from 5-card shuffle** (Oracle 0 controls order). **Pigeonhole: 2 Preps among 5 cards, drawing 3 guarantees at least 1 Prep.** 2 cards stranded in drawPile
3. **Play 4 Shivs** (0E) → 16 damage, Shivs exhaust
4. **Play a Prepared+** (0E) → draw 2 (retrieves 2 stranded cards), discard 2 (discard Tactician+ and Reflex+). Tactician+ triggers +2E, Reflex+ triggers draw 3
5. **Draw 3 from 3-card shuffle** (Oracle 1). **All 3 drawn, oracle has no control**
6. **Back to anchor state**: hand = {SoS+, Tact+, Reflex+, Prep+, Prep+}

**Why it works for ALL shuffles**:
- **Step 2 (pigeonhole)**: 5 cards with 2 Preps → draw 3 always includes at least 1 Prep
- **Step 4 (Prep recovery)**: drawPile has exactly 2 stranded cards, Prep draws both back
- **Step 5 (full draw)**: pile has exactly 3 = draw count, all recovered, oracle irrelevant
- **`sameModAccum` interchangeability**: both Prep+ have identical (name, cost, damage), sorted comparison matches regardless of which is where

**drawCondBool bridge proof structure** (4 layers):

1. **Computational verification**: `native_decide` checks all 120×6 = 720 permutation combinations
2. **Oracle bridge**: proved by induction on the trace — if the real oracle agrees with the fixed oracle at shuffle points, `executeL2` gives the same result (using `stepL2_oracle_cond`)
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

## Benchmark Distribution

`sts_benchmark.tar.gz` contains the full benchmark without reference solutions. Extract and let the LLM agent read `INSTRUCTIONS.md` to complete the task.

```bash
tar xzf sts_benchmark.tar.gz -C my_workspace/ && cd my_workspace/
```

Prompt:
> Read INSTRUCTIONS.md, then prove all theorems marked `sorry` in `StSVerify/CombosTemplateL1/` and `StSVerify/CombosTemplateL2/`. Verify each proof compiles with `lake build`. If you finish, try the bonus challenges in `StSVerify/ExtendedTargets.lean`.

## Commands

```bash
# Build and verify all proofs (full repo with reference solutions)
cd lean_framework && export PATH="$HOME/.elan/bin:$PATH" && lake build

# Verify a single solution
lake env lean StSVerify/CombosLevel1Solution/ComboDropkickExhaust.lean
lake env lean StSVerify/CombosLevel2Solution/ComboDropkickExhaust.lean

# Generate templates from combo data
python generate_templates.py
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
