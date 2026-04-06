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
  ExtendedTargets.lean       — Extended proof targets (bonus challenges)
  CombosSpecL1/              — Level 1 specs: card lists + enemy state (READ-ONLY)
  CombosSpecL2/              — Level 2 specs: card lists + enemy state (READ-ONLY)
  CombosTemplateL1/          — Level 1 checkers: import spec+solution, type check + axiom audit (READ-ONLY)
  CombosTemplateL2/          — Level 2 checkers: import spec+solution, type check + axiom audit (READ-ONLY)
  CombosLevel1Solution/      — Level 1 solutions — LLM fills these (12/12 verified)
  CombosLevel2Solution/      — Level 2 solutions — LLM fills these (11/12 verified, 1 open)
eval/
  eval.py                    — Grading script: integrity check + build + axiom audit
  prepare.py                 — Preparation script: strip solutions, generate sorry stubs, snapshot checksums
```

### Three-File Architecture

Each combo × level has three files:

1. **Spec file** (`CombosSpec{L1,L2}/`): defines `cards` and `enemy` (read-only)
2. **Solution file** (`CombosLevel{1,2}Solution/`): LLM writes proof, exports `theorem proof`
3. **Checker file** (`CombosTemplate{L1,L2}/`): imports spec + solution, verifies type match, `#print axioms` audits axioms (read-only)

Lean's namespace mechanism prevents the solution file from redefining `cards` and `enemy` from the spec.

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

**Loop strategy** (single turn, no endTurn, two branches):

**Shared opening**:
1. **Play Storm of Steel+** (1E) → discard 4 hand cards, create 4 Shivs. Tactician+ triggers +2E, Reflex+ triggers draw 3
2. **Draw 3 from 5-card shuffle** (Oracle controls order). 2 cards stranded in drawPile

**NS branch** (drew at least 1 Prepared+):
3. **Play 4 Shivs** (0E) → 16 damage
4. **Play Prepared+** (0E) → draw 2 (retrieves stranded cards), discard 2 (Tactician+ and Reflex+). Triggers +2E and draw 3
5. **Draw 3 from 3-card shuffle** → all 3 drawn, oracle has no control
6. **Back to anchor state** ✓

**PS branch** (drew 0 Prepared+, i.e. {SoS+, Tact+, Reflex+}):
3. **Play 4 Shivs** (0E) → 16 damage
4. **Play Storm of Steel+ again** (1E) → discard Tactician+ and Reflex+, create 2 Shivs. Triggers +2E and draw 3
5. **Draw 3** → retrieve 2 Prepared+ from drawPile + 1 from shuffle
6. **Play 2 Shivs** (0E) → 8 damage
7. **Play Prepared+** (0E) → draw 2 (shuffle remainder), discard 2 (Tactician+ and Reflex+). Triggers +2E and draw 3
8. **Draw 3 from 3-card shuffle** → all 3 drawn, oracle has no control
9. **Back to anchor state** ✓

**Why it works for ALL shuffles**:
- **NS/PS covers all cases**: the 3 drawn cards either include a Prep (NS) or don't (PS). Both paths return to anchor state
- **Final step (full draw)**: both paths end by drawing exactly 3 from a 3-card shuffle — oracle has no control
- **`sameModAccum` interchangeability**: both Prep+ have identical (name, cost, damage), sorted comparison matches regardless of which is where

**drawCondBool bridge proof structure** (4 layers):

1. **Computational verification**: `native_decide` checks all 120×6 = 720 permutation combinations
2. **Oracle bridge**: proved by induction on the trace — if the real oracle agrees with the fixed oracle at shuffle points, `executeL2` gives the same result (using `stepL2_oracle_cond`)
3. **Permutation completeness**: mathematical case analysis proves `List.Perm l pile → l ∈ allPerms` (Nodup + element membership)
4. **Main theorem**: introduces oracle, combines bridge with verification. **No `native_decide` in main proof body**

## Benchmark Evaluation

### Preparing the Benchmark

```bash
# Clone the repo
git clone <repo-url> && cd <repo>

# Prepare: strip solutions, generate sorry stubs, snapshot checksums, clean build cache
python eval/prepare.py
```

`prepare.py` will:
1. Replace all solution files with sorry stubs (preserving correct namespace, imports, type signatures)
2. Remove non-benchmark files (`legacy/`, `data/`, `generate_*.py`, READMEs, etc.)
3. Remove `.git/` (use `--keep-git` to preserve)
4. Snapshot SHA256 checksums of all read-only files
5. Clean `.lake/build/` build cache

### Running the Agent

```bash
claude --dangerously-skip-permissions -p "Read INSTRUCTIONS.md, then prove all theorems marked sorry in StSVerify/CombosLevel1Solution/ and StSVerify/CombosLevel2Solution/. Verify each proof compiles with lake build. If you finish, try the bonus challenges in StSVerify/ExtendedTargets.lean."
```

### Grading

**Important:** The agent may have modified files under `eval/` (grading script, checksums). Before grading, restore the `eval/` directory from the original repo commit to ensure the evaluation logic has not been tampered with.

```bash
# Restore eval/ from the original commit (replace <commit-hash> with the commit before prepare.py was run)
git clone <repo-url> /tmp/sts_eval_clean --depth 1 --branch <commit-or-tag>
rm -rf eval/
cp -r /tmp/sts_eval_clean/eval/ eval/

# Grade: integrity check + build each test case + axiom audit
python eval/eval.py grade
```

The grading script will:
1. Verify all read-only file SHA256 checksums match the snapshot (any modification fails all tests)
2. Run `lake build` for each test case
3. Parse `#print axioms` output, rejecting `sorryAx` and custom axioms
4. Output per-combo per-level pass/fail results to `eval/eval_results.json`

## Commands

```bash
# Build and verify all proofs (full repo with reference solutions)
export PATH="$HOME/.elan/bin:$PATH" && lake build

# Verify a single test case
lake build StSVerify.CombosTemplateL1.ComboDropkickExhaust
lake build StSVerify.CombosTemplateL2.ComboDropkickExhaust
```

## Open Questions

The formalization surfaced several open questions (extended definitions in `ExtendedTargets.lean`):

1. **Can [Storm of Steel+, Tactician+, Reflex+, Prepared+×3] deal unbounded damage?**
   With 6 cards, the adversary can strand Reflex at the bottom of the draw pile, breaking the "draw 3" trigger and preventing a period-1 loop. But the player may be able to adapt — keeping Reflex in hand and using the 3 Prepared+ copies to cycle the deck. No reference solution.

2. **Does oracle foreknowledge strictly help the player?**
   Our `UnboundedDamage` lets the player see all future shuffle results before choosing actions (offline optimization). `OnlineUnboundedDamage` restricts the player to decisions based only on past shuffle results (online strategy, matching the real game). Is there a combo where the former holds but the latter doesn't?

3. **Period-1 loop → fixed strategy (`GuaranteedInfiniteCombo → RobustInfinite`)**
   If a combo can loop once back to the same state under any shuffle, can it be repeated N times to form a fixed infinite action sequence? Intuitively obvious, but the formal proof requires a simulation theorem showing sameModAccum-equivalent states produce identical engine behavior. Currently sorry.

## Soundness

The eval harness checks LLM submissions via a three-file architecture:

1. **Integrity check**: SHA256 checksums of all read-only files must match the pre-agent snapshot
2. **Type safety**: The checker file forces the solution's `proof` theorem to match the spec's `cards` and `enemy` — Lean's type system prevents mismatches
3. **Axiom audit**: `#print axioms` must show only `{propext, Lean.ofReduceBool, Quot.sound, Classical.choice}` — no `sorryAx` or custom axioms
4. **Namespace protection**: Lean prevents duplicate declarations, so the solution cannot redefine spec-provided `cards` or `enemy`

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
