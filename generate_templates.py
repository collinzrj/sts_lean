#!/usr/bin/env python3
"""Generate L1 and L2 Lean template files from combos_v2.jsonl."""

import json
import os

def load_combos(path="data/combos_v2.jsonl"):
    combos = []
    with open(path) as f:
        for line in f:
            combos.append(json.loads(line))
    return combos

def card_ref_comment(cards):
    """Generate card reference comment block."""
    lines = []
    for c in cards:
        copy_str = f" #{c['copy']}" if c.get('copy') else ""
        lines.append(f"    id={c['id']:2d}  {c['cn_name']}{copy_str} ({c['lean_name']}, {c['cost']}E, {c['type']}): {c['effect']}")
    return "\n".join(lines)

def cards_lean_def(cards_lean, def_name="allCards"):
    """Generate the allCards Lean definition."""
    pairs = ", ".join(f"({c['name']}, {c['count']})" for c in cards_lean)
    return f"def {def_name} : List (CardName \u00d7 Nat) :=\n  [{pairs}]"

def enemy_lean_def(enemy):
    vuln = enemy["vulnerable"]
    weak = enemy["weak"]
    intend = "true" if enemy["intending"] else "false"
    return f"def enemy : EnemyState := {{ vulnerable := {vuln}, weak := {weak}, intending := {intend} }}"

def actions_comment():
    return """  Available actions:
    .play <id>              -- play a card from hand (by card instance ID)
    .draw <id>              -- draw a specific card (must be on top of draw pile)
    .failDraw               -- signal that draw pile is empty and cannot draw
    .discard <id>           -- discard a card from hand (for effects that require discarding)
    .exhaust <id>           -- exhaust a card from hand (for effects that require exhausting)
    .endTurn                -- end turn: discard hand, reset energy to 3, draw 5
    .changeStance <stance>  -- change stance: .Calm, .Wrath, .Neutral
    .resolveRushdown        -- resolve Rushdown trigger (draw 2 on entering Wrath)
    .resolveDrawTrigger <id> -- resolve on-draw trigger (Deus Ex Machina, Void)
    .autoPlayFlurry <id>    -- auto-play Flurry of Blows from discard
    .hologramChoose <id>    -- retrieve card from discard (Hologram effect)
    .allForOneChoose [ids]  -- retrieve 0-cost cards from discard (All for One)
    .recycleChoose <id>     -- exhaust card for energy (Recycle effect)"""

def generate_l1_template(combo, out_dir="StSVerify/CombosTemplateL1"):
    """Generate L1 template: LLM provides traces + states, native_decide verifies."""
    c = combo
    ns = f"Combo{c['id']}"

    content = f"""/-
  {c['cn_name']} (Level 1: Existence of infinite loop)
  Cards: {c['total_cards']}

  Prove there EXISTS a sequence of actions that loops,
  dealing damage each iteration. Lucky draws are OK.
-/
import StSVerify.Basic
import StSVerify.CardDB

open CardName Action

namespace {ns}

-- ============================================================
-- FRAMEWORK-PROVIDED (do not modify)
-- ============================================================

{cards_lean_def(c['cards_lean'])}

{enemy_lean_def(c['enemy'])}

/-
  Card reference (id, name, cost, type, effect):
{card_ref_comment(c['cards'])}

  Initial state: all {c['total_cards']} cards in draw pile, 5 draws queued, 3 energy.
  Your first actions must be .draw to pick your opening hand.

{actions_comment()}

  Proof structure:
    1. setupTrace: actions from initial state to reach stateA (the loop start)
    2. loopTrace: actions from stateA to reach stateB (one loop iteration)
    3. stateA, stateB: the game states before/after one loop
    4. Theorems verified by native_decide:
       - setup_ok: executing setupTrace from initial state gives stateA
       - loop_ok: executing loopTrace from stateA gives stateB
       - same_mod: stateA and stateB have the same cards (modulo damage/energy)
       - dealt_dmg: stateB has more damage than stateA
-/

-- ============================================================
-- LLM FILLS IN BELOW
-- ============================================================

def setupTrace : List Action := sorry

def loopTrace : List Action := sorry

def stateA : GameState := sorry

def stateB : GameState := sorry

-- ============================================================
-- VERIFICATION
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB allCards enemy) setupTrace = some stateA := by
  native_decide

theorem loop_ok :
    execute cardDB stateA loopTrace = some stateB := by
  native_decide

theorem same_mod : sameModAccum stateA stateB = true := by native_decide
theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

theorem {ns}_infinite : InfiniteCombo cardDB allCards enemy :=
  \u27e8setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg\u27e9

end {ns}
"""
    os.makedirs(out_dir, exist_ok=True)
    path = os.path.join(out_dir, f"Combo{c['id']}.lean")
    with open(path, "w") as f:
        f.write(content)
    return path

def generate_l2_template(combo, out_dir="StSVerify/CombosTemplateL2"):
    """Generate L2 template: LLM proves combo works for ALL shuffle orders."""
    c = combo
    ns = f"Combo{c['id']}_L2"

    content = f"""/-
  {c['cn_name']} (Level 2: Guaranteed infinite despite shuffle randomness)
  Cards: {c['total_cards']}

  Prove that for ANY valid shuffle oracle (adversarial card ordering),
  the player can STILL loop dealing damage each iteration.

  Setup uses lucky draws (Level 1). The loop proof must handle all shuffles.
-/
import StSVerify.Basic
import StSVerify.CardDB

open CardName Action

namespace {ns}

-- ============================================================
-- FRAMEWORK-PROVIDED (do not modify)
-- ============================================================

{cards_lean_def(c['cards_lean'])}

{enemy_lean_def(c['enemy'])}

/-
  Card reference (id, name, cost, type, effect):
{card_ref_comment(c['cards'])}

  Initial state: all {c['total_cards']} cards in draw pile, 5 draws queued, 3 energy.

{actions_comment()}

  Level 2 proof structure:
    GuaranteedInfiniteCombo requires:
    1. A setupTrace that reaches stateA (lucky draws OK, verified by native_decide)
    2. For ALL valid shuffle oracles:
       - A loopTrace (may depend on oracle output)
       - executeL2 succeeds from stateA with the oracle
       - sameModAccum: same card distribution after loop
       - dealtDamage: more damage after loop

  Key engine types:
    ShuffleOracle = Nat -> List CardInstance -> List CardInstance
    validOracle oracle = forall n pile, List.Perm (oracle n pile) pile
    executeL2: uses oracle to control shuffle order at each draw-from-empty-pile

  Available helper lemmas in Basic.lean:
    drawCardL2_oracle_agree:  oracle agreement on discardPile -> drawCardL2 agrees
    drawCardL2_nonempty_irrel: drawPile non-empty -> oracle irrelevant for drawCardL2
    stepL2_oracle_cond: drawPile non-empty OR oracle agrees -> stepL2 agrees
    executeL2_oraclesCond: general oracle simulation via oraclesCond
    perm_singleton_eq: singleton list has only one permutation

  RULES:
    - native_decide is allowed ONLY for engine computation helpers
      (step, resolveInUse, execute for setup, sameModAccum, dealtDamage)
    - native_decide is NOT allowed in the main GuaranteedInfiniteCombo proof
    - The oracle quantification (forall oracle) must use real proof tactics
-/

-- ============================================================
-- LLM FILLS IN BELOW
-- ============================================================

theorem {ns}_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB allCards enemy := by
  sorry

end {ns}
"""
    os.makedirs(out_dir, exist_ok=True)
    path = os.path.join(out_dir, f"Combo{c['id']}.lean")
    with open(path, "w") as f:
        f.write(content)
    return path

def main():
    combos = load_combos()
    print(f"Loaded {len(combos)} combos")

    for c in combos:
        p1 = generate_l1_template(c)
        p2 = generate_l2_template(c)
        print(f"  {c['id']}: {p1}, {p2}")

    print(f"\nGenerated {len(combos)} L1 templates in StSVerify/CombosTemplateL1/")
    print(f"Generated {len(combos)} L2 templates in StSVerify/CombosTemplateL2/")

if __name__ == "__main__":
    main()
