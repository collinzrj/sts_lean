/-
  StormOfSteel (Level 1: Existence of infinite loop)
  Cards: 4

  Prove there EXISTS a sequence of actions that loops,
  dealing damage each iteration. Lucky draws are OK.
-/
import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboStormOfSteel

-- ============================================================
-- FRAMEWORK-PROVIDED (do not modify)
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1), (PreparedPlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

/-
  Card reference (id, name, cost, type, effect):
    id= 0  钢铁风暴+ (StormOfSteelPlus, 1E, Skill): Discard your hand. Add 1 Shiv per card discarded.
    id= 1  战术大师+ (TacticianPlus, 0E, Skill): Cannot be played. On discard: gain 2 energy.
    id= 2  本能反应+ (ReflexPlus, 0E, Skill): Cannot be played. On discard: draw 3 cards.
    id= 3  早有准备+ (PreparedPlus, 0E, Skill): Draw 2 cards. Discard 2 cards.

  Initial state: all 4 cards in draw pile, 5 draws queued, 3 energy.
  Your first actions must be .draw to pick your opening hand.

  Available actions:
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
    .recycleChoose <id>     -- exhaust card for energy (Recycle effect)

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

theorem ComboStormOfSteel_infinite : InfiniteCombo cardDB allCards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboStormOfSteel
