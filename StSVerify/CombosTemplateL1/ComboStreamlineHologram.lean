/-
  故障机器人 - 流线型+全息影像+精简 (Level 1: Existence of infinite loop)
  Cards: 11

  Prove there EXISTS a sequence of actions that loops,
  dealing damage each iteration. Lucky draws are OK.
-/
import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboStreamlineHologram

-- ============================================================
-- FRAMEWORK-PROVIDED (do not modify)
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(StreamlinePlus, 1), (HologramPlus, 2), (CoolheadedPlus, 1), (DefragmentPlus, 1), (BiasedCognitionPlus, 1), (CapacitorPlus, 1), (RecyclePlus, 1), (SkimPlus, 1), (TurboPlus, 1), (RebootPlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

/-
  Card reference (id, name, cost, type, effect):
    id= 0  精简+ (StreamlinePlus, 3E, Attack): Deal 20 damage. Costs 1 less each time played.
    id= 1  全息影像+ #1 (HologramPlus, 1E, Skill): Gain 5 Block. Choose a card from discard pile and put it in hand.
    id= 2  全息影像+ #2 (HologramPlus, 1E, Skill): Gain 5 Block. Choose a card from discard pile and put it in hand.
    id= 3  冷静思考+ (CoolheadedPlus, 0E, Skill): Channel 1 Frost. Draw 2 cards.
    id= 4  碎片整理+ (DefragmentPlus, 0E, Power): Gain 2 Focus.
    id= 5  偏见认知+ (BiasedCognitionPlus, 1E, Power): Gain 5 Focus. Lose 1 Focus at end of each turn.
    id= 6  电容器+ (CapacitorPlus, 1E, Power): Gain 3 Orb slots.
    id= 7  循环利用+ (RecyclePlus, 0E, Skill): Exhaust a card from hand. Gain its cost +1 as energy.
    id= 8  掠读+ (SkimPlus, 1E, Skill): Draw 4 cards.
    id= 9  涡轮+ (TurboPlus, 0E, Skill): Gain 2 energy. Add a Void to discard pile.
    id=10  重启+ (RebootPlus, 0E, Skill): Shuffle all hand and discard into draw pile. Draw 6 cards. Exhaust.

  Initial state: all 11 cards in draw pile, 5 draws queued, 3 energy.
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

theorem ComboStreamlineHologram_infinite : InfiniteCombo cardDB allCards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboStreamlineHologram
