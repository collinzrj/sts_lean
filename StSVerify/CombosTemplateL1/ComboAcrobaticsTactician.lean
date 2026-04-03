/-
  AcrobaticsTactician (Level 1: Existence of infinite loop)
  Cards: 12

  Prove there EXISTS a sequence of actions that loops,
  dealing damage each iteration. Lucky draws are OK.
-/
import StSVerify.Basic
import StSVerify.CardDB

open CardName Action

namespace ComboAcrobaticsTactician

-- ============================================================
-- FRAMEWORK-PROVIDED (do not modify)
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(AcrobaticsPlus, 2), (TacticianPlus, 1), (ReflexPlus, 1), (BackflipPlus, 2), (NeutralizePlus, 1), (AfterImage, 1), (AdrenalinePlus, 1), (CaltropPlus, 1), (EscapePlanPlus, 1), (GrandFinalePlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

/-
  Card reference (id, name, cost, type, effect):
    id= 0  杂技+ #1 (AcrobaticsPlus, 1E, Skill): Draw 4 cards. Discard 1 card.
    id= 1  杂技+ #2 (AcrobaticsPlus, 1E, Skill): Draw 4 cards. Discard 1 card.
    id= 2  战术大师+ (TacticianPlus, 0E, Skill): Cannot be played. On discard: gain 2 energy.
    id= 3  本能反应+ (ReflexPlus, 0E, Skill): Cannot be played. On discard: draw 3 cards.
    id= 4  后空翻+ #1 (BackflipPlus, 1E, Skill): Gain 8 Block. Draw 2 cards.
    id= 5  后空翻+ #2 (BackflipPlus, 1E, Skill): Gain 8 Block. Draw 2 cards.
    id= 6  中和+ (NeutralizePlus, 0E, Attack): Deal 4 damage. Apply 2 Weak.
    id= 7  残影 (AfterImage, 1E, Power): Whenever you play a card, gain 1 Block.
    id= 8  肾上腺素+ (AdrenalinePlus, 0E, Skill): Gain 2 energy. Draw 2 cards. Exhaust.
    id= 9  铁蒺藜+ (CaltropPlus, 1E, Power): Whenever you are attacked, deal 5 damage back.
    id=10  逃跑计划+ (EscapePlanPlus, 0E, Skill): Draw 1 card. If it's a Skill, gain 5 Block.
    id=11  终幕+ (GrandFinalePlus, 0E, Attack): Can only be played if draw pile is empty. Deal 60 damage.

  Initial state: all 12 cards in draw pile, 5 draws queued, 3 energy.
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

theorem ComboAcrobaticsTactician_infinite : InfiniteCombo cardDB allCards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboAcrobaticsTactician
