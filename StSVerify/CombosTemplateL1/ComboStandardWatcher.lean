/-
  观者 - 标准沙雕无限 (Level 1: Existence of infinite loop)
  Cards: 12

  Prove there EXISTS a sequence of actions that loops,
  dealing damage each iteration. Lucky draws are OK.
-/
import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboStandardWatcher

-- ============================================================
-- FRAMEWORK-PROVIDED (do not modify)
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(Rushdown, 2), (MentalFortressPlus, 1), (EruptionPlus, 1), (TantrumPlus, 1), (InnerPeacePlus, 1), (FearNoEvilPlus, 1), (FlurryOfBlowsPlus, 1), (Scrawl, 1), (VaultPlus, 1), (DeusExMachina, 1), (TalkToTheHandPlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := true }

/-
  Card reference (id, name, cost, type, effect):
    id= 0  冲锋 #1 (Rushdown, 1E, Power): Whenever you enter Wrath, draw 2 cards.
    id= 1  冲锋 #2 (Rushdown, 1E, Power): Whenever you enter Wrath, draw 2 cards.
    id= 2  精神堡垒+ (MentalFortressPlus, 1E, Power): Whenever you change Stance, gain 6 Block.
    id= 3  喷发+ (EruptionPlus, 1E, Attack): Deal 10 damage. Enter Wrath.
    id= 4  发泄+ (TantrumPlus, 1E, Attack): Deal 12 damage. Enter Wrath. Shuffle into draw pile.
    id= 5  心如止水+ (InnerPeacePlus, 1E, Skill): If Calm: enter Wrath. Otherwise: enter Calm. Draw 3 cards.
    id= 6  不惧妖邪+ (FearNoEvilPlus, 1E, Attack): Deal 11 damage. If enemy intends to attack: enter Calm.
    id= 7  连续拳+ (FlurryOfBlowsPlus, 0E, Attack): Deal 6 damage. Whenever you change Stance, play this from discard.
    id= 8  涂鸦 (Scrawl, 0E, Skill): Draw cards until hand is full (10). Exhaust.
    id= 9  拱顶+ (VaultPlus, 2E, Skill): Take an additional turn. Exhaust.
    id=10  天降奇兵 (DeusExMachina, 0E, Skill): On draw: add 2 Miracles to hand. Exhaust.
    id=11  以手代口+ (TalkToTheHandPlus, 1E, Attack): Deal 7 damage. Whenever this enemy deals damage, gain 3 Block. Exhaust.

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

theorem ComboStandardWatcher_infinite : InfiniteCombo cardDB allCards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboStandardWatcher
