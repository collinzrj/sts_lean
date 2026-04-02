/-
  铁甲战士 - 腐化消耗精简+飞踢 (Level 1: Existence of infinite loop)
  Cards: 13

  Prove there EXISTS a sequence of actions that loops,
  dealing damage each iteration. Lucky draws are OK.
-/
import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboCorruptionDropkick

-- ============================================================
-- FRAMEWORK-PROVIDED (do not modify)
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(Corruption, 1), (DarkEmbracePlus, 1), (FeelNoPainPlus, 1), (BashPlus, 1), (Dropkick, 2), (ShrugItOff, 2), (TrueGritPlus, 1), (MetallicizePlus, 1), (ImperviousPlus, 1), (Offering, 1), (BattleTrancePlus, 1)]

def enemy : EnemyState := { vulnerable := 3, weak := 0, intending := false }

/-
  Card reference (id, name, cost, type, effect):
    id= 0  腐化 (Corruption, 2E, Power): Skills cost 0. Whenever you play a Skill, Exhaust it.
    id= 1  黑暗拥抱+ (DarkEmbracePlus, 1E, Power): Whenever a card is Exhausted, draw 2 cards.
    id= 2  毫无痛觉+ (FeelNoPainPlus, 1E, Power): Whenever a card is Exhausted, gain 4 Block.
    id= 3  痛击+ (BashPlus, 2E, Attack): Deal 10 damage. Apply 3 Vulnerable.
    id= 4  飞踢 #1 (Dropkick, 1E, Attack): Deal 5 damage. If enemy is Vulnerable: gain 1 energy, draw 1 card.
    id= 5  飞踢 #2 (Dropkick, 1E, Attack): Deal 5 damage. If enemy is Vulnerable: gain 1 energy, draw 1 card.
    id= 6  耸肩无视 #1 (ShrugItOff, 1E, Skill): Gain 8 Block. Draw 1 card.
    id= 7  耸肩无视 #2 (ShrugItOff, 1E, Skill): Gain 8 Block. Draw 1 card.
    id= 8  意志坚定+ (TrueGritPlus, 1E, Skill): Gain 9 Block. Exhaust a chosen card from hand.
    id= 9  金属化+ (MetallicizePlus, 1E, Power): At the end of your turn, gain 4 Block.
    id=10  坚不可摧+ (ImperviousPlus, 2E, Skill): Gain 40 Block. Exhaust.
    id=11  祭品 (Offering, 0E, Skill): Lose 6 HP. Gain 2 energy. Draw 5 cards. Exhaust.
    id=12  战斗冥想+ (BattleTrancePlus, 0E, Skill): Draw 2 cards. Cannot draw additional cards this turn. Exhaust.

  Initial state: all 13 cards in draw pile, 5 draws queued, 3 energy.
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

theorem ComboCorruptionDropkick_infinite : InfiniteCombo cardDB allCards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboCorruptionDropkick
