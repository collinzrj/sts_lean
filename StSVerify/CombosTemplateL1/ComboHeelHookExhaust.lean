/-
  静默猎手 - 足跟勾+消耗精简 (Level 1: Existence of infinite loop)
  Cards: 10

  Prove there EXISTS a sequence of actions that loops,
  dealing damage each iteration. Lucky draws are OK.
-/
import StSVerify.Basic
import StSVerify.CardDB

open CardName Action

namespace ComboHeelHookExhaust

-- ============================================================
-- FRAMEWORK-PROVIDED (do not modify)
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(HeelHookPlus, 2), (NeutralizePlus, 1), (MalaisePlus, 1), (PiercingWail, 1), (AdrenalinePlus, 1), (DieDieDiePlus, 1), (AfterImage, 1), (EscapePlanPlus, 1), (BackflipPlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 2, intending := false }

/-
  Card reference (id, name, cost, type, effect):
    id= 0  足跟勾+ #1 (HeelHookPlus, 1E, Attack): Deal 8 damage. If enemy is Weak: gain 1 energy, draw 1 card.
    id= 1  足跟勾+ #2 (HeelHookPlus, 1E, Attack): Deal 8 damage. If enemy is Weak: gain 1 energy, draw 1 card.
    id= 2  中和+ (NeutralizePlus, 0E, Attack): Deal 4 damage. Apply 2 Weak.
    id= 3  萎靡+ (MalaisePlus, 0E, Skill): Apply X+1 Weak. Enemy loses X+1 Strength. Exhaust. (X=energy spent)
    id= 4  刺耳尖叫 (PiercingWail, 1E, Skill): ALL enemies lose 8 Strength. Exhaust.
    id= 5  肾上腺素+ (AdrenalinePlus, 0E, Skill): Gain 2 energy. Draw 2 cards. Exhaust.
    id= 6  连环杀+ (DieDieDiePlus, 1E, Attack): Deal 5 damage to ALL enemies 3 times. Exhaust.
    id= 7  残影 (AfterImage, 1E, Power): Whenever you play a card, gain 1 Block.
    id= 8  逃跑计划+ (EscapePlanPlus, 0E, Skill): Draw 1 card. If it's a Skill, gain 5 Block.
    id= 9  后空翻+ (BackflipPlus, 1E, Skill): Gain 8 Block. Draw 2 cards.

  Initial state: all 10 cards in draw pile, 5 draws queued, 3 energy.
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

theorem ComboHeelHookExhaust_infinite : InfiniteCombo cardDB allCards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboHeelHookExhaust
