/-
  观者 - 真言/神格混合无限 (Level 2: Guaranteed infinite despite shuffle randomness)
  Cards: 13

  Prove that for ANY valid shuffle oracle (adversarial card ordering),
  the player can STILL loop dealing damage each iteration.

  Setup uses lucky draws (Level 1). The loop proof must handle all shuffles.
-/
import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboMantraDivine_L2

-- ============================================================
-- FRAMEWORK-PROVIDED (do not modify)
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(Rushdown, 2), (MentalFortressPlus, 1), (EruptionPlus, 1), (InnerPeace, 1), (PrayPlus, 1), (ProstatePlus, 1), (EmptyMindPlus, 1), (FlurryOfBlowsPlus, 1), (Scrawl, 1), (VaultPlus, 1), (DeusExMachina, 1), (OmnisciencePlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

/-
  Card reference (id, name, cost, type, effect):
    id= 0  冲锋 #1 (Rushdown, 1E, Power): Whenever you enter Wrath, draw 2 cards.
    id= 1  冲锋 #2 (Rushdown, 1E, Power): Whenever you enter Wrath, draw 2 cards.
    id= 2  精神堡垒+ (MentalFortressPlus, 1E, Power): Whenever you change Stance, gain 6 Block.
    id= 3  喷发+ (EruptionPlus, 1E, Attack): Deal 10 damage. Enter Wrath.
    id= 4  心如止水 (InnerPeace, 1E, Skill): If Calm: enter Wrath. Otherwise: enter Calm.
    id= 5  祈祷+ (PrayPlus, 1E, Skill): Gain 4 Mantra. Gain 8 Block.
    id= 6  叩拜+ (ProstatePlus, 0E, Skill): Gain 3 Mantra. Gain 4 Block.
    id= 7  放空精神+ (EmptyMindPlus, 1E, Skill): Draw 3 cards. Exit your Stance.
    id= 8  连续拳+ (FlurryOfBlowsPlus, 0E, Attack): Deal 6 damage. Whenever you change Stance, play this from discard.
    id= 9  涂鸦 (Scrawl, 0E, Skill): Draw cards until hand is full (10). Exhaust.
    id=10  拱顶+ (VaultPlus, 2E, Skill): Take an additional turn. Exhaust.
    id=11  天降奇兵 (DeusExMachina, 0E, Skill): On draw: add 2 Miracles to hand. Exhaust.
    id=12  全知+ (OmnisciencePlus, 3E, Skill): Play a card from draw pile twice. Exhaust.

  Initial state: all 13 cards in draw pile, 5 draws queued, 3 energy.

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

theorem ComboMantraDivine_L2_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB allCards enemy := by
  sorry

end ComboMantraDivine_L2
