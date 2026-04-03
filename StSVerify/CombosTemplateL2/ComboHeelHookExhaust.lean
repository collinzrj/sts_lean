/-
  静默猎手 - 足跟勾+消耗精简 (Level 2: Guaranteed infinite despite shuffle randomness)
  Cards: 10

  Prove that for ANY valid shuffle oracle (adversarial card ordering),
  the player can STILL loop dealing damage each iteration.

  Setup uses lucky draws (Level 1). The loop proof must handle all shuffles.
-/
import StSVerify.Basic
import StSVerify.CardDB

open CardName Action

namespace ComboHeelHookExhaust_L2

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

theorem ComboHeelHookExhaust_L2_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB allCards enemy := by
  sorry

end ComboHeelHookExhaust_L2
