/-
  铁甲战士 - 飞踢消耗精简无限 (Level 2: Guaranteed infinite despite shuffle randomness)
  Cards: 11

  Prove that for ANY valid shuffle oracle (adversarial card ordering),
  the player can STILL loop dealing damage each iteration.

  Setup uses lucky draws (Level 1). The loop proof must handle all shuffles.
-/
import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB

open CardName Action

namespace ComboDropkickExhaust_L2

-- ============================================================
-- FRAMEWORK-PROVIDED (do not modify)
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(BashPlus, 1), (Dropkick, 2), (TrueGritPlus, 2), (BurningPactPlus, 1), (ShrugItOffPlus, 1), (OfferingPlus, 1), (Purity, 1), (BattleCryPlus, 1), (PommelStrikePlus, 1)]

def enemy : EnemyState := { vulnerable := 3, weak := 0, intending := false }

/-
  Card reference (id, name, cost, type, effect):
    id= 0  痛击+ (BashPlus, 2E, Attack): Deal 10 damage. Apply 3 Vulnerable.
    id= 1  飞踢 #1 (Dropkick, 1E, Attack): Deal 5 damage. If enemy is Vulnerable: gain 1 energy, draw 1 card.
    id= 2  飞踢 #2 (Dropkick, 1E, Attack): Deal 5 damage. If enemy is Vulnerable: gain 1 energy, draw 1 card.
    id= 3  意志坚定+ #1 (TrueGritPlus, 1E, Skill): Gain 9 Block. Exhaust a chosen card from hand.
    id= 4  意志坚定+ #2 (TrueGritPlus, 1E, Skill): Gain 9 Block. Exhaust a chosen card from hand.
    id= 5  燃烧契约+ (BurningPactPlus, 1E, Skill): Exhaust 1 card from hand. Draw 3 cards.
    id= 6  耸肩无视+ (ShrugItOffPlus, 1E, Skill): Gain 11 Block. Draw 1 card.
    id= 7  祭品+ (OfferingPlus, 0E, Skill): Lose 6 HP. Gain 2 energy. Draw 5 cards. Exhaust.
    id= 8  净化 (Purity, 0E, Skill): Exhaust up to 3 cards from hand. Exhaust.
    id= 9  战吼+ (BattleCryPlus, 0E, Skill): Put a card from hand on top of draw pile. Exhaust.
    id=10  剑柄打击+ (PommelStrikePlus, 1E, Attack): Deal 10 damage. Draw 2 cards.

  Initial state: all 11 cards in draw pile, 5 draws queued, 3 energy.

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

theorem ComboDropkickExhaust_L2_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB allCards enemy := by
  sorry

end ComboDropkickExhaust_L2
