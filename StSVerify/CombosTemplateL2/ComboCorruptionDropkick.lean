/-
  铁甲战士 - 腐化消耗精简+飞踢 (Level 2: Guaranteed infinite despite shuffle randomness)
  Cards: 13

  Prove that for ANY valid shuffle oracle (adversarial card ordering),
  the player can STILL loop dealing damage each iteration.

  Setup uses lucky draws (Level 1). The loop proof must handle all shuffles.
-/
import StSVerify.Basic
import StSVerify.CardDB

open CardName Action

namespace ComboCorruptionDropkick_L2

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

theorem ComboCorruptionDropkick_L2_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB allCards enemy := by
  sorry

end ComboCorruptionDropkick_L2
