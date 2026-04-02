/-
  故障机器人 - 流线型+全息影像+精简 (Level 2: Guaranteed infinite despite shuffle randomness)
  Cards: 11

  Prove that for ANY valid shuffle oracle (adversarial card ordering),
  the player can STILL loop dealing damage each iteration.

  Setup uses lucky draws (Level 1). The loop proof must handle all shuffles.
-/
import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB

open CardName Action

namespace ComboStreamlineHologram_L2

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

theorem ComboStreamlineHologram_L2_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB allCards enemy := by
  sorry

end ComboStreamlineHologram_L2
