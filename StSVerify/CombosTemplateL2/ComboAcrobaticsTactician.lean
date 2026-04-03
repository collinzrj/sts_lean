/-
  AcrobaticsTactician (Level 2: Guaranteed infinite despite shuffle randomness)
  Cards: 12

  Prove that for ANY valid shuffle oracle (adversarial card ordering),
  the player can STILL loop dealing damage each iteration.

  Setup uses lucky draws (Level 1). The loop proof must handle all shuffles.
-/
import StSVerify.Basic
import StSVerify.CardDB

open CardName Action

namespace ComboAcrobaticsTactician_L2

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

theorem ComboAcrobaticsTactician_L2_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB allCards enemy := by
  sorry

end ComboAcrobaticsTactician_L2
