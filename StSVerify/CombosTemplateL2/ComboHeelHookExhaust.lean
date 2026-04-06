/-
  HeelHookExhaust -- Level 2 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel2Solution/ComboHeelHookExhaust.lean
-/
import StSVerify.CombosSpecL2.ComboHeelHookExhaust
import StSVerify.CombosLevel2Solution.ComboHeelHookExhaust

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboHeelHookExhaust_L2_verified :
    GuaranteedInfiniteCombo cardDB
      ComboHeelHookExhaust_L2.cards
      ComboHeelHookExhaust_L2.enemy :=
  ComboHeelHookExhaust_L2.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboHeelHookExhaust_L2_verified
