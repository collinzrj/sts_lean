/-
  StormOfSteel3Prep -- Level 2 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel2Solution/ComboStormOfSteel3Prep.lean
-/
import StSVerify.CombosSpecL2.ComboStormOfSteel3Prep
import StSVerify.CombosLevel2Solution.ComboStormOfSteel3Prep

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboStormOfSteel3Prep_L2_verified :
    GuaranteedInfiniteCombo cardDB
      ComboStormOfSteel3Prep_L2.cards
      ComboStormOfSteel3Prep_L2.enemy :=
  ComboStormOfSteel3Prep_L2.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboStormOfSteel3Prep_L2_verified
