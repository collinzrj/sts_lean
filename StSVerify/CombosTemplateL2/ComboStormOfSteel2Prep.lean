/-
  StormOfSteel2Prep -- Level 2 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel2Solution/ComboStormOfSteel2Prep.lean
-/
import StSVerify.CombosSpecL2.ComboStormOfSteel2Prep
import StSVerify.CombosLevel2Solution.ComboStormOfSteel2Prep

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboStormOfSteel2Prep_L2_verified :
    GuaranteedInfiniteCombo cardDB
      ComboStormOfSteel2Prep_L2.cards
      ComboStormOfSteel2Prep_L2.enemy :=
  ComboStormOfSteel2Prep_L2.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboStormOfSteel2Prep_L2_verified
