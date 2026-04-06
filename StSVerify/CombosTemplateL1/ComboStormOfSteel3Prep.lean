/-
  StormOfSteel3Prep -- Level 1 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel1Solution/ComboStormOfSteel3Prep.lean
-/
import StSVerify.CombosSpecL1.ComboStormOfSteel3Prep
import StSVerify.CombosLevel1Solution.ComboStormOfSteel3Prep

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboStormOfSteel3Prep_L1_verified :
    InfiniteCombo cardDB
      ComboStormOfSteel3Prep_L1.cards
      ComboStormOfSteel3Prep_L1.enemy :=
  ComboStormOfSteel3Prep_L1.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboStormOfSteel3Prep_L1_verified
