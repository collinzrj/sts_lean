/-
  StormOfSteel -- Level 1 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel1Solution/ComboStormOfSteel.lean
-/
import StSVerify.CombosSpecL1.ComboStormOfSteel
import StSVerify.CombosLevel1Solution.ComboStormOfSteel

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboStormOfSteel_L1_verified :
    InfiniteCombo cardDB
      ComboStormOfSteel_L1.cards
      ComboStormOfSteel_L1.enemy :=
  ComboStormOfSteel_L1.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboStormOfSteel_L1_verified
