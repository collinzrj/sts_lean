/-
  StormStrike -- Level 2 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel2Solution/ComboStormStrike.lean
-/
import StSVerify.CombosSpecL2.ComboStormStrike
import StSVerify.CombosLevel2Solution.ComboStormStrike

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboStormStrike_L2_verified :
    GuaranteedInfiniteCombo cardDB
      ComboStormStrike_L2.cards
      ComboStormStrike_L2.enemy :=
  ComboStormStrike_L2.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboStormStrike_L2_verified
