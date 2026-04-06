/-
  StormStrike -- Level 1 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel1Solution/ComboStormStrike.lean
-/
import StSVerify.CombosSpecL1.ComboStormStrike
import StSVerify.CombosLevel1Solution.ComboStormStrike

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboStormStrike_L1_verified :
    InfiniteCombo cardDB
      ComboStormStrike_L1.cards
      ComboStormStrike_L1.enemy :=
  ComboStormStrike_L1.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboStormStrike_L1_verified
