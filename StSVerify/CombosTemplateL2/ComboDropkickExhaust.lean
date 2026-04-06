/-
  DropkickExhaust -- Level 2 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel2Solution/ComboDropkickExhaust.lean
-/
import StSVerify.CombosSpecL2.ComboDropkickExhaust
import StSVerify.CombosLevel2Solution.ComboDropkickExhaust

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboDropkickExhaust_L2_verified :
    GuaranteedInfiniteCombo cardDB
      ComboDropkickExhaust_L2.cards
      ComboDropkickExhaust_L2.enemy :=
  ComboDropkickExhaust_L2.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboDropkickExhaust_L2_verified
