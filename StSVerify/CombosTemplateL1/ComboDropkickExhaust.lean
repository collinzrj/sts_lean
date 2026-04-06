/-
  DropkickExhaust -- Level 1 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel1Solution/ComboDropkickExhaust.lean
-/
import StSVerify.CombosSpecL1.ComboDropkickExhaust
import StSVerify.CombosLevel1Solution.ComboDropkickExhaust

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboDropkickExhaust_L1_verified :
    InfiniteCombo cardDB
      ComboDropkickExhaust_L1.cards
      ComboDropkickExhaust_L1.enemy :=
  ComboDropkickExhaust_L1.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboDropkickExhaust_L1_verified
