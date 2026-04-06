/-
  CorruptionDropkick -- Level 2 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel2Solution/ComboCorruptionDropkick.lean
-/
import StSVerify.CombosSpecL2.ComboCorruptionDropkick
import StSVerify.CombosLevel2Solution.ComboCorruptionDropkick

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboCorruptionDropkick_L2_verified :
    GuaranteedInfiniteCombo cardDB
      ComboCorruptionDropkick_L2.cards
      ComboCorruptionDropkick_L2.enemy :=
  ComboCorruptionDropkick_L2.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboCorruptionDropkick_L2_verified
