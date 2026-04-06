/-
  CorruptionDropkick -- Level 1 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel1Solution/ComboCorruptionDropkick.lean
-/
import StSVerify.CombosSpecL1.ComboCorruptionDropkick
import StSVerify.CombosLevel1Solution.ComboCorruptionDropkick

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboCorruptionDropkick_L1_verified :
    InfiniteCombo cardDB
      ComboCorruptionDropkick_L1.cards
      ComboCorruptionDropkick_L1.enemy :=
  ComboCorruptionDropkick_L1.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboCorruptionDropkick_L1_verified
