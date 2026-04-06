/-
  StreamlineHologram -- Level 2 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel2Solution/ComboStreamlineHologram.lean
-/
import StSVerify.CombosSpecL2.ComboStreamlineHologram
import StSVerify.CombosLevel2Solution.ComboStreamlineHologram

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboStreamlineHologram_L2_verified :
    GuaranteedInfiniteCombo cardDB
      ComboStreamlineHologram_L2.cards
      ComboStreamlineHologram_L2.enemy :=
  ComboStreamlineHologram_L2.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboStreamlineHologram_L2_verified
