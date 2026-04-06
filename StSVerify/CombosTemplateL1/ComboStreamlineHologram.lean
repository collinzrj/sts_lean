/-
  StreamlineHologram -- Level 1 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel1Solution/ComboStreamlineHologram.lean
-/
import StSVerify.CombosSpecL1.ComboStreamlineHologram
import StSVerify.CombosLevel1Solution.ComboStreamlineHologram

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboStreamlineHologram_L1_verified :
    InfiniteCombo cardDB
      ComboStreamlineHologram_L1.cards
      ComboStreamlineHologram_L1.enemy :=
  ComboStreamlineHologram_L1.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboStreamlineHologram_L1_verified
