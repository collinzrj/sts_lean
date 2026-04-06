/-
  MantraDivine -- Level 2 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel2Solution/ComboMantraDivine.lean
-/
import StSVerify.CombosSpecL2.ComboMantraDivine
import StSVerify.CombosLevel2Solution.ComboMantraDivine

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboMantraDivine_L2_verified :
    GuaranteedInfiniteCombo cardDB
      ComboMantraDivine_L2.cards
      ComboMantraDivine_L2.enemy :=
  ComboMantraDivine_L2.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboMantraDivine_L2_verified
