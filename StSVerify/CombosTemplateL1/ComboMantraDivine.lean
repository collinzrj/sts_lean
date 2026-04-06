/-
  MantraDivine -- Level 1 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel1Solution/ComboMantraDivine.lean
-/
import StSVerify.CombosSpecL1.ComboMantraDivine
import StSVerify.CombosLevel1Solution.ComboMantraDivine

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboMantraDivine_L1_verified :
    InfiniteCombo cardDB
      ComboMantraDivine_L1.cards
      ComboMantraDivine_L1.enemy :=
  ComboMantraDivine_L1.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboMantraDivine_L1_verified
