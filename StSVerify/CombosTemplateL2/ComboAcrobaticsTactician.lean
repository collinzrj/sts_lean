/-
  AcrobaticsTactician — Level 2 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel2Solution/ComboAcrobaticsTactician.lean
-/
import StSVerify.CombosSpecL2.ComboAcrobaticsTactician
import StSVerify.CombosLevel2Solution.ComboAcrobaticsTactician

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboAcrobaticsTactician_L2_verified :
    GuaranteedInfiniteCombo cardDB
      ComboAcrobaticsTactician_L2.cards
      ComboAcrobaticsTactician_L2.enemy :=
  ComboAcrobaticsTactician_L2.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboAcrobaticsTactician_L2_verified
