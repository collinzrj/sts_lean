/-
  AcrobaticsTactician -- Level 1 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel1Solution/ComboAcrobaticsTactician.lean
-/
import StSVerify.CombosSpecL1.ComboAcrobaticsTactician
import StSVerify.CombosLevel1Solution.ComboAcrobaticsTactician

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboAcrobaticsTactician_L1_verified :
    InfiniteCombo cardDB
      ComboAcrobaticsTactician_L1.cards
      ComboAcrobaticsTactician_L1.enemy :=
  ComboAcrobaticsTactician_L1.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboAcrobaticsTactician_L1_verified
