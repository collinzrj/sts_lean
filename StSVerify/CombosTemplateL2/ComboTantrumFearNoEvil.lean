/-
  TantrumFearNoEvil -- Level 2 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel2Solution/ComboTantrumFearNoEvil.lean
-/
import StSVerify.CombosSpecL2.ComboTantrumFearNoEvil
import StSVerify.CombosLevel2Solution.ComboTantrumFearNoEvil

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboTantrumFearNoEvil_L2_verified :
    GuaranteedInfiniteCombo cardDB
      ComboTantrumFearNoEvil_L2.cards
      ComboTantrumFearNoEvil_L2.enemy :=
  ComboTantrumFearNoEvil_L2.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboTantrumFearNoEvil_L2_verified
