/-
  TantrumFearNoEvil -- Level 1 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel1Solution/ComboTantrumFearNoEvil.lean
-/
import StSVerify.CombosSpecL1.ComboTantrumFearNoEvil
import StSVerify.CombosLevel1Solution.ComboTantrumFearNoEvil

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboTantrumFearNoEvil_L1_verified :
    InfiniteCombo cardDB
      ComboTantrumFearNoEvil_L1.cards
      ComboTantrumFearNoEvil_L1.enemy :=
  ComboTantrumFearNoEvil_L1.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboTantrumFearNoEvil_L1_verified
