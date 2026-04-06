/-
  StandardWatcher -- Level 2 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel2Solution/ComboStandardWatcher.lean
-/
import StSVerify.CombosSpecL2.ComboStandardWatcher
import StSVerify.CombosLevel2Solution.ComboStandardWatcher

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboStandardWatcher_L2_verified :
    GuaranteedInfiniteCombo cardDB
      ComboStandardWatcher_L2.cards
      ComboStandardWatcher_L2.enemy :=
  ComboStandardWatcher_L2.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboStandardWatcher_L2_verified
