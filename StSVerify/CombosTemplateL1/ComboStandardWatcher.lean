/-
  StandardWatcher -- Level 1 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel1Solution/ComboStandardWatcher.lean
-/
import StSVerify.CombosSpecL1.ComboStandardWatcher
import StSVerify.CombosLevel1Solution.ComboStandardWatcher

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboStandardWatcher_L1_verified :
    InfiniteCombo cardDB
      ComboStandardWatcher_L1.cards
      ComboStandardWatcher_L1.enemy :=
  ComboStandardWatcher_L1.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboStandardWatcher_L1_verified
