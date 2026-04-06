/-
  HeelHookExhaust -- Level 1 Checker (READ-ONLY)

  This file verifies that the solution provides a valid proof.
  DO NOT MODIFY this file. Write your proof in:
    StSVerify/CombosLevel1Solution/ComboHeelHookExhaust.lean
-/
import StSVerify.CombosSpecL1.ComboHeelHookExhaust
import StSVerify.CombosLevel1Solution.ComboHeelHookExhaust

-- Type forcing: must match spec's cards and enemy exactly
theorem ComboHeelHookExhaust_L1_verified :
    InfiniteCombo cardDB
      ComboHeelHookExhaust_L1.cards
      ComboHeelHookExhaust_L1.enemy :=
  ComboHeelHookExhaust_L1.proof

-- Axiom auditing: must not depend on sorry or custom axioms
-- Expected output: only propext, Classical.choice, Quot.sound
#print axioms ComboHeelHookExhaust_L1_verified
