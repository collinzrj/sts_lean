/-
  Storm of Steel+ + Tactician+ + Reflex+ + 3×Prepared+ (6 cards) - Level 2

  This is the HARDEST combo in the benchmark. Unlike all other combos, the 6-card
  deck creates cascading oracle interactions that prevent a simple period-1 loop:

  - The loop draws 2 of 3 from a sub-shuffle, stranding 1 card in drawPile.
  - The stranded card varies per oracle → state is (hand=5, draw=1), not (hand=6, draw=0).
  - The adversary can strand Reflex, killing the draw-3 trigger in the next iteration.

  The combo IS UnboundedDamage (the player can adaptively deal damage by keeping
  Reflex in hand and using Preps to cycle), but proving it requires analyzing a
  complex multi-iteration adaptive strategy — well beyond single-loop native_decide.

  Proof target: UnboundedDamage (not GuaranteedInfiniteCombo).
  Status: OPEN — no reference solution provided.
-/
import StSVerify.CombosSpecL2.ComboStormOfSteel3Prep
import StSVerify.ExtendedTargets
open CardName Action

namespace ComboStormOfSteel3Prep_L2

private def ci0 : CardInstance := { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }
private def ci1 : CardInstance := { id := 1, name := TacticianPlus, cost := 0, damage := 0 }
private def ci2 : CardInstance := { id := 2, name := ReflexPlus, cost := 0, damage := 0 }
private def ci3 : CardInstance := { id := 3, name := PreparedPlus, cost := 0, damage := 0 }
private def ci4 : CardInstance := { id := 4, name := PreparedPlus, cost := 0, damage := 0 }
private def ci5 : CardInstance := { id := 5, name := PreparedPlus, cost := 0, damage := 0 }

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0, .draw 5, .draw 1, .draw 2,
  .play 6, .play 7, .play 8, .play 9,
  .play 5, .draw 0, .draw 4, .discard 2, .discard 1,
  .draw 3, .draw 2, .draw 1,
  .play 3, .draw 5, .failDraw, .discard 2, .discard 1,
  .draw 3, .draw 2, .draw 1]

def stateA : GameState := {
  hand := [ci1, ci2, ci3, ci5, ci4, ci0]
  drawPile := []
  discardPile := []
  exhaustPile := [{ id := 9, name := Shiv, cost := 0, damage := 4 },
                  { id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 }]
  inUse := []
  actionQueue := []
  energy := 8
  damage := 16
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 10
  noDraw := false
  corruptionActive := false
}

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

theorem ComboStormOfSteel3Prep_unbounded_damage :
    UnboundedDamage cardDB cards enemy := by
  sorry

theorem proof : GuaranteedInfiniteCombo cardDB cards enemy := by sorry

end ComboStormOfSteel3Prep_L2
