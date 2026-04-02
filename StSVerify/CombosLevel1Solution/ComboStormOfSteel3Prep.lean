/-
  Storm of Steel+ + Tactician+ + Reflex+ + 3x Prepared+ (6 cards)
  16 damage per loop (4 Shivs x 4 damage)

  Engine v2: CardInstance system, no token bags.
  Storm creates Shiv CardInstances dynamically via nextId.
  autoDrain discards hand R-to-L, fires Tactician (+2E) and Reflex (draw 3).
  endTurn resets energy to 3 each loop.
  Only 5 cards drawn per turn; Prep#3 stays in draw pile.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboStormOfSteel3Prep

def cards : List (CardName × Nat) := [
  (StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1), (PreparedPlus, 3)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- Card instance IDs:
-- 0 = Storm of Steel+, 1 = Tactician+, 2 = Reflex+,
-- 3 = Prepared+#1, 4 = Prepared+#2, 5 = Prepared+#3

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0,                          -- Storm: 4 hand cards -> 4 Shivs(6,7,8,9), Tact+2E, Reflex draw 3
  .draw 5, .draw 3, .draw 4,       -- draw Prep5 from drawPile, shuffle, draw Prep3, Prep4
  .play 6, .play 7, .play 8, .play 9, -- play 4 Shivs
  .play 3, .draw 2, .draw 1, .discard 1, -- Prep: draw 2 (Reflex, Tact from shuffled), discard Tact (+2E)
  .endTurn,                          -- reset energy to 3
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4
]

def loopTrace : List Action := [
  .play 0,                          -- Storm: 4 hand cards -> 4 Shivs, Tact+2E, Reflex draw 3
  .draw 5, .draw 3, .draw 4,       -- draw Prep5 from drawPile, shuffle, draw 2
  .play 10, .play 11, .play 12, .play 13, -- play 4 Shivs
  .play 3, .draw 2, .draw 1, .discard 1, -- Prep: draw 2, discard Tact (+2E)
  .endTurn,
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4
]

-- #eval execute cardDB (mkInitialState cardDB cards enemy) setupTrace
-- #eval execute cardDB (mkInitialState cardDB cards enemy) (setupTrace ++ loopTrace)

def stateA : GameState := {
  hand := [{ id := 4, name := PreparedPlus, cost := 0, damage := 0 },
           { id := 3, name := PreparedPlus, cost := 0, damage := 0 },
           { id := 2, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 1, name := TacticianPlus, cost := 0, damage := 0 },
           { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }]
  drawPile := [{ id := 5, name := PreparedPlus, cost := 0, damage := 0 }]
  discardPile := []
  exhaustPile := [{ id := 9, name := Shiv, cost := 0, damage := 4 },
                  { id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 16
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := []
  nextId := 10
  noDraw := false
  corruptionActive := false
}

def stateB : GameState := {
  hand := [{ id := 4, name := PreparedPlus, cost := 0, damage := 0 },
           { id := 3, name := PreparedPlus, cost := 0, damage := 0 },
           { id := 2, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 1, name := TacticianPlus, cost := 0, damage := 0 },
           { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }]
  drawPile := [{ id := 5, name := PreparedPlus, cost := 0, damage := 0 }]
  discardPile := []
  exhaustPile := [{ id := 13, name := Shiv, cost := 0, damage := 4 },
                  { id := 12, name := Shiv, cost := 0, damage := 4 },
                  { id := 11, name := Shiv, cost := 0, damage := 4 },
                  { id := 10, name := Shiv, cost := 0, damage := 4 },
                  { id := 9, name := Shiv, cost := 0, damage := 4 },
                  { id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 32
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := []
  nextId := 14
  noDraw := false
  corruptionActive := false
}

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

theorem loop_ok :
    execute cardDB stateA loopTrace = some stateB := by
  native_decide

theorem same_mod : sameModAccum stateA stateB = true := by native_decide
theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

theorem ComboStormOfSteel3Prep_infinite : InfiniteCombo cardDB cards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboStormOfSteel3Prep
