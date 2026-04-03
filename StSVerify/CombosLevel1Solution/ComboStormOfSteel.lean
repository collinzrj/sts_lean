/-
  Storm of Steel+ + Tactician+ + Reflex+ + Prepared+ (4 cards)
  8 damage per loop (2 Shivs x 4 damage)

  Engine v2: CardInstance system, no token bags.
  Storm of Steel creates Shiv CardInstances dynamically via nextId.
  autoDrain discards hand R-to-L, fires Tactician (+2E top) and Reflex (draw 3 bottom).
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboStormOfSteel

def cards : List (CardName × Nat) := [
  (StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1), (PreparedPlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- Card instance IDs assigned by mkInitialState:
-- 0 = Storm of Steel+, 1 = Tactician+, 2 = Reflex+, 3 = Prepared+

-- Setup: draw all 4, play Storm (creates Shivs 4,5,6), draw 3, play 3 Shivs
def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .failDraw,
  .play 0,                          -- Storm: discard hand R-to-L, Tact+2E, Reflex draw 3, 3 Shivs
  .draw 1, .draw 2, .draw 3,       -- draw 3 from shuffled discard (SoS resolved to discard by autoDrain)
  .play 4, .play 5, .play 6        -- play 3 Shivs (4 dmg each, exhaust)
]

-- Loop: Prep cycle, discard Reflex+Tact for draw 3 + 2E, play Storm again
-- Creates Shivs 7,8,9 (3 hand cards at Storm time)
def loopTrace : List Action := [
  .play 3,                          -- Prepared+: draw 2, discard 2
  .draw 0, .failDraw,              -- draw SoS from drawPile, fail 2nd (piles empty)
  .discard 2,                       -- discard Reflex (trigger: draw 3 bottom)
  .discard 1,                       -- discard Tact (trigger: +2E); resolveCard 3 auto -> Prep discard
  .draw 1, .draw 2, .draw 3,       -- shuffle [Prep(3),Tact(1),Reflex(2)], draw 3
  .play 0,                          -- Storm: 3 hand cards -> 3 Shivs (7,8,9); autoDrain discards all + SoS
  .draw 1, .draw 2, .draw 3,       -- shuffle [SoS(0),Tact(1),Reflex(2),Prep(3)], draw 3
  .play 7, .play 8, .play 9        -- play 3 Shivs (12 dmg)
]

-- #eval execute cardDB (mkInitialState cardDB cards enemy) setupTrace
-- #eval execute cardDB (mkInitialState cardDB cards enemy) (setupTrace ++ loopTrace)

def stateA : GameState := {
  hand := [{ id := 3, name := PreparedPlus, cost := 0, damage := 0 },
           { id := 2, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 1, name := TacticianPlus, cost := 0, damage := 0 }]
  drawPile := [{ id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }]
  discardPile := []
  exhaustPile := [{ id := 6, name := Shiv, cost := 0, damage := 4 },
                  { id := 5, name := Shiv, cost := 0, damage := 4 },
                  { id := 4, name := Shiv, cost := 0, damage := 4 }]
  inUse := []
  actionQueue := []
  energy := 4
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := []
  nextId := 7
  noDraw := false
  corruptionActive := false
}

def stateB : GameState := {
  hand := [{ id := 3, name := PreparedPlus, cost := 0, damage := 0 },
           { id := 2, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 1, name := TacticianPlus, cost := 0, damage := 0 }]
  drawPile := [{ id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }]
  discardPile := []
  exhaustPile := [{ id := 9, name := Shiv, cost := 0, damage := 4 },
                  { id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 },
                  { id := 5, name := Shiv, cost := 0, damage := 4 },
                  { id := 4, name := Shiv, cost := 0, damage := 4 }]
  inUse := []
  actionQueue := []
  energy := 7
  damage := 24
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

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

theorem loop_ok :
    execute cardDB stateA loopTrace = some stateB := by
  native_decide

theorem no_end : noEndTurn loopTrace = true := by native_decide
theorem same_mod : sameModAccum stateA stateB = true := by native_decide
theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

theorem ComboStormOfSteel_infinite : InfiniteCombo cardDB cards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, no_end, same_mod, dealt_dmg⟩

end ComboStormOfSteel
