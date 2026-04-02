/-
  Storm of Steel+ + Tactician+ + Reflex+ + Prepared+ + Strike (Silent)
  22 damage per loop (4 Shivs x 4 + Strike 6)

  Engine v2: CardInstance system, no token bags.
  Storm creates Shiv CardInstances dynamically via nextId.
  autoDrain discards hand R-to-L, fires Tactician (+2E) and Reflex (draw 3).
  Strike absorbs the extra energy (Storm -1E + Tact +2E - Strike 1E = net 0).
  endTurn resets energy to 3 each loop.

  NOTE on Level 2: This combo is NOT L2-provable. The adversary can place Prepared+
  at position 4 or 5 in the first shuffled pile (5 cards, only 3 drawn by Reflex+
  trigger), preventing the player from drawing the remaining 2 cards.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboStormStrike_Solution

def cards : List (CardName × Nat) := [
  (StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1),
  (PreparedPlus, 1), (StrikeSilent, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- Card instance IDs:
-- 0 = Storm of Steel+, 1 = Tactician+, 2 = Reflex+, 3 = Prepared+, 4 = Strike

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0,                          -- Storm: 4 hand cards -> 4 Shivs(5,6,7,8), Tact+2E, Reflex draw 3
  .draw 3, .draw 4, .draw 1,       -- draw 3 from shuffled discard
  .play 5, .play 6, .play 7, .play 8, -- play 4 Shivs (16 dmg)
  .play 4,                          -- Strike: 6 dmg, cost 1
  .play 3,                          -- Prep: draw 2, discard 1
  .draw 2, .draw 0,                -- draw Reflex, SoS from shuffled discard
  .discard 2,                       -- discard Reflex (trigger: draw 3)
  .draw 4, .draw 2, .failDraw,    -- draw Strike, Reflex from shuffled, fail 3rd
  .endTurn,
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4
]

def loopTrace : List Action := [
  .play 0,                          -- Storm: 4 hand cards -> 4 Shivs, Tact+2E, Reflex draw 3
  .draw 3, .draw 4, .draw 1,       -- draw 3 from shuffled discard
  .play 9, .play 10, .play 11, .play 12, -- play 4 Shivs
  .play 4,                          -- Strike: 6 dmg, cost 1
  .play 3,                          -- Prep: draw 2, discard 1
  .draw 2, .draw 0,
  .discard 2,                       -- discard Reflex (trigger: draw 3)
  .draw 4, .draw 2, .failDraw,
  .endTurn,
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4
]

-- #eval execute cardDB (mkInitialState cardDB cards enemy) setupTrace
-- #eval execute cardDB (mkInitialState cardDB cards enemy) (setupTrace ++ loopTrace)

def stateA : GameState := {
  hand := [{ id := 4, name := StrikeSilent, cost := 1, damage := 6 },
           { id := 3, name := PreparedPlus, cost := 0, damage := 0 },
           { id := 2, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 1, name := TacticianPlus, cost := 0, damage := 0 },
           { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }]
  drawPile := []
  discardPile := []
  exhaustPile := [{ id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 },
                  { id := 5, name := Shiv, cost := 0, damage := 4 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 22
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := []
  nextId := 9
  noDraw := false
  corruptionActive := false
}

def stateB : GameState := {
  hand := [{ id := 4, name := StrikeSilent, cost := 1, damage := 6 },
           { id := 3, name := PreparedPlus, cost := 0, damage := 0 },
           { id := 2, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 1, name := TacticianPlus, cost := 0, damage := 0 },
           { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }]
  drawPile := []
  discardPile := []
  exhaustPile := [{ id := 12, name := Shiv, cost := 0, damage := 4 },
                  { id := 11, name := Shiv, cost := 0, damage := 4 },
                  { id := 10, name := Shiv, cost := 0, damage := 4 },
                  { id := 9, name := Shiv, cost := 0, damage := 4 },
                  { id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 },
                  { id := 5, name := Shiv, cost := 0, damage := 4 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 44
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := []
  nextId := 13
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

theorem is_infinite : InfiniteCombo cardDB cards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboStormStrike_Solution
