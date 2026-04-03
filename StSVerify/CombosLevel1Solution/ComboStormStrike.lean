/-
  Storm of Steel+ + Tactician+ + Reflex+ + Prepared+ + Strike Silent (5 cards)
  12 damage per loop (3 Shivs x 4 damage)

  Engine v2: CardInstance system, no token bags.
  Storm creates Shiv CardInstances dynamically via nextId.
  autoDrain discards hand R-to-L, fires Tactician (+2E) and Reflex (draw 3).

  Single-turn loop (no endTurn):
  Strike stays in drawPile throughout the loop. It gets drawn during Prep but
  discarding Reflex+Tact recycles the engine. SoS discards Strike+Prep from hand
  (creating 3 Shivs since Tact+Reflex already discarded). Strike never needs to be played.

  Play Prep -> draw 2 (Strike + SoS from shuffle) -> discard Reflex+Tact -> +2E + draw 3
  -> draw Tact+Reflex from shuffle -> play SoS -> discard 3 -> 3 Shivs + triggers
  -> draw 3 (Prep+Reflex+Tact) -> play 3 Shivs -> back to stateA
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

-- Setup: draw all 5, play SoS, draw 3, play 4 Shivs
def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0,                          -- Storm: discard 4, Tact+2E, Reflex draw 3, 4 Shivs(5,6,7,8)
  .draw 1, .draw 2, .draw 3,       -- draw Tact, Reflex, Prep from shuffled discard
  .play 5, .play 6, .play 7, .play 8  -- play 4 Shivs (16 dmg)
]

-- Loop: single-turn, no endTurn
def loopTrace : List Action := [
  .play 3,                          -- Prepared+: draw 2, discard 2
  .draw 4, .draw 0,                -- draw Strike(4) from drawPile, shuffle {SoS(0)}, draw SoS(0)
  .discard 2,                       -- discard Reflex (trigger: draw 3)
  .discard 1,                       -- discard Tact (trigger: +2E)
  .draw 1, .draw 2, .failDraw,    -- draw Tact, Reflex from shuffled discard {Tact,Reflex}, fail 3rd
  .play 0,                          -- SoS: discard 3 hand cards (Strike,Prep), 3 Shivs (9,10,11)
  .draw 3, .draw 2, .draw 1,       -- draw 3 from shuffled discard
  .play 9, .play 10, .play 11      -- play 3 Shivs (12 dmg)
]

def stateA : GameState := {
  hand := [{ id := 3, name := PreparedPlus, cost := 0, damage := 0 },
           { id := 2, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 1, name := TacticianPlus, cost := 0, damage := 0 }]
  drawPile := [{ id := 4, name := StrikeSilent, cost := 1, damage := 6 }]
  discardPile := [{ id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }]
  exhaustPile := [{ id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 },
                  { id := 5, name := Shiv, cost := 0, damage := 4 }]
  inUse := []
  actionQueue := []
  energy := 4
  damage := 16
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
  hand := [{ id := 1, name := TacticianPlus, cost := 0, damage := 0 },
           { id := 2, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 3, name := PreparedPlus, cost := 0, damage := 0 }]
  drawPile := [{ id := 4, name := StrikeSilent, cost := 1, damage := 6 }]
  discardPile := [{ id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }]
  exhaustPile := [{ id := 11, name := Shiv, cost := 0, damage := 4 },
                  { id := 10, name := Shiv, cost := 0, damage := 4 },
                  { id := 9, name := Shiv, cost := 0, damage := 4 },
                  { id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 },
                  { id := 5, name := Shiv, cost := 0, damage := 4 }]
  inUse := []
  actionQueue := []
  energy := 7
  damage := 28
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := []
  nextId := 12
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

theorem is_infinite : InfiniteCombo cardDB cards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, no_end, same_mod, dealt_dmg⟩

end ComboStormStrike_Solution
