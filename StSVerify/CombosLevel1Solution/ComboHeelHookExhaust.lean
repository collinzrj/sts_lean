/-
  静默猎手 - 足跟勾+消耗精简 (Silent Heel Hook+ Exhaust Infinite)
  Cards: 10
  v2 engine rewrite
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboHeelHookExhaust

-- ============================================================
-- Deck definition
-- IDs: HH1=0, HH2=1, N=2, Mal=3, PW=4, Adr=5, DDD=6, AI=7, EP=8, BF=9
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(HeelHookPlus, 2), (NeutralizePlus, 1), (MalaisePlus, 1), (PiercingWail, 1),
   (AdrenalinePlus, 1), (DieDieDiePlus, 1), (AfterImage, 1), (EscapePlanPlus, 1),
   (BackflipPlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 2, intending := false }

-- ============================================================
-- Traces
-- ============================================================

def setupTrace : List Action := [
  -- Turn 1: draw exhaust/power cards
  .draw 5, .draw 3, .draw 4, .draw 6, .draw 7,
  .play 3,                        -- Malaise+ (0E, exhaust self)
  .play 5,                        -- Adrenaline+ (0E, +2E, draw 2, exhaust self)
  .draw 8, .draw 9,
  .play 7,                        -- After Image (1E, power)
  .play 4,                        -- Piercing Wail (1E, exhaust self)
  .play 6,                        -- Die Die Die+ (1E, 17dmg, exhaust self)
  .play 8,                        -- Escape Plan+ (0E, draw 1)
  .draw 0,                        -- draw HH1
  .play 9,                        -- Backflip+ (1E, +8blk, draw 2)
  .draw 1, .draw 2,
  .endTurn,
  -- Turn 2
  .draw 0, .draw 1, .draw 2, .draw 8, .draw 9,
  .play 0,                        -- HH1: 8dmg, weak -> +1E, +1draw
  .failDraw                       -- piles empty; HH1 -> discard via resolveInUse
]

def stateA : GameState := {
  hand := [{ id := 9, name := BackflipPlus, cost := 1, damage := 0 },
           { id := 8, name := EscapePlanPlus, cost := 0, damage := 0 },
           { id := 2, name := NeutralizePlus, cost := 0, damage := 4 },
           { id := 1, name := HeelHookPlus, cost := 1, damage := 8 }]
  drawPile := []
  discardPile := [{ id := 0, name := HeelHookPlus, cost := 1, damage := 8 }]
  exhaustPile := [{ id := 6, name := DieDieDiePlus, cost := 1, damage := 17 },
                  { id := 4, name := PiercingWail, cost := 1, damage := 0 },
                  { id := 5, name := AdrenalinePlus, cost := 0, damage := 0 },
                  { id := 3, name := MalaisePlus, cost := 0, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 25
  block := 1
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := [AfterImage]
  nextId := 10
  noDraw := false
  corruptionActive := false
}

def loopTrace : List Action := [
  .play 1,                        -- HH2: 8dmg, +1E, +1draw
  .draw 0,                        -- shuffle HH1 -> draw, draw HH1
  .play 0,                        -- HH1: 8dmg, +1E, +1draw
  .draw 1                         -- shuffle HH2 -> draw, draw HH2
]

def stateB : GameState := {
  hand := [{ id := 1, name := HeelHookPlus, cost := 1, damage := 8 },
           { id := 9, name := BackflipPlus, cost := 1, damage := 0 },
           { id := 8, name := EscapePlanPlus, cost := 0, damage := 0 },
           { id := 2, name := NeutralizePlus, cost := 0, damage := 4 }]
  drawPile := []
  discardPile := [{ id := 0, name := HeelHookPlus, cost := 1, damage := 8 }]
  exhaustPile := [{ id := 6, name := DieDieDiePlus, cost := 1, damage := 17 },
                  { id := 4, name := PiercingWail, cost := 1, damage := 0 },
                  { id := 5, name := AdrenalinePlus, cost := 0, damage := 0 },
                  { id := 3, name := MalaisePlus, cost := 0, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 41
  block := 3
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := [AfterImage]
  nextId := 10
  noDraw := false
  corruptionActive := false
}

-- ============================================================
-- Verification
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB allCards enemy) setupTrace = some stateA := by
  native_decide

theorem loop_ok :
    execute cardDB stateA loopTrace = some stateB := by
  native_decide

theorem same_mod : sameModAccum stateA stateB = true := by native_decide
theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

theorem ComboHeelHookExhaust_infinite : InfiniteCombo cardDB allCards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboHeelHookExhaust
