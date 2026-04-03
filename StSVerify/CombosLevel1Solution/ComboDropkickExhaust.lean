/-
  铁甲战士 - 飞踢消耗精简无限 (Ironclad Dropkick Exhaust Infinite)
  Cards: 11
  v2 engine rewrite
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboDropkickExhaust

-- ============================================================
-- Deck definition
-- IDs: Bash+=0, DK1=1, DK2=2, TG1=3, TG2=4, BP=5, SIO+=6, Off+=7, Pur=8, BC+=9, PS+=10
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(BashPlus, 1), (Dropkick, 2), (TrueGritPlus, 2), (BurningPactPlus, 1),
   (ShrugItOffPlus, 1), (OfferingPlus, 1), (Purity, 1), (BattleCryPlus, 1),
   (PommelStrikePlus, 1)]

def enemy : EnemyState := { vulnerable := 3, weak := 0, intending := false }

-- ============================================================
-- Traces
-- ============================================================

def setupTrace : List Action := [
  -- Turn 1: exhaust junk cards
  .draw 8, .draw 7, .draw 5, .draw 6, .draw 10,
  .play 8,                        -- Purity: exhaust self + exhaust 3 from hand
  .exhaust 5, .exhaust 6, .exhaust 10,
  .play 7,                        -- Offering+: +2E, draw 5, exhaust self
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 3, .exhaust 4,           -- TrueGrit+#1: +9blk, exhaust TG#2
  .play 1,                        -- Dropkick#1: 7dmg (vuln), +1E, +1draw
  .draw 9,                        -- draw BattleCry+
  .play 9,                        -- BattleCry+: exhaust self
  .endTurn,
  -- Turn 2: establish loop state
  .draw 0, .draw 1, .draw 3, .draw 2,
  .failDraw,                       -- only 4 cards in deck
  .play 0,                        -- Bash+: 15dmg (vuln), +3 vuln
  .play 1,                        -- Dropkick#1: 7dmg, +1E, +1draw
  .draw 0,                        -- shuffle discard -> draw, draw Bash+
  .play 2,                        -- Dropkick#2: 7dmg, +1E, +1draw
  .draw 1                         -- draw DK#1
]

def stateA : GameState := {
  hand := [{ id := 1, name := Dropkick, cost := 1, damage := 5 },
           { id := 0, name := BashPlus, cost := 2, damage := 10 },
           { id := 3, name := TrueGritPlus, cost := 1, damage := 0 }]
  drawPile := []
  discardPile := [{ id := 2, name := Dropkick, cost := 1, damage := 5 }]
  exhaustPile := [{ id := 9, name := BattleCryPlus, cost := 0, damage := 0 },
                  { id := 4, name := TrueGritPlus, cost := 1, damage := 0 },
                  { id := 7, name := OfferingPlus, cost := 0, damage := 0 },
                  { id := 8, name := Purity, cost := 0, damage := 0 },
                  { id := 10, name := PommelStrikePlus, cost := 1, damage := 10 },
                  { id := 6, name := ShrugItOffPlus, cost := 1, damage := 0 },
                  { id := 5, name := BurningPactPlus, cost := 1, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 1
  damage := 36
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 6, weak := 0, intending := false }
  activePowers := []
  nextId := 11
  noDraw := false
  corruptionActive := false
}

def loopTrace : List Action := [
  .play 1,                        -- DK#1: 7dmg, +1E, +1draw
  .draw 2,                        -- shuffle DK#2 -> draw, draw DK#2
  .play 2,                        -- DK#2: 7dmg, +1E, +1draw
  .draw 1                         -- shuffle DK#1 -> draw, draw DK#1
]

def stateB : GameState := {
  hand := [{ id := 1, name := Dropkick, cost := 1, damage := 5 },
           { id := 0, name := BashPlus, cost := 2, damage := 10 },
           { id := 3, name := TrueGritPlus, cost := 1, damage := 0 }]
  drawPile := []
  discardPile := [{ id := 2, name := Dropkick, cost := 1, damage := 5 }]
  exhaustPile := [{ id := 9, name := BattleCryPlus, cost := 0, damage := 0 },
                  { id := 4, name := TrueGritPlus, cost := 1, damage := 0 },
                  { id := 7, name := OfferingPlus, cost := 0, damage := 0 },
                  { id := 8, name := Purity, cost := 0, damage := 0 },
                  { id := 10, name := PommelStrikePlus, cost := 1, damage := 10 },
                  { id := 6, name := ShrugItOffPlus, cost := 1, damage := 0 },
                  { id := 5, name := BurningPactPlus, cost := 1, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 1
  damage := 50
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 6, weak := 0, intending := false }
  activePowers := []
  nextId := 11
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

theorem no_end : noEndTurn loopTrace = true := by native_decide
theorem same_mod : sameModAccum stateA stateB = true := by native_decide
theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

theorem ComboDropkickExhaust_infinite : InfiniteCombo cardDB allCards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, no_end, same_mod, dealt_dmg⟩

end ComboDropkickExhaust
