/-
  Acrobatics+ x2 + Tactician+ + Reflex+ + Backflip+ x2 + Neutralize+ +
  After Image + Adrenaline+ + Caltrops+ + Escape Plan+ + Grand Finale+ (12 cards)

  4 damage per loop (Neutralize+ 4 dmg).

  Engine v2: CardInstance system.
  Setup exhausts Adrenaline+ and Grand Finale+ (60 dmg).
  Loop cycles Acrobatics draws with Tactician energy and Reflex draw triggers.
  Discarding Tactician/Reflex fires triggers automatically via fireOnDiscard.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboAcrobaticsTactician

def cards : List (CardName × Nat) := [
  (AcrobaticsPlus, 2), (TacticianPlus, 1), (ReflexPlus, 1),
  (BackflipPlus, 2), (NeutralizePlus, 1), (AfterImage, 1),
  (AdrenalinePlus, 1), (CaltropPlus, 1), (EscapePlanPlus, 1),
  (GrandFinalePlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- Card instance IDs (assigned by mkInitialState):
-- 0 = Acrobatics+#1, 1 = Acrobatics+#2, 2 = Tactician+, 3 = Reflex+,
-- 4 = Backflip+#1, 5 = Backflip+#2, 6 = Neutralize+, 7 = After Image,
-- 8 = Adrenaline+, 9 = Caltrops+, 10 = Escape Plan+, 11 = Grand Finale+

def setupTrace : List Action := [
  .draw 8, .draw 7, .draw 9, .draw 6, .draw 0,
  .play 8,                          -- Adrenaline+: +2E, draw 2, exhaust
  .draw 11, .draw 1,               -- draw GF, Acro#2
  .play 7,                          -- After Image (power, cost 1)
  .play 9,                          -- Caltrops+ (power, cost 1)
  .play 6,                          -- Neutralize+: 4 dmg, +2 weak (cost 0)
  .play 0,                          -- Acrobatics+#1: draw 4, discard 1 (cost 1)
  .draw 2, .draw 3, .draw 4, .draw 5,
  .discard 2,                       -- discard Tactician+ -> +2E
  .play 1,                          -- Acrobatics+#2: draw 4, discard 1 (cost 1)
  .draw 10, .draw 6, .draw 0, .draw 2,
  .discard 3,                       -- discard Reflex+ -> draw 3
  .draw 3, .failDraw,             -- draw Reflex, fail rest
  .play 11                          -- Grand Finale+: 60 dmg, exhaust (draw pile empty)
]

-- Loop: cycle Acrobatics with Tact/Reflex triggers for energy/draws
def loopTrace : List Action := [
  .play 6,                          -- Neutralize+: 4 dmg, +2 weak
  .play 10,                         -- Escape Plan+: draw 1
  .draw 1,                          -- draw Acro#2 (shuffle discard)
  .play 0,                          -- Acro#1: draw 4, discard 1
  .draw 6, .draw 10, .failDraw,   -- draw Neut, EscPlan, fail rest
  .discard 2,                       -- discard Tactician+ -> +2E
  .play 1,                          -- Acro#2: draw 4, discard 1
  .draw 2, .draw 0, .failDraw,    -- draw Tact, Acro#1, fail rest
  .discard 3,                       -- discard Reflex+ -> draw 3
  .draw 3, .failDraw              -- draw Reflex, fail rest
]

-- #eval execute cardDB (mkInitialState cardDB cards enemy) setupTrace
-- #eval execute cardDB (mkInitialState cardDB cards enemy) (setupTrace ++ loopTrace)

def stateA : GameState := {
  hand := [{ id := 3, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 2, name := TacticianPlus, cost := 0, damage := 0 },
           { id := 0, name := AcrobaticsPlus, cost := 1, damage := 0 },
           { id := 6, name := NeutralizePlus, cost := 0, damage := 4 },
           { id := 10, name := EscapePlanPlus, cost := 0, damage := 0 },
           { id := 5, name := BackflipPlus, cost := 1, damage := 0 },
           { id := 4, name := BackflipPlus, cost := 1, damage := 0 }]
  drawPile := []
  discardPile := [{ id := 1, name := AcrobaticsPlus, cost := 1, damage := 0 }]
  exhaustPile := [{ id := 11, name := GrandFinalePlus, cost := 0, damage := 60 },
                  { id := 8, name := AdrenalinePlus, cost := 0, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 64
  block := 6
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12
  noDraw := false
  corruptionActive := false
}

def stateB : GameState := {
  hand := [{ id := 3, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 0, name := AcrobaticsPlus, cost := 1, damage := 0 },
           { id := 2, name := TacticianPlus, cost := 0, damage := 0 },
           { id := 10, name := EscapePlanPlus, cost := 0, damage := 0 },
           { id := 6, name := NeutralizePlus, cost := 0, damage := 4 },
           { id := 5, name := BackflipPlus, cost := 1, damage := 0 },
           { id := 4, name := BackflipPlus, cost := 1, damage := 0 }]
  drawPile := []
  discardPile := [{ id := 1, name := AcrobaticsPlus, cost := 1, damage := 0 }]
  exhaustPile := [{ id := 11, name := GrandFinalePlus, cost := 0, damage := 60 },
                  { id := 8, name := AdrenalinePlus, cost := 0, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 68
  block := 10
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
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

theorem same_mod : sameModAccum stateA stateB = true := by native_decide
theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

theorem ComboAcrobaticsTactician_infinite : InfiniteCombo cardDB cards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboAcrobaticsTactician
