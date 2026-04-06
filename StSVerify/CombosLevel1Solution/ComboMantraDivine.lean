/-
  观者 - 真言/神格混合无限
  Cards: 13
-/

import StSVerify.CombosSpecL1.ComboMantraDivine

open CardName Action

namespace ComboMantraDivine_L1

-- ============================================================
-- FRAMEWORK-GENERATED (DO NOT MODIFY)
-- ============================================================



-- ============================================================
-- LLM FILLS IN BELOW
-- ============================================================

/-
  Strategy (v2 engine):
  Turn 1: Draw DEM + powers + Scrawl.
    Resolve DEM draw trigger (add 2 Miracles ids 13,14, exhaust DEM).
    Play Miracles, 3 powers, Scrawl (draw all remaining, exhaust).
    Play Flurry, Prostrate, InnerPeace (enter Calm). End turn.
  Turn 2: Draw 5, play InnerPeace (draw 3 from Calm).
    Cycle: Flurry+Prostrate, EmptyMind(Calm->Neutral, draw 3), InnerPeace(->Calm).
    Reach loop state with hand=[Erupt, Vault, Omni, Pray].

  Loop: Eruption+(Calm->Wrath, auto Rushdown draws + Flurry auto).
    Draw 4 from disc. Play Flurry(Wrath), IP(Wrath->Calm),
    EmptyMind(Calm->Neutral, draw 3), IP(Neutral->Calm),
    Flurry(Calm), Prostrate. 51 damage per loop.
-/

def setupTrace : List Action := [
  -- Turn 1
  .draw 9, .draw 0, .draw 1, .draw 2, .draw 11,
  .resolveDrawTrigger 11,
  .play 13, .play 14,
  .play 0, .play 1, .play 2,
  .play 9,
  .draw 3, .draw 4, .draw 5, .draw 6, .draw 7, .draw 8, .draw 10, .draw 12,
  .failDraw,
  .play 8, .play 6, .play 4,
  .endTurn,
  -- Turn 2
  .draw 3, .draw 4, .draw 5, .draw 10, .draw 12,
  .play 4,
  .draw 6, .draw 8, .draw 7,
  .play 8, .play 6,
  .play 7,
  .draw 4, .draw 8, .draw 6,
  .play 4, .play 8, .play 6
]

def loopTrace : List Action := [
  .play 3,                         -- Eruption+ (Calm->Wrath, auto Rushdown + Flurry)
  .draw 8, .draw 4, .draw 7, .draw 6,
  .play 8,                         -- Flurry+ (Wrath)
  .play 4,                         -- InnerPeace (Wrath->Calm)
  .play 7,                         -- EmptyMind+ (Calm->Neutral, draw 3)
  .draw 3, .draw 4, .draw 8,
  .play 4,                         -- InnerPeace (Neutral->Calm)
  .play 8,                         -- Flurry+ (Calm)
  .play 6                          -- Prostrate+ (free)
]

def stateA : GameState := {
  hand := [ { id := 12, name := OmnisciencePlus, cost := 3, damage := 0 }
           , { id := 10, name := VaultPlus, cost := 2, damage := 0 }
           , { id := 5, name := PrayPlus, cost := 1, damage := 0 }
           , { id := 3, name := EruptionPlus, cost := 1, damage := 9 } ]
  drawPile := []
  discardPile := [ { id := 6, name := ProstatePlus, cost := 0, damage := 0 }
                 , { id := 8, name := FlurryOfBlowsPlus, cost := 0, damage := 6 }
                 , { id := 4, name := InnerPeace, cost := 1, damage := 0 }
                 , { id := 7, name := EmptyMindPlus, cost := 1, damage := 0 } ]
  exhaustPile := [ { id := 9, name := Scrawl, cost := 1, damage := 0 }
                 , { id := 14, name := Miracle, cost := 0, damage := 0 }
                 , { id := 13, name := Miracle, cost := 0, damage := 0 }
                 , { id := 11, name := DeusExMachina, cost := 0, damage := 0 } ]
  inUse := []
  actionQueue := []
  energy := 2
  damage := 30
  block := 22
  stance := .Calm
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 15
  noDraw := false
  corruptionActive := false
}

def stateB : GameState := {
  hand := [ { id := 3, name := EruptionPlus, cost := 1, damage := 9 }
           , { id := 12, name := OmnisciencePlus, cost := 3, damage := 0 }
           , { id := 10, name := VaultPlus, cost := 2, damage := 0 }
           , { id := 5, name := PrayPlus, cost := 1, damage := 0 } ]
  drawPile := []
  discardPile := [ { id := 6, name := ProstatePlus, cost := 0, damage := 0 }
                 , { id := 8, name := FlurryOfBlowsPlus, cost := 0, damage := 6 }
                 , { id := 4, name := InnerPeace, cost := 1, damage := 0 }
                 , { id := 7, name := EmptyMindPlus, cost := 1, damage := 0 } ]
  exhaustPile := [ { id := 9, name := Scrawl, cost := 1, damage := 0 }
                 , { id := 14, name := Miracle, cost := 0, damage := 0 }
                 , { id := 13, name := Miracle, cost := 0, damage := 0 }
                 , { id := 11, name := DeusExMachina, cost := 0, damage := 0 } ]
  inUse := []
  actionQueue := []
  energy := 2
  damage := 81
  block := 51
  stance := .Calm
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 15
  noDraw := false
  corruptionActive := false
}

-- ============================================================
-- VERIFICATION (automatic)
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

theorem loop_ok :
    execute cardDB stateA loopTrace = some stateB := by
  native_decide

theorem no_end : noEndTurn loopTrace = true := by native_decide
theorem same_mod : sameModAccum stateA stateB = true := by native_decide
theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

theorem ComboMantraDivine_infinite : InfiniteCombo cardDB cards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, no_end, same_mod, dealt_dmg⟩

theorem proof : InfiniteCombo cardDB cards enemy := ComboMantraDivine_infinite

end ComboMantraDivine_L1
