/-
  观者 - 真言/神格混合无限
  Cards: 13
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboMantraDivine

-- ============================================================
-- FRAMEWORK-GENERATED (DO NOT MODIFY)
-- ============================================================

def cards : List (CardName × Nat) :=
  [ (Rushdown, 2)             -- ids 0,1
  , (MentalFortressPlus, 1)   -- id 2
  , (EruptionPlus, 1)         -- id 3
  , (InnerPeace, 1)           -- id 4
  , (PrayPlus, 1)             -- id 5
  , (ProstatePlus, 1)         -- id 6
  , (EmptyMindPlus, 1)        -- id 7
  , (FlurryOfBlowsPlus, 1)    -- id 8
  , (Scrawl, 1)               -- id 9
  , (VaultPlus, 1)            -- id 10
  , (DeusExMachina, 1)        -- id 11
  , (OmnisciencePlus, 1)      -- id 12
  ]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- ============================================================
-- LLM FILLS IN BELOW
-- ============================================================

/-
  Strategy:
  Turn 1: Draw Scrawl, Rushdown x2, Vault+, Deus Ex Machina.
    Resolve DEM draw trigger (add 2 Miracles ids 13,14, exhaust DEM).
    Play Miracles for +2 energy (total 5).
    Play 2 Rushdowns, Scrawl (draw to full, exhaust).
    Draw all remaining cards. Play MF+.
    Recycle exhaust: Pray+, EmptyMind+, Prostrate+, Omniscience+, Vault+.
    Play Inner Peace (enter Calm). Play Flurry.

  Loop: Eruption+ (Calm→Wrath, Rushdown draws, Flurry auto).
    Draw cards, play Flurry (Wrath), Inner Peace (→Calm), Flurry auto.
    39 damage per loop.
-/

def setupTrace : List Action := [
  .draw 9, .draw 0, .draw 1, .draw 10, .draw 11,
  .resolveDrawTrigger 11,
  .play 13, .play 14,
  .play 0, .play 1,
  .play 9,
  .draw 2, .draw 3, .draw 4, .draw 5,
  .draw 6, .draw 7, .draw 8, .draw 12,
  .failDraw,
  .play 2,
  .recycleChoose 5, .recycleChoose 7, .recycleChoose 6,
  .recycleChoose 12, .recycleChoose 10,
  .play 4,
  .play 8
]

def loopTrace : List Action := [
  .play 3,
  .resolveRushdown,
  .autoPlayFlurry 8,
  .draw 4, .draw 3, .draw 8,
  .failDraw,
  .play 8,
  .play 4,
  .autoPlayFlurry 8
]

def stateA : GameState := {
  hand := [ { id := 3, name := EruptionPlus, cost := 1, damage := 9 } ]
  drawPile := []
  discardPile := [ { id := 8, name := FlurryOfBlowsPlus, cost := 0, damage := 6 }
                 , { id := 4, name := InnerPeace, cost := 1, damage := 0 } ]
  exhaustPile := [ { id := 10, name := VaultPlus, cost := 2, damage := 0 }
                 , { id := 12, name := OmnisciencePlus, cost := 3, damage := 0 }
                 , { id := 6, name := ProstatePlus, cost := 0, damage := 0 }
                 , { id := 7, name := EmptyMindPlus, cost := 1, damage := 0 }
                 , { id := 5, name := PrayPlus, cost := 1, damage := 0 }
                 , { id := 9, name := Scrawl, cost := 1, damage := 0 }
                 , { id := 14, name := Miracle, cost := 0, damage := 0 }
                 , { id := 13, name := Miracle, cost := 0, damage := 0 }
                 , { id := 11, name := DeusExMachina, cost := 0, damage := 0 } ]
  inUse := []
  actionQueue := []
  energy := 7
  damage := 6
  block := 6
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
  hand := [ { id := 3, name := EruptionPlus, cost := 1, damage := 9 } ]
  drawPile := []
  discardPile := [ { id := 4, name := InnerPeace, cost := 1, damage := 0 }
                 , { id := 8, name := FlurryOfBlowsPlus, cost := 0, damage := 6 } ]
  exhaustPile := [ { id := 10, name := VaultPlus, cost := 2, damage := 0 }
                 , { id := 12, name := OmnisciencePlus, cost := 3, damage := 0 }
                 , { id := 6, name := ProstatePlus, cost := 0, damage := 0 }
                 , { id := 7, name := EmptyMindPlus, cost := 1, damage := 0 }
                 , { id := 5, name := PrayPlus, cost := 1, damage := 0 }
                 , { id := 9, name := Scrawl, cost := 1, damage := 0 }
                 , { id := 14, name := Miracle, cost := 0, damage := 0 }
                 , { id := 13, name := Miracle, cost := 0, damage := 0 }
                 , { id := 11, name := DeusExMachina, cost := 0, damage := 0 } ]
  inUse := []
  actionQueue := []
  energy := 7
  damage := 45
  block := 18
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

end ComboMantraDivine
