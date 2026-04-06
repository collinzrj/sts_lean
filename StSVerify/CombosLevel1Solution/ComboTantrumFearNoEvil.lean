/-
  观者 - 发泄+不惧妖邪双输出无限
  Cards: 11
-/

import StSVerify.CombosSpecL1.ComboTantrumFearNoEvil

open CardName Action

namespace ComboTantrumFearNoEvil_L1

-- ============================================================
-- FRAMEWORK-GENERATED (DO NOT MODIFY)
-- ============================================================



-- ============================================================
-- LLM FILLS IN BELOW
-- ============================================================

/-
  Strategy:
  Turn 1: Draw 3 powers + Tantrum + FNE. Play 3 powers. End turn.
  Turn 2: Draw DEM (triggers: +2 Miracles ids 11,12, exhaust DEM).
    Draw Vault+, Scrawl, FNE#2, Flurry#1.
    Play Miracles for energy. Exhaust Vault+ and Scrawl.
    Play FNE#1 (Neutral->Calm), Flurry#1, Flurry#2.
    Keep Tantrum+ and FNE#2 in hand.

  Loop: Tantrum+ (Calm->Wrath, +2E, Flurry auto 24 dmg, resolveCard shuffles Tant
    to drawPile, then Rushdown 4 draws: draw Tant back + 3 from disc).
    FNE (Wrath->Calm, 22 dmg). Flurry x2.
    70 damage per loop.
-/

def setupTrace : List Action := [
  -- Turn 1: play 3 powers
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0, .play 1, .play 2,
  .endTurn,
  -- Turn 2: exhaust DEM, Vault+, Scrawl; set up loop
  .draw 10,
  .resolveDrawTrigger 10,
  .draw 9, .draw 8, .draw 5, .draw 6,
  .play 11, .play 12,             -- Miracles (+2E)
  .play 9,                        -- Vault+ (exhaust)
  .play 8,                        -- Scrawl (exhaust, draw to full)
  .draw 7, .draw 3, .draw 4,
  .failDraw,
  .play 4,                        -- FNE#1 (Neutral->Calm, 11 dmg, MF +6 blk)
  .play 6,                        -- Flurry (Calm, 6 dmg)
  .play 7                         -- Flurry (Calm, 6 dmg)
]

def loopTrace : List Action := [
  .play 3,                        -- Tantrum+ (Calm->Wrath, +2E, 12 dmg, Flurry auto 24 dmg)
  .draw 3,                        -- draw Tantrum back (resolveCard fires first via autoDrain)
  .draw 4, .draw 6, .draw 7,     -- draw 3 from shuffled disc
  .play 4,                        -- FNE (Wrath->Calm, 22 dmg, MF +6 blk)
  .play 6,                        -- Flurry (Calm, 6 dmg)
  .play 7                         -- Flurry (Calm, 6 dmg)
]

def stateA : GameState := {
  hand := [ { id := 3, name := TantrumPlus, cost := 1, damage := 12 }
           , { id := 5, name := FearNoEvilPlus, cost := 1, damage := 11 } ]
  drawPile := []
  discardPile := [ { id := 7, name := FlurryOfBlowsPlus, cost := 0, damage := 6 }
                 , { id := 6, name := FlurryOfBlowsPlus, cost := 0, damage := 6 }
                 , { id := 4, name := FearNoEvilPlus, cost := 1, damage := 11 } ]
  exhaustPile := [ { id := 8, name := Scrawl, cost := 1, damage := 0 }
                 , { id := 9, name := VaultPlus, cost := 2, damage := 0 }
                 , { id := 12, name := Miracle, cost := 0, damage := 0 }
                 , { id := 11, name := Miracle, cost := 0, damage := 0 }
                 , { id := 10, name := DeusExMachina, cost := 0, damage := 0 } ]
  inUse := []
  actionQueue := []
  energy := 1
  damage := 23
  block := 6
  stance := .Calm
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 13
  noDraw := false
  corruptionActive := false
}

def stateB : GameState := {
  hand := [ { id := 3, name := TantrumPlus, cost := 1, damage := 12 }
           , { id := 5, name := FearNoEvilPlus, cost := 1, damage := 11 } ]
  drawPile := []
  discardPile := [ { id := 7, name := FlurryOfBlowsPlus, cost := 0, damage := 6 }
                 , { id := 6, name := FlurryOfBlowsPlus, cost := 0, damage := 6 }
                 , { id := 4, name := FearNoEvilPlus, cost := 1, damage := 11 } ]
  exhaustPile := [ { id := 8, name := Scrawl, cost := 1, damage := 0 }
                 , { id := 9, name := VaultPlus, cost := 2, damage := 0 }
                 , { id := 12, name := Miracle, cost := 0, damage := 0 }
                 , { id := 11, name := Miracle, cost := 0, damage := 0 }
                 , { id := 10, name := DeusExMachina, cost := 0, damage := 0 } ]
  inUse := []
  actionQueue := []
  energy := 1
  damage := 93
  block := 18
  stance := .Calm
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 13
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

theorem ComboTantrumFearNoEvil_infinite : InfiniteCombo cardDB cards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, no_end, same_mod, dealt_dmg⟩

theorem proof : InfiniteCombo cardDB cards enemy := ComboTantrumFearNoEvil_infinite

end ComboTantrumFearNoEvil_L1
