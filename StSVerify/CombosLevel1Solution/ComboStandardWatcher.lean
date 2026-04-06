/-
  观者 - 标准沙雕无限
  Cards: 12
-/

import StSVerify.CombosSpecL1.ComboStandardWatcher

open CardName Action

namespace ComboStandardWatcher_L1

-- ============================================================
-- FRAMEWORK-GENERATED (DO NOT MODIFY)
-- ============================================================



-- ============================================================
-- LLM FILLS IN BELOW
-- ============================================================

/-
  Strategy (v2 engine):
  Turn 1: Draw DEM + 3 powers + InnerPeace+.
    Resolve DEM draw trigger (add 2 Miracles ids 12,13, exhaust DEM).
    Play powers (Rushdown x2, MF+). Play Miracles for +2 energy.
    Play InnerPeace+ to enter Calm.
  Turn 2: Draw Tantrum+, FNE, TtTH, Vault+, Scrawl.
    Play Tantrum+ (Calm->Wrath, auto Rushdown draws + Flurry auto damage).
    Draw from Rushdown: Eruption+, Flurry+, then shuffle disc for Tantrum+, IP+.
    Play TtTH (exhaust), Vault+ (exhaust), Scrawl (exhaust, draw to full, piles empty).
    End turn.
  Turn 3: Draw all 5 cards from disc.
    Play FNE (Wrath->Calm), Eruption+ (Calm->Wrath, Rushdown draws).
    Draw FNE and Eruption+ back. Play Flurry+ (Wrath), InnerPeace+ (Wrath->Calm).

  Loop: Tantrum+(Calm->Wrath), 4 Rushdown draws, FNE(Wrath->Calm),
    Eruption+(Calm->Wrath), 4 Rushdown draws, Flurry+(Wrath), IP+(Wrath->Calm).
    73 damage per loop.
-/

def setupTrace : List Action := [
  -- Turn 1: play powers
  .draw 10, .resolveDrawTrigger 10,
  .draw 0, .draw 1, .draw 2, .draw 5,
  .play 0, .play 1, .play 2,
  .play 12, .play 13,
  .play 5,
  .endTurn,
  -- Turn 2: Tantrum -> Rushdown draws -> exhaust utilities
  .draw 4, .draw 6, .draw 11, .draw 9, .draw 8,
  .play 4,
  .draw 3, .draw 7, .draw 4, .draw 5,
  .play 11, .play 9, .play 8,
  .failDraw,
  .endTurn,
  -- Turn 3: cycle stances to set up loop
  .draw 5, .draw 4, .draw 7, .draw 3, .draw 6,
  .play 6, .play 3,
  .draw 6, .draw 3,
  .failDraw,
  .play 7, .play 5
]

def loopTrace : List Action := [
  .play 4,                      -- Tantrum+: Calm->Wrath, Rushdown 4 draws, Flurry auto 12 dmg
  .draw 4, .draw 5, .draw 7,
  .failDraw,                    -- 4th draw fails
  .play 6,                      -- FNE: Wrath->Calm
  .play 3,                      -- Eruption+: Calm->Wrath, Rushdown 4 draws
  .draw 3, .draw 6,
  .failDraw,                    -- remaining draws fail
  .play 7,                      -- Flurry: Wrath
  .play 5                       -- InnerPeace+: Wrath->Calm
]

def stateA : GameState := {
  hand := [ { id := 3, name := EruptionPlus, cost := 1, damage := 9 }
           , { id := 6, name := FearNoEvilPlus, cost := 1, damage := 11 }
           , { id := 4, name := TantrumPlus, cost := 1, damage := 12 } ]
  drawPile := []
  discardPile := [ { id := 5, name := InnerPeacePlus, cost := 1, damage := 0 }
                 , { id := 7, name := FlurryOfBlowsPlus, cost := 0, damage := 6 } ]
  exhaustPile := [ { id := 8, name := Scrawl, cost := 1, damage := 0 }
                 , { id := 9, name := VaultPlus, cost := 2, damage := 0 }
                 , { id := 11, name := TalkToTheHandPlus, cost := 1, damage := 7 }
                 , { id := 13, name := Miracle, cost := 0, damage := 0 }
                 , { id := 12, name := Miracle, cost := 0, damage := 0 }
                 , { id := 10, name := DeusExMachina, cost := 0, damage := 0 } ]
  inUse := []
  actionQueue := []
  energy := 2
  damage := 75
  block := 18
  stance := .Calm
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14
  noDraw := false
  corruptionActive := false
}

def stateB : GameState := {
  hand := [ { id := 6, name := FearNoEvilPlus, cost := 1, damage := 11 }
           , { id := 3, name := EruptionPlus, cost := 1, damage := 9 }
           , { id := 4, name := TantrumPlus, cost := 1, damage := 12 } ]
  drawPile := []
  discardPile := [ { id := 5, name := InnerPeacePlus, cost := 1, damage := 0 }
                 , { id := 7, name := FlurryOfBlowsPlus, cost := 0, damage := 6 } ]
  exhaustPile := [ { id := 8, name := Scrawl, cost := 1, damage := 0 }
                 , { id := 9, name := VaultPlus, cost := 2, damage := 0 }
                 , { id := 11, name := TalkToTheHandPlus, cost := 1, damage := 7 }
                 , { id := 13, name := Miracle, cost := 0, damage := 0 }
                 , { id := 12, name := Miracle, cost := 0, damage := 0 }
                 , { id := 10, name := DeusExMachina, cost := 0, damage := 0 } ]
  inUse := []
  actionQueue := []
  energy := 2
  damage := 148
  block := 42
  stance := .Calm
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14
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

theorem ComboStandardWatcher_infinite : InfiniteCombo cardDB cards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, no_end, same_mod, dealt_dmg⟩

theorem proof : InfiniteCombo cardDB cards enemy := ComboStandardWatcher_infinite

end ComboStandardWatcher_L1
