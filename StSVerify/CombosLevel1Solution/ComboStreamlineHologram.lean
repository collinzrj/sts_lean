/-
  故障机器人 - 流线型+全息影像+精简
  Cards: 11

  Engine v3 change: hologramChoose is now queue-gated (requires hologramChoice
  from playing Hologram+). The original loop used 4 hologramChooses from 2
  Hologram plays, which is no longer valid.

  New strategy:
  - Setup: Play 3 powers (Defrag, Biased, Capacitor), exhaust Reboot, reduce
    Streamline cost to 0 over 3 turns, fill 6 Frost orb slots over 7 turns,
    then arrange hand={SL,CH,Skim,Turbo,Rec} disc={H1,H2}.
  - Loop: Play Turbo(+2E), SL(dmg), CH(Frost+draw H1,H2), H1(retrieve CH),
    H2(retrieve H1), Skim(draw SL,Turbo,Void,H2), Rec(exhaust Void),
    H1(retrieve Rec), H2(retrieve Skim). Net: 0 energy, +20 damage, state cycles.
-/

import StSVerify.CombosSpecL1.ComboStreamlineHologram

open CardName Action

namespace ComboStreamlineHologram_L1

-- ============================================================
-- FRAMEWORK-GENERATED (DO NOT MODIFY)
-- ============================================================

-- Card list: (CardName × count)


-- ============================================================
-- LLM FILLS IN BELOW
-- ============================================================

def setupTrace : List Action :=
  [ -- Turn 1: Draw powers + Reboot. Play 3 powers + Reboot.
    .draw 4, .draw 5, .draw 6, .draw 0, .draw 10,
    .play 4,   -- Defrag (power, 1E)
    .play 5,   -- Biased Cognition (power, 1E)
    .play 6,   -- Capacitor (power, 1E). E=0. OrbSlots=6. Focus=5.
    .play 10,  -- Reboot (0E): shuffle hand into draw, draw 5, exhaust self
    .draw 0, .draw 1, .draw 2, .draw 3, .draw 7,
    .endTurn,
    -- Turn 2: SL(2->1), CH(Frost#1)
    .draw 8, .draw 9,
    .draw 3, .draw 0, .draw 1,
    .play 0,   -- SL (2E): 20dmg, cost 2->1
    .play 3,   -- CH (1E): Frost#1, draw 2
    .draw 2, .draw 7,
    .endTurn,
    -- Turn 3: SL(1->0), CH(Frost#2)
    .draw 0, .draw 3, .draw 9, .draw 8, .draw 7,
    .play 0,   -- SL (1E): 20dmg, cost 1->0
    .play 3,   -- CH (1E): Frost#2, draw 2
    .draw 1, .draw 2,
    .endTurn,
    -- Turns 4-7: CH for Frost #3-#6
    .draw 3, .draw 0, .draw 9, .draw 8, .draw 7,
    .play 3, .draw 1, .draw 2,
    .endTurn,
    .draw 3, .draw 0, .draw 9, .draw 8, .draw 7,
    .play 3, .draw 1, .draw 2,
    .endTurn,
    .draw 3, .draw 0, .draw 9, .draw 8, .draw 7,
    .play 3, .draw 1, .draw 2,
    .endTurn,
    .draw 3, .draw 0, .draw 9, .draw 8, .draw 7,
    .play 3, .draw 1, .draw 2,
    .endTurn,
    -- Turn 8: Final arrangement
    .draw 3, .draw 0, .draw 9, .draw 8, .draw 7,
    .play 3,           -- CH (1E): Frost (stable at 6), draw 2
    .draw 1, .draw 2,
    .play 9,           -- Turbo (0E): +2E, Void(11) to disc
    .play 8,           -- Skim (1E): draw 4
    .draw 9, .draw 11, .draw 3, .failDraw,
    .play 7,           -- Recycle: exhaust Void(11)
    .recycleChoose 11,
    .play 1,           -- H1: retrieve Rec
    .hologramChoose 7,
    .play 2,           -- H2: retrieve Skim
    .hologramChoose 8
  ]

def loopTrace : List Action :=
  [ .play 9,           -- Turbo (0E): +2E, Void(12) to disc
    .play 0,           -- SL (0E): 20dmg
    .play 3,           -- CH (1E): Frost (stable), draw 2
    .draw 1, .draw 2,  -- draw H1, H2 from shuffled disc
    .play 1,           -- H1: hologramChoose
    .hologramChoose 3, -- retrieve CH
    .play 2,           -- H2: hologramChoose
    .hologramChoose 1, -- retrieve H1
    .play 8,           -- Skim (1E): draw 4
    .draw 0, .draw 9, .draw 12, .draw 2,  -- SL, Turbo, Void, H2
    .play 7,           -- Recycle: exhaust Void(12)
    .recycleChoose 12,
    .play 1,           -- H1: retrieve Rec
    .hologramChoose 7,
    .play 2,           -- H2: retrieve Skim
    .hologramChoose 8
  ]

def stateA : GameState := {
  hand := [{ id := 8, name := SkimPlus, cost := 1, damage := 0 },
           { id := 7, name := RecyclePlus, cost := 0, damage := 0 },
           { id := 3, name := CoolheadedPlus, cost := 1, damage := 0 },
           { id := 9, name := TurboPlus, cost := 0, damage := 0 },
           { id := 0, name := StreamlinePlus, cost := 0, damage := 20 }]
  drawPile := []
  discardPile := [{ id := 2, name := HologramPlus, cost := 0, damage := 0 },
                  { id := 1, name := HologramPlus, cost := 0, damage := 0 }]
  exhaustPile := [{ id := 11, name := Void, cost := 0, damage := 0 },
                  { id := 10, name := RebootPlus, cost := 0, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 40
  block := 10
  stance := .Neutral
  orbs := [.Frost, .Frost, .Frost, .Frost, .Frost, .Frost]
  orbSlots := 6
  focus := 5
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [CapacitorPlus, BiasedCognitionPlus, DefragmentPlus]
  nextId := 12
  noDraw := false
  corruptionActive := false
}

def stateB : GameState := {
  hand := [{ id := 8, name := SkimPlus, cost := 1, damage := 0 },
           { id := 7, name := RecyclePlus, cost := 0, damage := 0 },
           { id := 9, name := TurboPlus, cost := 0, damage := 0 },
           { id := 0, name := StreamlinePlus, cost := 0, damage := 20 },
           { id := 3, name := CoolheadedPlus, cost := 1, damage := 0 }]
  drawPile := []
  discardPile := [{ id := 2, name := HologramPlus, cost := 0, damage := 0 },
                  { id := 1, name := HologramPlus, cost := 0, damage := 0 }]
  exhaustPile := [{ id := 12, name := Void, cost := 0, damage := 0 },
                  { id := 11, name := Void, cost := 0, damage := 0 },
                  { id := 10, name := RebootPlus, cost := 0, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 60
  block := 30
  stance := .Neutral
  orbs := [.Frost, .Frost, .Frost, .Frost, .Frost, .Frost]
  orbSlots := 6
  focus := 5
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [CapacitorPlus, BiasedCognitionPlus, DefragmentPlus]
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

theorem ComboStreamlineHologram_infinite : InfiniteCombo cardDB cards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, no_end, same_mod, dealt_dmg⟩

theorem proof : InfiniteCombo cardDB cards enemy := ComboStreamlineHologram_infinite

end ComboStreamlineHologram_L1
