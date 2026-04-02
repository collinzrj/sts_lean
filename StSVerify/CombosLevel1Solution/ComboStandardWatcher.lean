/-
  观者 - 标准沙雕无限
  Cards: 12
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboStandardWatcher

-- ============================================================
-- FRAMEWORK-GENERATED (DO NOT MODIFY)
-- ============================================================

def cards : List (CardName × Nat) :=
  [ (Rushdown, 2)             -- ids 0,1
  , (MentalFortressPlus, 1)   -- id 2
  , (EruptionPlus, 1)         -- id 3
  , (TantrumPlus, 1)          -- id 4
  , (InnerPeacePlus, 1)       -- id 5
  , (FearNoEvilPlus, 1)       -- id 6
  , (FlurryOfBlowsPlus, 1)    -- id 7
  , (Scrawl, 1)               -- id 8
  , (VaultPlus, 1)            -- id 9
  , (DeusExMachina, 1)        -- id 10
  , (TalkToTheHandPlus, 1)    -- id 11
  ]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := true }

-- ============================================================
-- LLM FILLS IN BELOW
-- ============================================================

/-
  Strategy:
  Turn 1: Draw DEM + powers + InnerPeace+. DEM triggers: +2 Miracles (ids 12,13), exhaust.
    Play powers (Rushdown x2, MF+). Play Miracles for energy. InnerPeace+ enters Calm.
  Turn 2: Draw remaining cards. Tantrum+ (Calm→Wrath, Rushdown draws). Exhaust TtTH, Vault, Scrawl.
  Turn 3: Set up loop state with stance cycling.

  Loop: Tantrum+ (Calm→Wrath), FNE (Wrath→Calm), Eruption+ (Calm→Wrath),
    Flurry cycle. 73 damage per loop.
-/

def setupTrace : List Action := [
  -- Turn 1: draw 5
  .draw 10, .draw 0, .draw 1, .draw 2, .draw 5,
  .resolveDrawTrigger 10,       -- DEM: +2 Miracles (ids 12,13), exhaust DEM
  .play 0,                      -- Rushdown (power), E=2
  .play 1,                      -- Rushdown (power), E=1
  .play 2,                      -- MF+ (power), E=0
  .play 12,                     -- Miracle: E=1, exhaust
  .play 13,                     -- Miracle: E=2, exhaust
  .play 5,                      -- InnerPeace+: enter Calm, E=1
  .endTurn,
  -- Turn 2
  .draw 4, .draw 6, .draw 11, .draw 9, .draw 8,
  .play 4,                      -- Tantrum+: Calm→Wrath +2E=4, 24dmg
  .resolveRushdown,             -- +4 draws
  .draw 3, .draw 7, .draw 4, .draw 5,
  .play 11,                     -- TtTH: 14dmg, exhaust, E=3
  .play 9,                      -- Vault+: exhaust, E=1
  .play 8,                      -- Scrawl: exhaust, E=0, draw to full
  .failDraw,                    -- piles empty
  .endTurn,
  -- Turn 3
  .draw 4, .draw 6, .draw 3, .draw 7, .draw 5,
  .play 6,                      -- FNE: Wrath→Calm +2E+6blk, 22dmg
  .play 3,                      -- Eruption+: Calm→Wrath +2E+6blk, 18dmg
  .resolveRushdown,             -- +4 draws
  .draw 6, .draw 3,
  .failDraw,
  .play 7,                      -- Flurry: 12dmg Wrath
  .play 5,                      -- InnerPeace+: →Calm +6blk
  .autoPlayFlurry 7             -- Flurry auto: 6dmg
]

def loopTrace : List Action := [
  .play 4,                      -- Tantrum+: Calm→Wrath +2E, 24dmg +6blk
  .resolveRushdown,             -- +4 draws
  .autoPlayFlurry 7,            -- Flurry auto: 12dmg (Wrath)
  .draw 4, .draw 5, .draw 7,
  .failDraw,
  .play 6,                      -- FNE: Wrath→Calm +2E+6blk, 22dmg
  .play 3,                      -- Eruption+: Calm→Wrath +2E+6blk, 18dmg
  .resolveRushdown,             -- +4 draws
  .draw 6, .draw 3,
  .failDraw,
  .play 7,                      -- Flurry: 12dmg Wrath
  .play 5,                      -- InnerPeace+: →Calm +6blk
  .autoPlayFlurry 7             -- Flurry auto: 6dmg
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

theorem same_mod : sameModAccum stateA stateB = true := by native_decide
theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

theorem ComboStandardWatcher_infinite : InfiniteCombo cardDB cards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboStandardWatcher
