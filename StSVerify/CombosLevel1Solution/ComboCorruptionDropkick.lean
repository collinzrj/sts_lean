/-
  铁甲战士 - 腐化消耗精简+飞踢 (Ironclad Corruption + Dropkick Infinite)
  Cards: 13
  v2 engine rewrite
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboCorruptionDropkick

-- ============================================================
-- Deck definition
-- IDs: Corr=0, DE+=1, FNP+=2, Bash+=3, DK1=4, DK2=5,
--      SIO1=6, SIO2=7, TG+=8, Met+=9, Imp+=10, Off=11, BT+=12
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(Corruption, 1), (DarkEmbracePlus, 1), (FeelNoPainPlus, 1), (BashPlus, 1),
   (Dropkick, 2), (ShrugItOff, 2), (TrueGritPlus, 1), (MetallicizePlus, 1),
   (ImperviousPlus, 1), (Offering, 1), (BattleTrancePlus, 1)]

def enemy : EnemyState := { vulnerable := 3, weak := 0, intending := false }

-- ============================================================
-- Traces
-- ============================================================

def setupTrace : List Action := [
  -- Turn 1
  .draw 11, .draw 0, .draw 1, .draw 9, .draw 8,
  .play 11,                       -- Offering (0E): +2E, draw 3, exhaust self
  .draw 12, .draw 2, .draw 3,
  .play 0, .play 1, .play 9,     -- Corruption(3E), DarkEmbrace+(1E), Metallicize+(1E)
  .play 8,                        -- TrueGrit+ (0 cost, corruption): +9blk, exhaust 1, self exhausts
  .exhaust 12,                    -- Exhaust BattleTrance+ -> DE+1 draw, FNP+4 block
  .draw 4, .draw 5,              -- Draw both Dropkicks
  .endTurn,
  -- Turn 2
  .draw 6, .draw 7, .draw 10,
  .draw 2, .draw 3,              -- shuffle discard -> draw first
  .play 2,                        -- FeelNoPain+ (1E, power)
  .play 6,                        -- ShrugItOff#1 (0 cost, corruption): +8blk, draw 1, exhausts -> DE+1, FNP+4
  .draw 4, .draw 5,              -- DE draw + SIO draw
  .play 7,                        -- ShrugItOff#2 (0 cost, corruption): +8blk, draw 1, exhausts -> DE+1, FNP+4
  .failDraw,                      -- piles empty
  .play 10,                       -- Impervious+ (0 cost, corruption): +40blk, exhausts -> DE+1, FNP+4
  .failDraw,                      -- piles empty
  .play 5,                        -- DK#2: 7dmg, +1E, +1draw
  .failDraw,                      -- piles empty (DK#2 still in inUse)
  .play 4,                        -- DK#1: 7dmg, +1E, +1draw
  .draw 5                         -- shuffle DK#2 from discard -> draw, draw DK#2
]

def stateA : GameState := {
  hand := [{ id := 5, name := Dropkick, cost := 1, damage := 5 },
           { id := 3, name := BashPlus, cost := 2, damage := 10 }]
  drawPile := []
  discardPile := [{ id := 4, name := Dropkick, cost := 1, damage := 5 }]
  exhaustPile := [{ id := 10, name := ImperviousPlus, cost := 2, damage := 0 },
                  { id := 7, name := ShrugItOff, cost := 1, damage := 0 },
                  { id := 6, name := ShrugItOff, cost := 1, damage := 0 },
                  { id := 8, name := TrueGritPlus, cost := 1, damage := 0 },
                  { id := 12, name := BattleTrancePlus, cost := 0, damage := 0 },
                  { id := 11, name := Offering, cost := 0, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 2
  damage := 14
  block := 68
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 3, weak := 0, intending := false }
  activePowers := [FeelNoPainPlus, MetallicizePlus, DarkEmbracePlus, Corruption]
  nextId := 13
  noDraw := false
  corruptionActive := true
}

def loopTrace : List Action := [
  .play 5,                        -- DK#2: 7dmg, +1E, +1draw
  .draw 4,                        -- shuffle DK#1 -> draw, draw DK#1
  .play 4,                        -- DK#1: 7dmg, +1E, +1draw
  .draw 5                         -- shuffle DK#2 -> draw, draw DK#2
]

def stateB : GameState :=
  { stateA with damage := 28 }

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

theorem ComboCorruptionDropkick_infinite : InfiniteCombo cardDB allCards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, same_mod, dealt_dmg⟩

end ComboCorruptionDropkick
