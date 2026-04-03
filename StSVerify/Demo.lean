/-
  Demo: Silent 5-card infinite combo
  Prepared+ x2, Reflex+ x2, Neutralize+ x1

  v2 engine: unified CardInstance model, mkInitialState takes List (CardName × Nat)
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace DemoSilent5Card

-- ============================================================
-- Card deck: (CardName, count)
-- IDs assigned sequentially: PP1=0, PP2=1, RP1=2, RP2=3, NP=4
-- ============================================================

def allCards : List (CardName × Nat) := [(PreparedPlus, 2), (ReflexPlus, 2), (NeutralizePlus, 1)]
def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- ============================================================
-- Traces
-- ============================================================

-- Setup: draw 5, play Neutralize, play Prepared#1 (draw 2, discard 2), draw/discard cycle
def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 4,                -- Neutralize+: 4 dmg, +2 weak -> resolveCard 4 auto-drained
  .play 0,                -- Prepared+#1: draw 2, discard 2 -> resolveCard 0 queued
  .draw 4,                -- shuffle discard [N(4)] -> draw, draw N(4)
  .failDraw,              -- draw pile empty, skip 2nd draw
  .discard 2,             -- discard Reflex+(2) -> triggers draw 3 (bottom)
  .discard 3,             -- discard Reflex+(3) -> triggers draw 3 (bottom); autoDrain resolves P1(0)->discard
  -- discard=[PP1(0),RP2(3),RP1(2)], queue=6 draws
  .draw 3,                -- shuffle -> draw, draw RP2(3)
  .draw 2,                -- draw RP1(2)
  .draw 0,                -- draw PP1(0)
  .failDraw               -- 3 remaining draws, piles empty
]

-- stateA: after setup — all 5 cards in hand, nothing in discard
def stateA : GameState := {
  hand := [{ id := 0, name := PreparedPlus, cost := 0, damage := 0 },
           { id := 2, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 3, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 4, name := NeutralizePlus, cost := 0, damage := 4 },
           { id := 1, name := PreparedPlus, cost := 0, damage := 0 }]
  drawPile := []
  discardPile := []
  exhaustPile := []
  inUse := []
  actionQueue := []
  energy := 3
  damage := 4
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := []
  nextId := 5
  noDraw := false
  corruptionActive := false
}

-- Loop: play Neutralize, play Prepared#2 (draw 2, discard 2), draw/discard cycle
def loopTrace : List Action := [
  .play 4,                -- Neutralize+: 4 dmg, +2 weak -> resolveCard auto-drained
  .play 1,                -- Prepared+#2: draw 2, discard 2
  .draw 4,                -- shuffle discard [N(4)] -> draw, draw N(4)
  .failDraw,              -- piles empty
  .discard 2,             -- discard Reflex+(2) -> triggers draw 3 (bottom)
  .discard 3,             -- discard Reflex+(3) -> triggers draw 3 (bottom); autoDrain resolves PP2(1)->discard
  -- discard=[PP2(1),RP2(3),RP1(2)], queue=6 draws
  .draw 3,                -- shuffle -> draw, draw RP2(3)
  .draw 2,                -- draw RP1(2)
  .draw 1,                -- draw PP2(1)
  .failDraw               -- 3 remaining draws, piles empty
]

-- stateB: after one loop iteration — same structure, damage increased
def stateB : GameState := {
  hand := [{ id := 1, name := PreparedPlus, cost := 0, damage := 0 },
           { id := 2, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 3, name := ReflexPlus, cost := 0, damage := 0 },
           { id := 4, name := NeutralizePlus, cost := 0, damage := 4 },
           { id := 0, name := PreparedPlus, cost := 0, damage := 0 }]
  drawPile := []
  discardPile := []
  exhaustPile := []
  inUse := []
  actionQueue := []
  energy := 3
  damage := 8
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := []
  nextId := 5
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

theorem silent_5card_infinite : InfiniteCombo cardDB allCards enemy :=
  ⟨setupTrace, loopTrace, stateA, stateB, setup_ok, loop_ok, no_end, same_mod, dealt_dmg⟩

end DemoSilent5Card
