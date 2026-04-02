/-
  故障机器人 - 流线型+全息影像+精简 (Level 2)
  Cards: 11
  v2 engine rewrite

  No shuffle in the loop: all cards stay in hand via hologramChoose.
  Loop is entirely deterministic (no draw actions), so oracle is irrelevant.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboStreamlineHologram_L2

-- ============================================================
-- Deck definition (v2: CardName × count)
-- ============================================================

def cards : List (CardName × Nat) :=
  [ (StreamlinePlus, 1)      -- id 0
  , (HologramPlus, 2)        -- ids 1,2
  , (CoolheadedPlus, 1)      -- id 3
  , (DefragmentPlus, 1)      -- id 4
  , (BiasedCognitionPlus, 1) -- id 5
  , (CapacitorPlus, 1)       -- id 6
  , (RecyclePlus, 1)         -- id 7
  , (SkimPlus, 1)            -- id 8
  , (TurboPlus, 1)           -- id 9
  , (RebootPlus, 1)          -- id 10
  ]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- Card instance abbreviations
def sl : CardInstance := { id := 0, name := StreamlinePlus, cost := 0, damage := 20 }
def h1 : CardInstance := { id := 1, name := HologramPlus, cost := 0, damage := 0 }
def h2 : CardInstance := { id := 2, name := HologramPlus, cost := 0, damage := 0 }

-- ============================================================
-- Traces
-- ============================================================

def setupTrace : List Action := [
  -- Turn 1: draw 5
  .draw 0, .draw 7, .draw 3, .draw 8, .draw 9,
  .play 0,                         -- Streamline+ (cost 2): 20 dmg, override→1
  .recycleChoose 3,                -- exhaust Coolheaded+ (refund 1)
  .recycleChoose 8,                -- exhaust Skim+ (refund 1)
  .recycleChoose 9,                -- exhaust Turbo+ (refund 0)
  .recycleChoose 7,                -- exhaust Recycle+ (refund 0)
  .endTurn,
  -- Turn 2: draw 5
  .draw 4, .draw 5, .draw 6, .draw 10, .draw 1,
  .play 4,                         -- Defragment+: +1 focus
  .play 5,                         -- Biased Cognition+: +4 focus
  .play 6,                         -- Capacitor+: +3 orb slots
  .play 10,                        -- Reboot+: shuffle hand→draw, draw 5, exhaust
  .draw 1, .draw 2,                -- draw from [c1,c2]
  .draw 0,                         -- shuffle discard[c0]→draw, draw c0
  .failDraw,                       -- 2 draws remaining, piles empty
  .endTurn,
  -- Turn 3: draw 3
  .draw 0, .draw 1, .draw 2,
  .failDraw,                       -- piles empty
  .play 0,                         -- Streamline+ (cost 1→override 0)
  .play 1,                         -- Hologram+: 5 block
  .hologramChoose 0,               -- retrieve Streamline from discard
  .play 2,                         -- Hologram+: 5 block
  .hologramChoose 1,               -- retrieve Hologram #1
  .hologramChoose 2                -- retrieve Hologram #2
]

def loopTrace : List Action := [
  .play 0,                         -- Streamline+ (0 cost): 20 dmg
  .play 1,                         -- Hologram+ (0 cost): 5 block
  .hologramChoose 0,               -- retrieve Streamline
  .play 2,                         -- Hologram+ (0 cost): 5 block
  .hologramChoose 1,               -- retrieve Hologram #1
  .play 0,                         -- Streamline+ (0 cost): 20 dmg
  .hologramChoose 0,               -- retrieve Streamline
  .hologramChoose 2                -- retrieve Hologram #2
]

def exhaust_ : List CardInstance :=
  [ { id := 10, name := RebootPlus, cost := 0, damage := 0 }
  , { id := 7, name := RecyclePlus, cost := 0, damage := 0 }
  , { id := 9, name := TurboPlus, cost := 0, damage := 0 }
  , { id := 8, name := SkimPlus, cost := 1, damage := 0 }
  , { id := 3, name := CoolheadedPlus, cost := 1, damage := 0 } ]

def powers_ : List CardName := [CapacitorPlus, BiasedCognitionPlus, DefragmentPlus]

def stateA : GameState := {
  hand := [h2, h1, sl]
  drawPile := []
  discardPile := []
  exhaustPile := exhaust_
  inUse := []
  actionQueue := []
  energy := 2
  damage := 40
  block := 10
  stance := .Neutral
  orbs := []
  orbSlots := 6
  focus := 5
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := powers_
  nextId := 11
  noDraw := false
  corruptionActive := false
}

def stateB : GameState := {
  hand := [h2, sl, h1]
  drawPile := []
  discardPile := []
  exhaustPile := exhaust_
  inUse := []
  actionQueue := []
  energy := 2
  damage := 80
  block := 20
  stance := .Neutral
  orbs := []
  orbSlots := 6
  focus := 5
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := powers_
  nextId := 11
  noDraw := false
  corruptionActive := false
}

-- ============================================================
-- VERIFICATION (Level 2: guaranteed despite shuffle randomness)
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

theorem same_mod : sameModAccum stateA stateB = true := by native_decide
theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

-- Loop intermediate states (careful about resolveInUse behavior)
-- State after step returns from play 0 (Streamline in inUse)
private def t1 : GameState := {
  hand := [h2, h1], drawPile := [], discardPile := [], exhaustPile := exhaust_,
  inUse := [sl], actionQueue := [], energy := 2, damage := 60, block := 10,
  stance := .Neutral, orbs := [], orbSlots := 6, focus := 5,
  enemy := { vulnerable := 0, weak := 0, intending := false },
  activePowers := powers_, nextId := 11, noDraw := false, corruptionActive := false }

-- After resolveInUse on t1: Streamline to discard
private def t1r : GameState := {
  hand := [h2, h1], drawPile := [], discardPile := [sl], exhaustPile := exhaust_,
  inUse := [], actionQueue := [], energy := 2, damage := 60, block := 10,
  stance := .Neutral, orbs := [], orbSlots := 6, focus := 5,
  enemy := { vulnerable := 0, weak := 0, intending := false },
  activePowers := powers_, nextId := 11, noDraw := false, corruptionActive := false }

-- After step play 1 (Hologram+ in inUse, +5 block)
private def t2 : GameState := {
  hand := [h2], drawPile := [], discardPile := [sl], exhaustPile := exhaust_,
  inUse := [h1], actionQueue := [], energy := 2, damage := 60, block := 15,
  stance := .Neutral, orbs := [], orbSlots := 6, focus := 5,
  enemy := { vulnerable := 0, weak := 0, intending := false },
  activePowers := powers_, nextId := 11, noDraw := false, corruptionActive := false }

-- After resolveInUse on t2: Holo1 to discard
private def t2r : GameState := {
  hand := [h2], drawPile := [], discardPile := [h1, sl], exhaustPile := exhaust_,
  inUse := [], actionQueue := [], energy := 2, damage := 60, block := 15,
  stance := .Neutral, orbs := [], orbSlots := 6, focus := 5,
  enemy := { vulnerable := 0, weak := 0, intending := false },
  activePowers := powers_, nextId := 11, noDraw := false, corruptionActive := false }

-- After step hologramChoose 0 (retrieve Streamline from discard)
private def t3 : GameState := {
  hand := [sl, h2], drawPile := [], discardPile := [h1], exhaustPile := exhaust_,
  inUse := [], actionQueue := [], energy := 2, damage := 60, block := 15,
  stance := .Neutral, orbs := [], orbSlots := 6, focus := 5,
  enemy := { vulnerable := 0, weak := 0, intending := false },
  activePowers := powers_, nextId := 11, noDraw := false, corruptionActive := false }

-- After step play 2 (Holo2 in inUse, +5 block)
private def t4 : GameState := {
  hand := [sl], drawPile := [], discardPile := [h1], exhaustPile := exhaust_,
  inUse := [h2], actionQueue := [], energy := 2, damage := 60, block := 20,
  stance := .Neutral, orbs := [], orbSlots := 6, focus := 5,
  enemy := { vulnerable := 0, weak := 0, intending := false },
  activePowers := powers_, nextId := 11, noDraw := false, corruptionActive := false }

-- After resolveInUse on t4: Holo2 to discard
private def t4r : GameState := {
  hand := [sl], drawPile := [], discardPile := [h2, h1], exhaustPile := exhaust_,
  inUse := [], actionQueue := [], energy := 2, damage := 60, block := 20,
  stance := .Neutral, orbs := [], orbSlots := 6, focus := 5,
  enemy := { vulnerable := 0, weak := 0, intending := false },
  activePowers := powers_, nextId := 11, noDraw := false, corruptionActive := false }

-- After step hologramChoose 1 (retrieve Holo1 from discard)
private def t5 : GameState := {
  hand := [h1, sl], drawPile := [], discardPile := [h2], exhaustPile := exhaust_,
  inUse := [], actionQueue := [], energy := 2, damage := 60, block := 20,
  stance := .Neutral, orbs := [], orbSlots := 6, focus := 5,
  enemy := { vulnerable := 0, weak := 0, intending := false },
  activePowers := powers_, nextId := 11, noDraw := false, corruptionActive := false }

-- After step play 0 again (Streamline in inUse)
private def t6 : GameState := {
  hand := [h1], drawPile := [], discardPile := [h2], exhaustPile := exhaust_,
  inUse := [sl], actionQueue := [], energy := 2, damage := 80, block := 20,
  stance := .Neutral, orbs := [], orbSlots := 6, focus := 5,
  enemy := { vulnerable := 0, weak := 0, intending := false },
  activePowers := powers_, nextId := 11, noDraw := false, corruptionActive := false }

-- After resolveInUse on t6: Streamline to discard
private def t6r : GameState := {
  hand := [h1], drawPile := [], discardPile := [sl, h2], exhaustPile := exhaust_,
  inUse := [], actionQueue := [], energy := 2, damage := 80, block := 20,
  stance := .Neutral, orbs := [], orbSlots := 6, focus := 5,
  enemy := { vulnerable := 0, weak := 0, intending := false },
  activePowers := powers_, nextId := 11, noDraw := false, corruptionActive := false }

-- After step hologramChoose 0 (retrieve Streamline from discard)
private def t7 : GameState := {
  hand := [sl, h1], drawPile := [], discardPile := [h2], exhaustPile := exhaust_,
  inUse := [], actionQueue := [], energy := 2, damage := 80, block := 20,
  stance := .Neutral, orbs := [], orbSlots := 6, focus := 5,
  enemy := { vulnerable := 0, weak := 0, intending := false },
  activePowers := powers_, nextId := 11, noDraw := false, corruptionActive := false }

-- After step hologramChoose 2 (retrieve Holo2 from discard) = stateB
-- stateB hand = [h2, sl, h1]

-- Step lemmas
private theorem c0 : resolveInUse cardDB (autoDrain cardDB stateA) = stateA := by native_decide
private theorem s1 : step cardDB stateA (.play 0) = some t1 := by native_decide
private theorem c1 : resolveInUse cardDB (autoDrain cardDB t1) = t1r := by native_decide
private theorem s2 : step cardDB t1r (.play 1) = some t2 := by native_decide
private theorem c2 : resolveInUse cardDB (autoDrain cardDB t2) = t2r := by native_decide
private theorem s3 : step cardDB t2r (.hologramChoose 0) = some t3 := by native_decide
private theorem c3 : resolveInUse cardDB (autoDrain cardDB t3) = t3 := by native_decide
private theorem s4 : step cardDB t3 (.play 2) = some t4 := by native_decide
private theorem c4 : resolveInUse cardDB (autoDrain cardDB t4) = t4r := by native_decide
private theorem s5 : step cardDB t4r (.hologramChoose 1) = some t5 := by native_decide
private theorem c5 : resolveInUse cardDB (autoDrain cardDB t5) = t5 := by native_decide
private theorem s6 : step cardDB t5 (.play 0) = some t6 := by native_decide
private theorem c6 : resolveInUse cardDB (autoDrain cardDB t6) = t6r := by native_decide
private theorem s7 : step cardDB t6r (.hologramChoose 0) = some t7 := by native_decide
private theorem c7 : resolveInUse cardDB (autoDrain cardDB t7) = t7 := by native_decide
private theorem s8 : step cardDB t7 (.hologramChoose 2) = some stateB := by native_decide
private theorem cB : resolveInUse cardDB (autoDrain cardDB stateB) = stateB := by native_decide

/-- No draw actions in the loop, so oracle is irrelevant. -/
theorem loop_executeL2_eq (oracle : ShuffleOracle) :
    executeL2 cardDB oracle 0 stateA loopTrace = some (stateB, 0) := by
  simp only [loopTrace, executeL2, stepL2]
  rw [c0, s1]; simp only []
  rw [c1, s2]; simp only []
  rw [c2, s3]; simp only []
  rw [c3, s4]; simp only []
  rw [c4, s5]; simp only []
  rw [c5, s6]; simp only []
  rw [c6, s7]; simp only []
  rw [c7, s8]; simp only []
  rw [cB]

theorem ComboStreamlineHologram_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  exact ⟨setupTrace, stateA, setup_ok, fun oracle _hvalid =>
    ⟨loopTrace, stateB, 0, loop_executeL2_eq oracle, same_mod, dealt_dmg⟩⟩

end ComboStreamlineHologram_L2
