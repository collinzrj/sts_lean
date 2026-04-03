/-
  Level 2: Acrobatics + Tactician combo (v2 engine rewrite)

  Shuffle points in the loop:
    oracle 0: [ci6, ci1]  (2 permutations)
    oracle 1: [ci10]      (singleton, forced)
    oracle 2: [ci0, ci2]  (2 permutations)
    oracle 3: [ci3]       (singleton, forced)
  Total: 2 x 2 = 4 oracle cases, but only 2 distinct final states.
  After step 9 (play c1), the two shuffle-0 paths converge,
  so only oracle 2 matters for the final hand order.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboAcrobaticsTactician_L2

-- ============================================================
-- CARD INSTANCES
-- ============================================================

private def ci0  : CardInstance := { id := 0,  name := AcrobaticsPlus,  cost := 1, damage := 0 }
private def ci1  : CardInstance := { id := 1,  name := AcrobaticsPlus,  cost := 1, damage := 0 }
private def ci2  : CardInstance := { id := 2,  name := TacticianPlus,   cost := 0, damage := 0 }
private def ci3  : CardInstance := { id := 3,  name := ReflexPlus,      cost := 0, damage := 0 }
private def ci4  : CardInstance := { id := 4,  name := BackflipPlus,    cost := 1, damage := 0 }
private def ci5  : CardInstance := { id := 5,  name := BackflipPlus,    cost := 1, damage := 0 }
private def ci6  : CardInstance := { id := 6,  name := NeutralizePlus,  cost := 0, damage := 4 }
private def ci10 : CardInstance := { id := 10, name := EscapePlanPlus,  cost := 0, damage := 0 }

-- ============================================================
-- FRAMEWORK-GENERATED
-- ============================================================

def cards : List (CardName × Nat) := [
  (AcrobaticsPlus, 2), (TacticianPlus, 1), (ReflexPlus, 1),
  (BackflipPlus, 2), (NeutralizePlus, 1), (AfterImage, 1),
  (AdrenalinePlus, 1), (CaltropPlus, 1), (EscapePlanPlus, 1),
  (GrandFinalePlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- ============================================================
-- SETUP
-- ============================================================

def setupTrace : List Action := [
  .draw 8, .draw 7, .draw 9, .draw 6, .draw 0,
  .play 8, .draw 11, .draw 1,
  .play 7, .play 9, .play 6,
  .play 0, .draw 2, .draw 3, .draw 4, .draw 5,
  .discard 2,
  .play 1, .draw 10, .draw 6, .draw 0, .draw 2,
  .discard 3,
  .draw 3, .failDraw,
  .play 11
]

-- ============================================================
-- STATES
-- ============================================================

private def exhaustConst : List CardInstance :=
  [ { id := 11, name := GrandFinalePlus, cost := 0, damage := 60 },
    { id := 8, name := AdrenalinePlus, cost := 0, damage := 0 } ]

def stateA : GameState := {
  hand := [ci3, ci2, ci0, ci6, ci10, ci5, ci4]
  drawPile := []
  discardPile := [ci1]
  exhaustPile := exhaustConst
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

-- Two possible final states depending on oracle 2
def stateBx : GameState := {
  hand := [ci3, ci2, ci0, ci10, ci6, ci5, ci4]
  drawPile := []
  discardPile := [ci1]
  exhaustPile := exhaustConst
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

def stateBy : GameState := {
  hand := [ci3, ci0, ci2, ci10, ci6, ci5, ci4]
  drawPile := []
  discardPile := [ci1]
  exhaustPile := exhaustConst
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

-- ============================================================
-- BASIC VERIFICATION
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

theorem same_mod_x : sameModAccum stateA stateBx = true := by native_decide
theorem same_mod_y : sameModAccum stateA stateBy = true := by native_decide
theorem dealt_dmg_x : dealtDamage stateA stateBx = true := by native_decide
theorem dealt_dmg_y : dealtDamage stateA stateBy = true := by native_decide

-- ============================================================
-- ORACLE-ADAPTIVE LOOP TRACE
-- ============================================================

def mkLoopTrace (oracle : ShuffleOracle) : List Action :=
  let shuf0 := oracle 0 [ci6, ci1]
  let shuf2 := oracle 2 [ci0, ci2]
  match shuf0, shuf2 with
  | d0a :: d0b :: _, d2a :: d2b :: _ =>
    [ .play 6, .play 10,
      .draw d0a.id,
      .play 0,
      .draw d0b.id,
      .draw 10,
      .failDraw,
      .discard 2,
      .play 1,
      .draw d2a.id,
      .draw d2b.id,
      .failDraw,
      .discard 3,
      .draw 3,
      .failDraw ]
  | _, _ => []

private theorem noEndTurn_bx1 (oracle : ShuffleOracle)
    (h0 : oracle 0 [ci6, ci1] = [ci6, ci1]) (h2 : oracle 2 [ci0, ci2] = [ci0, ci2]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h0, h2]; native_decide
private theorem noEndTurn_by1 (oracle : ShuffleOracle)
    (h0 : oracle 0 [ci6, ci1] = [ci6, ci1]) (h2 : oracle 2 [ci0, ci2] = [ci2, ci0]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h0, h2]; native_decide
private theorem noEndTurn_ax1 (oracle : ShuffleOracle)
    (h0 : oracle 0 [ci6, ci1] = [ci1, ci6]) (h2 : oracle 2 [ci0, ci2] = [ci0, ci2]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h0, h2]; native_decide
private theorem noEndTurn_ay1 (oracle : ShuffleOracle)
    (h0 : oracle 0 [ci6, ci1] = [ci1, ci6]) (h2 : oracle 2 [ci0, ci2] = [ci2, ci0]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h0, h2]; native_decide

-- ============================================================
-- PERMUTATION LEMMAS
-- ============================================================

private theorem perm_2_ci (l : List CardInstance) (x y : CardInstance) (hne : x ≠ y)
    (hp : List.Perm l [x, y]) :
    l = [x, y] ∨ l = [y, x] := by
  have hlen := hp.length_eq; simp at hlen
  match l, hlen with
  | [a, b], _ =>
    have hx : x ∈ [a, b] := hp.mem_iff.mpr (by simp)
    have hy : y ∈ [a, b] := hp.mem_iff.mpr (by simp)
    simp [List.mem_cons, List.mem_nil_iff] at hx hy
    have hnd : [a, b].Nodup := hp.nodup_iff.mpr (by simp [hne])
    rw [List.nodup_cons] at hnd
    simp [List.mem_cons, List.mem_nil_iff] at hnd
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> (first | simp_all | omega)

private theorem perm_one_ci (a : CardInstance) (l : List CardInstance) (hp : List.Perm l [a]) :
    l = [a] := by
  have hlen := hp.length_eq; simp at hlen
  match l, hlen with
  | [x], _ =>
    have : x ∈ [a] := hp.subset (List.mem_cons_self x [])
    simp [List.mem_cons, List.mem_nil_iff] at this; subst this; rfl

-- ============================================================
-- GENERIC STEP HELPERS
-- ============================================================

private theorem exL2_cons {oracle : ShuffleOracle} {si si' : Nat} {s s0 s' : GameState}
    {a : Action} {rest : List Action}
    (hc : resolveInUse cardDB (autoDrain cardDB s) = s0)
    (hs : stepL2 cardDB oracle si s0 a = some (s', si')) :
    executeL2 cardDB oracle si s (a :: rest) =
    executeL2 cardDB oracle si' s' rest := by
  simp only [executeL2, hc, hs]

private theorem sL2_step {oracle : ShuffleOracle} {si : Nat} {s s' : GameState} {a : Action}
    (hn1 : ∀ c, a ≠ .draw c)
    (hs : step cardDB s a = some s') :
    stepL2 cardDB oracle si s a = some (s', si) := by
  cases a with
  | draw c => exact absurd rfl (hn1 c)
  | _ => simp only [stepL2, hs]

private theorem sL2_draw {oracle : ShuffleOracle} {si si' : Nat} {s s' : GameState} {c : CId}
    (hd : drawCardL2 oracle si s c = some (s', si')) :
    stepL2 cardDB oracle si s (.draw c) = some (s', si') := by
  simp only [stepL2, hd]

-- ============================================================
-- INTERMEDIATE STATES
-- ============================================================

-- s1: After play c6 (Neutralize+)
-- hand=[ci3,ci2,ci0,ci10,ci5,ci4], inUse=[ci6], disc=[ci1]
-- E=3, D=68, B=7 (AI+1), weak=4
private def s1 : GameState := {
  hand := [ci3, ci2, ci0, ci10, ci5, ci4]
  drawPile := []
  discardPile := [ci1]
  exhaustPile := exhaustConst
  inUse := [ci6]
  actionQueue := []
  energy := 3, damage := 68, block := 7, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s1r: resolveInUse → ci6 to discard
private def s1r : GameState := {
  hand := [ci3, ci2, ci0, ci10, ci5, ci4]
  drawPile := []
  discardPile := [ci6, ci1]
  exhaustPile := exhaustConst
  inUse := []
  actionQueue := []
  energy := 3, damage := 68, block := 7, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s2: After play c10 (EscapePlan+): draw 1, block+1(EP), block+1(AI)
-- hand=[ci3,ci2,ci0,ci5,ci4], inUse=[ci10], disc=[ci6,ci1]
-- aq=[.draw], E=3, D=68, B=9
private def s2 : GameState := {
  hand := [ci3, ci2, ci0, ci5, ci4]
  drawPile := []
  discardPile := [ci6, ci1]
  exhaustPile := exhaustConst
  inUse := [ci10]
  actionQueue := [.draw]
  energy := 3, damage := 68, block := 8, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- After draw (shuffle 0): [ci6,ci1] permuted by oracle
-- aq was [.draw], inUse still [ci10] (aq not empty → no resolveInUse)
-- Case a: draw ci1 (oracle gives [ci1,ci6])
private def s3a : GameState := {
  hand := [ci1, ci3, ci2, ci0, ci5, ci4]
  drawPile := [ci6]
  discardPile := []
  exhaustPile := exhaustConst
  inUse := [ci10]
  actionQueue := []
  energy := 3, damage := 68, block := 8, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- Case b: draw ci6 (oracle gives [ci6,ci1])
private def s3b : GameState := {
  hand := [ci6, ci3, ci2, ci0, ci5, ci4]
  drawPile := [ci1]
  discardPile := []
  exhaustPile := exhaustConst
  inUse := [ci10]
  actionQueue := []
  energy := 3, damage := 68, block := 8, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- resolveInUse: aq empty now → ci10 to discard
private def s3ar : GameState := { s3a with discardPile := [ci10], inUse := [] }
private def s3br : GameState := { s3b with discardPile := [ci10], inUse := [] }

-- After play c0 (Acrobatics+): draw 4, discard 1. AI+1 block.
-- hand loses ci0, inUse=[ci0], aq=[.draw,.draw,.draw,.draw,.discardChoice]
-- Case a: hand=[ci1,ci3,ci2,ci5,ci4], draw=[ci6], disc=[ci10]
private def s4a : GameState := {
  hand := [ci1, ci3, ci2, ci5, ci4]
  drawPile := [ci6]
  discardPile := [ci10]
  exhaustPile := exhaustConst
  inUse := [ci0]
  actionQueue := [.draw, .draw, .draw, .draw, .discardChoice]
  energy := 2, damage := 68, block := 9, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}
-- Case b: hand=[ci6,ci3,ci2,ci5,ci4], draw=[ci1], disc=[ci10]
private def s4b : GameState := {
  hand := [ci6, ci3, ci2, ci5, ci4]
  drawPile := [ci1]
  discardPile := [ci10]
  exhaustPile := exhaustConst
  inUse := [ci0]
  actionQueue := [.draw, .draw, .draw, .draw, .discardChoice]
  energy := 2, damage := 68, block := 9, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- Draw d0b (second card from shuffle 0, from drawPile, no shuffle)
-- Case a: draw ci6 from [ci6]
private def s5a : GameState := { s4a with
  hand := [ci6, ci1, ci3, ci2, ci5, ci4], drawPile := []
  actionQueue := [.draw, .draw, .draw, .discardChoice] }
-- Case b: draw ci1 from [ci1]
private def s5b : GameState := { s4b with
  hand := [ci1, ci6, ci3, ci2, ci5, ci4], drawPile := []
  actionQueue := [.draw, .draw, .draw, .discardChoice] }

-- Draw c10: shuffle of [ci10] (singleton, oracle 1)
-- Case a: hand=[ci10,ci6,ci1,ci3,ci2,ci5,ci4], draw=[], disc=[]
private def s6a : GameState := { s5a with
  hand := [ci10, ci6, ci1, ci3, ci2, ci5, ci4], drawPile := [], discardPile := []
  actionQueue := [.draw, .draw, .discardChoice] }
-- Case b:
private def s6b : GameState := { s5b with
  hand := [ci10, ci1, ci6, ci3, ci2, ci5, ci4], drawPile := [], discardPile := []
  actionQueue := [.draw, .draw, .discardChoice] }

-- failDraw: drop leading draws → aq=[.discardChoice]
private def s7a : GameState := { s6a with actionQueue := [.discardChoice] }
private def s7b : GameState := { s6b with actionQueue := [.discardChoice] }

-- discard c2 (Tactician+): onDiscard=[gainEnergy 2], priority=.top
-- +2E, ci2 to disc. Then aq=[] → resolveInUse: ci0 to disc
-- Case a: hand=[ci10,ci6,ci1,ci3,ci5,ci4], disc=[ci0,ci2], E=4
private def s8a : GameState := {
  hand := [ci10, ci6, ci1, ci3, ci5, ci4]
  drawPile := [], discardPile := [ci0, ci2]
  exhaustPile := exhaustConst, inUse := []
  actionQueue := []
  energy := 4, damage := 68, block := 9, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}
-- Case b:
private def s8b : GameState := {
  hand := [ci10, ci1, ci6, ci3, ci5, ci4]
  drawPile := [], discardPile := [ci0, ci2]
  exhaustPile := exhaustConst, inUse := []
  actionQueue := []
  energy := 4, damage := 68, block := 9, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- play c1 (Acrobatics+ #2): CONVERGES!
-- Both paths: hand=[ci10,ci6,ci3,ci5,ci4], disc=[ci0,ci2]
-- inUse=[ci1], aq=[.draw,.draw,.draw,.draw,.discardChoice], E=3, B=11 (AI+1)
private def s9 : GameState := {
  hand := [ci10, ci6, ci3, ci5, ci4]
  drawPile := [], discardPile := [ci0, ci2]
  exhaustPile := exhaustConst, inUse := [ci1]
  actionQueue := [.draw, .draw, .draw, .draw, .discardChoice]
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- Draw d2a: shuffle [ci0,ci2] (oracle 2)
-- Case x: [ci0,ci2] → draw ci0
private def s10x : GameState := { s9 with
  hand := [ci0, ci10, ci6, ci3, ci5, ci4], drawPile := [ci2], discardPile := []
  actionQueue := [.draw, .draw, .draw, .discardChoice] }
-- Case y: [ci2,ci0] → draw ci2
private def s10y : GameState := { s9 with
  hand := [ci2, ci10, ci6, ci3, ci5, ci4], drawPile := [ci0], discardPile := []
  actionQueue := [.draw, .draw, .draw, .discardChoice] }

-- Draw d2b: from drawPile (no shuffle)
-- Case x: draw ci2 from [ci2]
private def s11x : GameState := { s10x with
  hand := [ci2, ci0, ci10, ci6, ci3, ci5, ci4], drawPile := []
  actionQueue := [.draw, .draw, .discardChoice] }
-- Case y: draw ci0 from [ci0]
private def s11y : GameState := { s10y with
  hand := [ci0, ci2, ci10, ci6, ci3, ci5, ci4], drawPile := []
  actionQueue := [.draw, .draw, .discardChoice] }

-- failDraw → aq=[.discardChoice]
private def s12x : GameState := { s11x with actionQueue := [.discardChoice] }
private def s12y : GameState := { s11y with actionQueue := [.discardChoice] }

-- discard c3 (Reflex+): onDiscard=[drawCards 3], priority=.bottom
-- ci3 to disc, aq=[.draw,.draw,.draw]
-- inUse still [ci1] (aq not empty)
private def s13x : GameState := {
  hand := [ci2, ci0, ci10, ci6, ci5, ci4]
  drawPile := [], discardPile := [ci3]
  exhaustPile := exhaustConst, inUse := [ci1]
  actionQueue := [.draw, .draw, .draw]
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}
private def s13y : GameState := {
  hand := [ci0, ci2, ci10, ci6, ci5, ci4]
  drawPile := [], discardPile := [ci3]
  exhaustPile := exhaustConst, inUse := [ci1]
  actionQueue := [.draw, .draw, .draw]
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- draw c3: shuffle [ci3] (singleton, oracle 3)
private def s14x : GameState := { s13x with
  hand := [ci3, ci2, ci0, ci10, ci6, ci5, ci4], drawPile := [], discardPile := []
  actionQueue := [.draw, .draw] }
private def s14y : GameState := { s13y with
  hand := [ci3, ci0, ci2, ci10, ci6, ci5, ci4], drawPile := [], discardPile := []
  actionQueue := [.draw, .draw] }

-- failDraw: aq=[] → resolveInUse: ci1 to disc → stateBx/stateBy
-- (resolveInUse fires because aq empty and inUse nonempty)

-- ============================================================
-- L1 STEP THEOREMS
-- ============================================================

theorem hs1 : step cardDB stateA (.play 6) = some s1 := by native_decide
theorem hc1 : resolveInUse cardDB (autoDrain cardDB s1) = s1r := by native_decide
theorem hs2 : step cardDB s1r (.play 10) = some s2 := by native_decide
theorem hc2 : resolveInUse cardDB (autoDrain cardDB s2) = s2 := by native_decide

-- play c0
theorem hs4a : step cardDB s3ar (.play 0) = some s4a := by native_decide
theorem hs4b : step cardDB s3br (.play 0) = some s4b := by native_decide

-- failDraw
theorem hs7a : step cardDB s6a .failDraw = some s7a := by native_decide
theorem hs7b : step cardDB s6b .failDraw = some s7b := by native_decide

-- discard c2 (Tactician+)
-- Note: discard fires onDiscard (gainEnergy 2). Then aq empty → resolveInUse: ci0 to disc
-- The raw state after discard has inUse=[ci0], disc=[ci2], aq=[]
-- resolveInUse moves ci0 to disc
private def s8a_raw : GameState := {
  hand := [ci10, ci6, ci1, ci3, ci5, ci4]
  drawPile := [], discardPile := [ci2]
  exhaustPile := exhaustConst, inUse := [ci0]
  actionQueue := []
  energy := 4, damage := 68, block := 9, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}
private def s8b_raw : GameState := {
  hand := [ci10, ci1, ci6, ci3, ci5, ci4]
  drawPile := [], discardPile := [ci2]
  exhaustPile := exhaustConst, inUse := [ci0]
  actionQueue := []
  energy := 4, damage := 68, block := 9, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

theorem hs8a : step cardDB s7a (.discard 2) = some s8a_raw := by native_decide
theorem hc8a : resolveInUse cardDB (autoDrain cardDB s8a_raw) = s8a := by native_decide
theorem hs8b : step cardDB s7b (.discard 2) = some s8b_raw := by native_decide
theorem hc8b : resolveInUse cardDB (autoDrain cardDB s8b_raw) = s8b := by native_decide

-- play c1 (converges)
theorem hs9a : step cardDB s8a (.play 1) = some s9 := by native_decide
theorem hs9b : step cardDB s8b (.play 1) = some s9 := by native_decide
theorem hc9 : resolveInUse cardDB (autoDrain cardDB s9) = s9 := by native_decide

-- failDraw after second draw pair
theorem hs12x : step cardDB s11x .failDraw = some s12x := by native_decide
theorem hs12y : step cardDB s11y .failDraw = some s12y := by native_decide

-- discard c3 (Reflex+)
theorem hs13x : step cardDB s12x (.discard 3) = some s13x := by native_decide
theorem hs13y : step cardDB s12y (.discard 3) = some s13y := by native_decide

-- failDraw final → resolveInUse
private def s15x_raw : GameState := { s14x with actionQueue := [] }
private def s15y_raw : GameState := { s14y with actionQueue := [] }
theorem hs15x : step cardDB s14x .failDraw = some s15x_raw := by native_decide
theorem hs15y : step cardDB s14y .failDraw = some s15y_raw := by native_decide

-- ============================================================
-- CLEANUP LEMMAS
-- ============================================================

theorem hc_stateA : resolveInUse cardDB (autoDrain cardDB stateA) = stateA := by native_decide
theorem hc3a : resolveInUse cardDB (autoDrain cardDB s3a) = s3ar := by native_decide
theorem hc3b : resolveInUse cardDB (autoDrain cardDB s3b) = s3br := by native_decide
theorem hc4a : resolveInUse cardDB (autoDrain cardDB s4a) = s4a := by native_decide
theorem hc4b : resolveInUse cardDB (autoDrain cardDB s4b) = s4b := by native_decide
theorem hc5a : resolveInUse cardDB (autoDrain cardDB s5a) = s5a := by native_decide
theorem hc5b : resolveInUse cardDB (autoDrain cardDB s5b) = s5b := by native_decide
theorem hc6a : resolveInUse cardDB (autoDrain cardDB s6a) = s6a := by native_decide
theorem hc6b : resolveInUse cardDB (autoDrain cardDB s6b) = s6b := by native_decide
theorem hc7a : resolveInUse cardDB (autoDrain cardDB s7a) = s7a := by native_decide
theorem hc7b : resolveInUse cardDB (autoDrain cardDB s7b) = s7b := by native_decide
theorem hc10x : resolveInUse cardDB (autoDrain cardDB s10x) = s10x := by native_decide
theorem hc10y : resolveInUse cardDB (autoDrain cardDB s10y) = s10y := by native_decide
theorem hc11x : resolveInUse cardDB (autoDrain cardDB s11x) = s11x := by native_decide
theorem hc11y : resolveInUse cardDB (autoDrain cardDB s11y) = s11y := by native_decide
theorem hc12x : resolveInUse cardDB (autoDrain cardDB s12x) = s12x := by native_decide
theorem hc12y : resolveInUse cardDB (autoDrain cardDB s12y) = s12y := by native_decide
theorem hc13x : resolveInUse cardDB (autoDrain cardDB s13x) = s13x := by native_decide
theorem hc13y : resolveInUse cardDB (autoDrain cardDB s13y) = s13y := by native_decide
theorem hc14x : resolveInUse cardDB (autoDrain cardDB s14x) = s14x := by native_decide
theorem hc14y : resolveInUse cardDB (autoDrain cardDB s14y) = s14y := by native_decide
theorem hc15x : resolveInUse cardDB (autoDrain cardDB s15x_raw) = stateBx := by native_decide
theorem hc15y : resolveInUse cardDB (autoDrain cardDB s15y_raw) = stateBy := by native_decide

-- ============================================================
-- ORACLE-DEPENDENT DRAW THEOREMS
-- ============================================================

-- Shuffle 0: draw from [ci6, ci1]
theorem hd3a (oracle : ShuffleOracle) (h : oracle 0 [ci6, ci1] = [ci1, ci6]) :
    drawCardL2 oracle 0 s2 1 = some (s3a, 1) := by
  unfold drawCardL2; simp only [s2, ci6, ci1] at h ⊢; rw [h]; native_decide

theorem hd3b (oracle : ShuffleOracle) (h : oracle 0 [ci6, ci1] = [ci6, ci1]) :
    drawCardL2 oracle 0 s2 6 = some (s3b, 1) := by
  unfold drawCardL2; simp only [s2, ci6, ci1] at h ⊢; rw [h]; native_decide

-- Draw d0b (from drawPile, no shuffle)
theorem hd5a (oracle : ShuffleOracle) :
    drawCardL2 oracle 1 s4a 6 = some (s5a, 1) := rfl
theorem hd5b (oracle : ShuffleOracle) :
    drawCardL2 oracle 1 s4b 1 = some (s5b, 1) := rfl

-- Shuffle 1: singleton [ci10]
theorem hd6a (oracle : ShuffleOracle) (hv : validOracle oracle) :
    drawCardL2 oracle 1 s5a 10 = some (s6a, 2) := by
  have hp := perm_one_ci ci10 _ (hv 1 [ci10])
  unfold drawCardL2; simp only [s5a, s4a, ci10] at hp ⊢; rw [hp]; native_decide

theorem hd6b (oracle : ShuffleOracle) (hv : validOracle oracle) :
    drawCardL2 oracle 1 s5b 10 = some (s6b, 2) := by
  have hp := perm_one_ci ci10 _ (hv 1 [ci10])
  unfold drawCardL2; simp only [s5b, s4b, ci10] at hp ⊢; rw [hp]; native_decide

-- Shuffle 2: [ci0, ci2]
theorem hd10x (oracle : ShuffleOracle) (h : oracle 2 [ci0, ci2] = [ci0, ci2]) :
    drawCardL2 oracle 2 s9 0 = some (s10x, 3) := by
  unfold drawCardL2; simp only [s9, ci0, ci2] at h ⊢; rw [h]; native_decide

theorem hd10y (oracle : ShuffleOracle) (h : oracle 2 [ci0, ci2] = [ci2, ci0]) :
    drawCardL2 oracle 2 s9 2 = some (s10y, 3) := by
  unfold drawCardL2; simp only [s9, ci0, ci2] at h ⊢; rw [h]; native_decide

-- Draw d2b (from drawPile, no shuffle)
theorem hd11x (oracle : ShuffleOracle) :
    drawCardL2 oracle 3 s10x 2 = some (s11x, 3) := rfl
theorem hd11y (oracle : ShuffleOracle) :
    drawCardL2 oracle 3 s10y 0 = some (s11y, 3) := rfl

-- Shuffle 3: singleton [ci3]
theorem hd14x (oracle : ShuffleOracle) (hv : validOracle oracle) :
    drawCardL2 oracle 3 s13x 3 = some (s14x, 4) := by
  have hp := perm_one_ci ci3 _ (hv 3 [ci3])
  unfold drawCardL2; simp only [s13x, ci3] at hp ⊢; rw [hp]; native_decide

theorem hd14y (oracle : ShuffleOracle) (hv : validOracle oracle) :
    drawCardL2 oracle 3 s13y 3 = some (s14y, 4) := by
  have hp := perm_one_ci ci3 _ (hv 3 [ci3])
  unfold drawCardL2; simp only [s13y, ci3] at hp ⊢; rw [hp]; native_decide

-- ============================================================
-- PER-CASE LOOP PROOFS
-- ============================================================

-- Case ax: oracle 0=[ci1,ci6], oracle 2=[ci0,ci2]
private theorem loop_ax (oracle : ShuffleOracle) (hv : validOracle oracle)
    (h0 : oracle 0 [ci6, ci1] = [ci1, ci6]) (h2 : oracle 2 [ci0, ci2] = [ci0, ci2]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateBx, 4) := by
  have htrace : mkLoopTrace oracle = [.play 6, .play 10, .draw 1, .play 0,
      .draw 6, .draw 10, .failDraw, .discard 2, .play 1,
      .draw 0, .draw 2, .failDraw, .discard 3, .draw 3, .failDraw] := by
    unfold mkLoopTrace; rw [h0, h2]; simp [ci0, ci1, ci2, ci3, ci6]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_draw (hd3a oracle h0))]
  rw [exL2_cons hc3a (sL2_step (by intro c; simp) hs4a)]
  rw [exL2_cons hc4a (sL2_draw (hd5a oracle))]
  rw [exL2_cons hc5a (sL2_draw (hd6a oracle hv))]
  rw [exL2_cons hc6a (sL2_step (by intro c; simp) hs7a)]
  rw [exL2_cons hc7a (sL2_step (by intro c; simp) hs8a)]
  rw [exL2_cons hc8a (sL2_step (by intro c; simp) hs9a)]
  rw [exL2_cons hc9 (sL2_draw (hd10x oracle h2))]
  rw [exL2_cons hc10x (sL2_draw (hd11x oracle))]
  rw [exL2_cons hc11x (sL2_step (by intro c; simp) hs12x)]
  rw [exL2_cons hc12x (sL2_step (by intro c; simp) hs13x)]
  rw [exL2_cons hc13x (sL2_draw (hd14x oracle hv))]
  rw [exL2_cons hc14x (sL2_step (by intro c; simp) hs15x)]
  simp only [executeL2, hc15x]

private theorem loop_ay (oracle : ShuffleOracle) (hv : validOracle oracle)
    (h0 : oracle 0 [ci6, ci1] = [ci1, ci6]) (h2 : oracle 2 [ci0, ci2] = [ci2, ci0]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateBy, 4) := by
  have htrace : mkLoopTrace oracle = [.play 6, .play 10, .draw 1, .play 0,
      .draw 6, .draw 10, .failDraw, .discard 2, .play 1,
      .draw 2, .draw 0, .failDraw, .discard 3, .draw 3, .failDraw] := by
    unfold mkLoopTrace; rw [h0, h2]; simp [ci0, ci1, ci2, ci3, ci6]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_draw (hd3a oracle h0))]
  rw [exL2_cons hc3a (sL2_step (by intro c; simp) hs4a)]
  rw [exL2_cons hc4a (sL2_draw (hd5a oracle))]
  rw [exL2_cons hc5a (sL2_draw (hd6a oracle hv))]
  rw [exL2_cons hc6a (sL2_step (by intro c; simp) hs7a)]
  rw [exL2_cons hc7a (sL2_step (by intro c; simp) hs8a)]
  rw [exL2_cons hc8a (sL2_step (by intro c; simp) hs9a)]
  rw [exL2_cons hc9 (sL2_draw (hd10y oracle h2))]
  rw [exL2_cons hc10y (sL2_draw (hd11y oracle))]
  rw [exL2_cons hc11y (sL2_step (by intro c; simp) hs12y)]
  rw [exL2_cons hc12y (sL2_step (by intro c; simp) hs13y)]
  rw [exL2_cons hc13y (sL2_draw (hd14y oracle hv))]
  rw [exL2_cons hc14y (sL2_step (by intro c; simp) hs15y)]
  simp only [executeL2, hc15y]

private theorem loop_bx (oracle : ShuffleOracle) (hv : validOracle oracle)
    (h0 : oracle 0 [ci6, ci1] = [ci6, ci1]) (h2 : oracle 2 [ci0, ci2] = [ci0, ci2]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateBx, 4) := by
  have htrace : mkLoopTrace oracle = [.play 6, .play 10, .draw 6, .play 0,
      .draw 1, .draw 10, .failDraw, .discard 2, .play 1,
      .draw 0, .draw 2, .failDraw, .discard 3, .draw 3, .failDraw] := by
    unfold mkLoopTrace; rw [h0, h2]; simp [ci0, ci1, ci2, ci3, ci6]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_draw (hd3b oracle h0))]
  rw [exL2_cons hc3b (sL2_step (by intro c; simp) hs4b)]
  rw [exL2_cons hc4b (sL2_draw (hd5b oracle))]
  rw [exL2_cons hc5b (sL2_draw (hd6b oracle hv))]
  rw [exL2_cons hc6b (sL2_step (by intro c; simp) hs7b)]
  rw [exL2_cons hc7b (sL2_step (by intro c; simp) hs8b)]
  rw [exL2_cons hc8b (sL2_step (by intro c; simp) hs9b)]
  rw [exL2_cons hc9 (sL2_draw (hd10x oracle h2))]
  rw [exL2_cons hc10x (sL2_draw (hd11x oracle))]
  rw [exL2_cons hc11x (sL2_step (by intro c; simp) hs12x)]
  rw [exL2_cons hc12x (sL2_step (by intro c; simp) hs13x)]
  rw [exL2_cons hc13x (sL2_draw (hd14x oracle hv))]
  rw [exL2_cons hc14x (sL2_step (by intro c; simp) hs15x)]
  simp only [executeL2, hc15x]

private theorem loop_by (oracle : ShuffleOracle) (hv : validOracle oracle)
    (h0 : oracle 0 [ci6, ci1] = [ci6, ci1]) (h2 : oracle 2 [ci0, ci2] = [ci2, ci0]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateBy, 4) := by
  have htrace : mkLoopTrace oracle = [.play 6, .play 10, .draw 6, .play 0,
      .draw 1, .draw 10, .failDraw, .discard 2, .play 1,
      .draw 2, .draw 0, .failDraw, .discard 3, .draw 3, .failDraw] := by
    unfold mkLoopTrace; rw [h0, h2]; simp [ci0, ci1, ci2, ci3, ci6]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_draw (hd3b oracle h0))]
  rw [exL2_cons hc3b (sL2_step (by intro c; simp) hs4b)]
  rw [exL2_cons hc4b (sL2_draw (hd5b oracle))]
  rw [exL2_cons hc5b (sL2_draw (hd6b oracle hv))]
  rw [exL2_cons hc6b (sL2_step (by intro c; simp) hs7b)]
  rw [exL2_cons hc7b (sL2_step (by intro c; simp) hs8b)]
  rw [exL2_cons hc8b (sL2_step (by intro c; simp) hs9b)]
  rw [exL2_cons hc9 (sL2_draw (hd10y oracle h2))]
  rw [exL2_cons hc10y (sL2_draw (hd11y oracle))]
  rw [exL2_cons hc11y (sL2_step (by intro c; simp) hs12y)]
  rw [exL2_cons hc12y (sL2_step (by intro c; simp) hs13y)]
  rw [exL2_cons hc13y (sL2_draw (hd14y oracle hv))]
  rw [exL2_cons hc14y (sL2_step (by intro c; simp) hs15y)]
  simp only [executeL2, hc15y]

-- ============================================================
-- MAIN THEOREM
-- ============================================================

theorem ComboAcrobaticsTactician_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hvalid
  have hp0 := hvalid 0 [ci6, ci1]
  have hp2 := hvalid 2 [ci0, ci2]
  have h61 := perm_2_ci (oracle 0 [ci6, ci1]) ci6 ci1 (by decide) hp0
  have h02 := perm_2_ci (oracle 2 [ci0, ci2]) ci0 ci2 (by decide) hp2
  rcases h61 with h0 | h0 <;> rcases h02 with h2 | h2
  · exact ⟨mkLoopTrace oracle, stateBx, 4, loop_bx oracle hvalid h0 h2, noEndTurn_bx1 oracle h0 h2, same_mod_x, dealt_dmg_x⟩
  · exact ⟨mkLoopTrace oracle, stateBy, 4, loop_by oracle hvalid h0 h2, noEndTurn_by1 oracle h0 h2, same_mod_y, dealt_dmg_y⟩
  · exact ⟨mkLoopTrace oracle, stateBx, 4, loop_ax oracle hvalid h0 h2, noEndTurn_ax1 oracle h0 h2, same_mod_x, dealt_dmg_x⟩
  · exact ⟨mkLoopTrace oracle, stateBy, 4, loop_ay oracle hvalid h0 h2, noEndTurn_ay1 oracle h0 h2, same_mod_y, dealt_dmg_y⟩

end ComboAcrobaticsTactician_L2
