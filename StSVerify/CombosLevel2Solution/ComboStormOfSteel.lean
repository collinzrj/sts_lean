/-
  Storm of Steel+ + Tactician+ + Reflex+ + Prepared+ (4 cards) - Level 2
  8 damage per loop (2 Shivs x 4 damage)

  v2 engine: CardInstance piles, sameModAccum, executeL2 with ShuffleOracle.

  Prepared+ now does draw 2, discard 2.

  Shuffle points in loop:
    0: discardPile = [SoS+(0)]              — singleton, deterministic
    1: discardPile = [Tact+(1), Reflex+(2)] — 2! = 2 perms
    2: discardPile = 3 cards (order depends on path) — 3! = 6 perms
  All permutations draw the same 3 cards; plays use findById so order is irrelevant.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboStormOfSteel_L2

-- ============================================================
-- CARD INSTANCES
-- ============================================================

private def ci0 : CardInstance := { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }
private def ci1 : CardInstance := { id := 1, name := TacticianPlus, cost := 0, damage := 0 }
private def ci2 : CardInstance := { id := 2, name := ReflexPlus, cost := 0, damage := 0 }
private def ci3 : CardInstance := { id := 3, name := PreparedPlus, cost := 0, damage := 0 }
private def shiv7 : CardInstance := { id := 7, name := Shiv, cost := 0, damage := 4 }
private def shiv8 : CardInstance := { id := 8, name := Shiv, cost := 0, damage := 4 }

-- ============================================================
-- DECK / ENEMY
-- ============================================================

def cards : List (CardName × Nat) := [
  (StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1), (PreparedPlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- ============================================================
-- SETUP
-- ============================================================

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .failDraw,
  .play 0,
  .draw 1, .draw 2, .draw 3,
  .play 4, .play 5, .play 6
]

private def exhaustBase : List CardInstance :=
  [{ id := 6, name := Shiv, cost := 0, damage := 4 },
   { id := 5, name := Shiv, cost := 0, damage := 4 },
   { id := 4, name := Shiv, cost := 0, damage := 4 }]

def stateA : GameState := {
  hand := [ci3, ci2, ci1]
  drawPile := []
  discardPile := [ci0]
  exhaustPile := exhaustBase
  inUse := []
  actionQueue := []
  energy := 4
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := []
  nextId := 7
  noDraw := false
  corruptionActive := false
}

-- ============================================================
-- LOOP TRACE
-- ============================================================

def mkLoopTrace (perm2 perm3 : List CardInstance) : List Action :=
  [.play 3, .draw 0, .failDraw, .discard 2, .discard 1] ++
  (perm2.map fun c => Action.draw c.id) ++
  [.failDraw, .play 0] ++
  (perm3.map fun c => Action.draw c.id) ++
  [.play 7, .play 8]

private def stateB_of (a b c : CardInstance) : GameState := {
  hand := [c, b, a]
  drawPile := []
  discardPile := [ci0]
  exhaustPile := [shiv8, shiv7] ++ exhaustBase
  inUse := []
  actionQueue := []
  energy := 7
  damage := 20
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := []
  nextId := 9
  noDraw := false
  corruptionActive := false
}

-- ============================================================
-- BASIC VERIFICATION
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- ============================================================
-- PERMUTATION ENUMERATION
-- ============================================================

private theorem perm_2_cases (l : List CardInstance) (hp : l.Perm [ci1, ci2]) :
    l = [ci1, ci2] ∨ l = [ci2, ci1] := by
  have hlen := hp.length_eq
  simp at hlen
  match l, hlen with
  | [x, y], _ =>
    have hx : x ∈ [ci1, ci2] := hp.mem_iff.mp (by simp)
    have hy : y ∈ [ci1, ci2] := hp.mem_iff.mp (by simp)
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals first
      | left; rfl
      | right; rfl
      | exact absurd hp (by decide)

private theorem perm_3_cases (l : List CardInstance) (hp : l.Perm [ci2, ci1, ci3]) :
    l = [ci2, ci1, ci3] ∨ l = [ci2, ci3, ci1] ∨ l = [ci1, ci2, ci3] ∨
    l = [ci1, ci3, ci2] ∨ l = [ci3, ci2, ci1] ∨ l = [ci3, ci1, ci2] := by
  have hlen := hp.length_eq
  simp at hlen
  match l, hlen with
  | [x, y, z], _ =>
    have hx : x ∈ [ci2, ci1, ci3] := hp.mem_iff.mp (by simp)
    have hy : y ∈ [ci2, ci1, ci3] := hp.mem_iff.mp (by simp)
    have hz : z ∈ [ci2, ci1, ci3] := hp.mem_iff.mp (by simp)
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy hz
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl
    all_goals first
      | left; rfl
      | right; left; rfl
      | right; right; left; rfl
      | right; right; right; left; rfl
      | right; right; right; right; left; rfl
      | right; right; right; right; right; rfl
      | exact absurd hp (by decide)

-- ============================================================
-- SINGLETON SHUFFLE LEMMA
-- ============================================================

private theorem perm_singleton_eq (a : CardInstance) (l : List CardInstance)
    (h : List.Perm l [a]) : l = [a] :=
  List.perm_singleton.mp h

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

-- After play Prepared+(3)
private def s1 : GameState := {
  hand := [ci2, ci1]
  drawPile := []
  discardPile := [ci0]
  exhaustPile := exhaustBase
  inUse := [ci3]
  actionQueue := [.draw, .draw, .discardChoice, .discardChoice]
  energy := 4
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 7
  noDraw := false
  corruptionActive := false
}

-- After draw SoS(0)
private def s2 : GameState := {
  hand := [ci0, ci2, ci1]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustBase
  inUse := [ci3]
  actionQueue := [.draw, .discardChoice, .discardChoice]
  energy := 4
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 7
  noDraw := false
  corruptionActive := false
}

-- After failDraw
private def s3 : GameState := { s2 with actionQueue := [.discardChoice, .discardChoice] }

-- After discard Reflex(2)
private def s4 : GameState := {
  hand := [ci0, ci1]
  drawPile := []
  discardPile := [ci2]
  exhaustPile := exhaustBase
  inUse := [ci3]
  actionQueue := [.discardChoice, .draw, .draw, .draw]
  energy := 4
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 7
  noDraw := false
  corruptionActive := false
}

-- After discard Tactician(1)
private def s4b : GameState := {
  hand := [ci0]
  drawPile := []
  discardPile := [ci1, ci2]
  exhaustPile := exhaustBase
  inUse := [ci3]
  actionQueue := [.draw, .draw, .draw]
  energy := 6
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 7
  noDraw := false
  corruptionActive := false
}

-- After first draw from 2-element shuffle
private def s5_2 (d e : CardInstance) : GameState := {
  hand := [d, ci0]
  drawPile := [e]
  discardPile := []
  exhaustPile := exhaustBase
  inUse := [ci3]
  actionQueue := [.draw, .draw]
  energy := 6
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 7
  noDraw := false
  corruptionActive := false
}

-- After second draw from 2-element shuffle
private def s5_3 (d e : CardInstance) : GameState := {
  hand := [e, d, ci0]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustBase
  inUse := [ci3]
  actionQueue := [.draw]
  energy := 6
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 7
  noDraw := false
  corruptionActive := false
}

-- After failDraw
private def s5_fd (d e : CardInstance) : GameState := { s5_3 d e with actionQueue := [] }

-- After cleanup: Prep+ from inUse to discard
private def s6 (d e : CardInstance) : GameState := {
  hand := [e, d, ci0]
  drawPile := []
  discardPile := [ci3]
  exhaustPile := exhaustBase
  inUse := []
  actionQueue := []
  energy := 6
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 7
  noDraw := false
  corruptionActive := false
}

-- After play SoS(0): RAW
private def s7_raw (d e : CardInstance) : GameState := {
  hand := [shiv7, shiv8, e, d]
  drawPile := []
  discardPile := [ci3]
  exhaustPile := exhaustBase
  inUse := [ci0]
  actionQueue := [.discardSpecific d.id, .discardSpecific e.id]
  energy := 5
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 9
  noDraw := false
  corruptionActive := false
}

-- Cleaned variant A (2-elem [ci1, ci2])
private def s7_cleanA : GameState := {
  hand := [shiv7, shiv8]
  drawPile := []
  discardPile := [ci2, ci1, ci3]
  exhaustPile := exhaustBase
  inUse := [ci0]
  actionQueue := [.draw, .draw, .draw]
  energy := 7
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 9
  noDraw := false
  corruptionActive := false
}

-- Cleaned variant B (2-elem [ci2, ci1])
private def s7_cleanB : GameState := {
  hand := [shiv7, shiv8]
  drawPile := []
  discardPile := [ci1, ci2, ci3]
  exhaustPile := exhaustBase
  inUse := [ci0]
  actionQueue := [.draw, .draw, .draw]
  energy := 7
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 9
  noDraw := false
  corruptionActive := false
}

-- After first draw from 3-element shuffle
private def s_d1 (a b c : CardInstance) : GameState := {
  hand := [a, shiv7, shiv8]
  drawPile := [b, c]
  discardPile := []
  exhaustPile := exhaustBase
  inUse := [ci0]
  actionQueue := [.draw, .draw]
  energy := 7
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 9
  noDraw := false
  corruptionActive := false
}

-- After second draw
private def s_d2 (a b c : CardInstance) : GameState := {
  hand := [b, a, shiv7, shiv8]
  drawPile := [c]
  discardPile := []
  exhaustPile := exhaustBase
  inUse := [ci0]
  actionQueue := [.draw]
  energy := 7
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 9
  noDraw := false
  corruptionActive := false
}

-- After third draw
private def s_d3 (a b c : CardInstance) : GameState := {
  hand := [c, b, a, shiv7, shiv8]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustBase
  inUse := [ci0]
  actionQueue := []
  energy := 7
  damage := 12
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 9
  noDraw := false
  corruptionActive := false
}

-- ============================================================
-- STEP LEMMAS (shared prefix)
-- ============================================================

private theorem hc_stateA : resolveInUse cardDB (autoDrain cardDB stateA) = stateA := by native_decide
private theorem hs_play_prep : step cardDB stateA (.play 3) = some s1 := by native_decide
private theorem hc_s1 : resolveInUse cardDB (autoDrain cardDB s1) = s1 := by native_decide

private theorem step_draw0 (oracle : ShuffleOracle) (hv : validOracle oracle) :
    drawCardL2 oracle 0 s1 0 = some (s2, 1) := by
  have hp : oracle 0 [ci0] = [ci0] := perm_singleton_eq ci0 _ (hv 0 [ci0])
  simp only [ci0] at hp
  unfold drawCardL2
  simp only [s1, s2, ci0, ci1, ci2, ci3]
  rw [hp]
  native_decide

private theorem hc_s2 : resolveInUse cardDB (autoDrain cardDB s2) = s2 := by native_decide
private theorem hs_failDraw1 : step cardDB s2 .failDraw = some s3 := by native_decide
private theorem hc_s3 : resolveInUse cardDB (autoDrain cardDB s3) = s3 := by native_decide
private theorem hs_discard2 : step cardDB s3 (.discard 2) = some s4 := by native_decide
private theorem hc_s4 : resolveInUse cardDB (autoDrain cardDB s4) = s4 := by native_decide
private theorem hs_discard1 : step cardDB s4 (.discard 1) = some s4b := by native_decide
private theorem hc_s4b : resolveInUse cardDB (autoDrain cardDB s4b) = s4b := by native_decide

-- ============================================================
-- 2-ELEMENT SHUFFLE DRAW LEMMAS
-- ============================================================

private theorem fd2_12 :
    drawCardL2 (fun _ _ => [ci1, ci2]) 1 s4b 1 = some (s5_2 ci1 ci2, 2) := by native_decide
private theorem fd2_21 :
    drawCardL2 (fun _ _ => [ci2, ci1]) 1 s4b 2 = some (s5_2 ci2 ci1, 2) := by native_decide

private theorem sd2_2elem (oracle : ShuffleOracle) (d e : CardInstance) :
    drawCardL2 oracle 2 (s5_2 d e) e.id = some (s5_3 d e, 2) := by
  simp [drawCardL2, s5_2, s5_3]

-- Concrete versions for matching literal action ids
private theorem sd2_2elem_12 (oracle : ShuffleOracle) :
    drawCardL2 oracle 2 (s5_2 ci1 ci2) 2 = some (s5_3 ci1 ci2, 2) := sd2_2elem oracle ci1 ci2
private theorem sd2_2elem_21 (oracle : ShuffleOracle) :
    drawCardL2 oracle 2 (s5_2 ci2 ci1) 1 = some (s5_3 ci2 ci1, 2) := sd2_2elem oracle ci2 ci1

private theorem hc_s5_2 (d e : CardInstance) :
    resolveInUse cardDB (autoDrain cardDB (s5_2 d e)) = s5_2 d e := by
  simp [s5_2, autoDrain, resolveInUse]
private theorem hc_s5_3 (d e : CardInstance) :
    resolveInUse cardDB (autoDrain cardDB (s5_3 d e)) = s5_3 d e := by
  simp [s5_3, autoDrain, resolveInUse]

private theorem hs_failDraw2_12 : step cardDB (s5_3 ci1 ci2) .failDraw = some (s5_fd ci1 ci2) := by native_decide
private theorem hs_failDraw2_21 : step cardDB (s5_3 ci2 ci1) .failDraw = some (s5_fd ci2 ci1) := by native_decide

private theorem hc_s5_fd_12 : resolveInUse cardDB (autoDrain cardDB (s5_fd ci1 ci2)) = s6 ci1 ci2 := by native_decide
private theorem hc_s5_fd_21 : resolveInUse cardDB (autoDrain cardDB (s5_fd ci2 ci1)) = s6 ci2 ci1 := by native_decide

private theorem hs_play_storm_12 : step cardDB (s6 ci1 ci2) (.play 0) = some (s7_raw ci1 ci2) := by native_decide
private theorem hs_play_storm_21 : step cardDB (s6 ci2 ci1) (.play 0) = some (s7_raw ci2 ci1) := by native_decide

private theorem hc_s7_raw_A : resolveInUse cardDB (autoDrain cardDB (s7_raw ci1 ci2)) = s7_cleanA := by native_decide
private theorem hc_s7_raw_B : resolveInUse cardDB (autoDrain cardDB (s7_raw ci2 ci1)) = s7_cleanB := by native_decide

-- ============================================================
-- 3-ELEMENT SHUFFLE DRAW LEMMAS (variant A)
-- ============================================================

private theorem fdA_213 :
    drawCardL2 (fun _ _ => [ci2, ci1, ci3]) 2 s7_cleanA 2 = some (s_d1 ci2 ci1 ci3, 3) := by native_decide
private theorem fdA_231 :
    drawCardL2 (fun _ _ => [ci2, ci3, ci1]) 2 s7_cleanA 2 = some (s_d1 ci2 ci3 ci1, 3) := by native_decide
private theorem fdA_123 :
    drawCardL2 (fun _ _ => [ci1, ci2, ci3]) 2 s7_cleanA 1 = some (s_d1 ci1 ci2 ci3, 3) := by native_decide
private theorem fdA_132 :
    drawCardL2 (fun _ _ => [ci1, ci3, ci2]) 2 s7_cleanA 1 = some (s_d1 ci1 ci3 ci2, 3) := by native_decide
private theorem fdA_321 :
    drawCardL2 (fun _ _ => [ci3, ci2, ci1]) 2 s7_cleanA 3 = some (s_d1 ci3 ci2 ci1, 3) := by native_decide
private theorem fdA_312 :
    drawCardL2 (fun _ _ => [ci3, ci1, ci2]) 2 s7_cleanA 3 = some (s_d1 ci3 ci1 ci2, 3) := by native_decide

-- ============================================================
-- 3-ELEMENT SHUFFLE DRAW LEMMAS (variant B)
-- ============================================================

private theorem fdB_213 :
    drawCardL2 (fun _ _ => [ci2, ci1, ci3]) 2 s7_cleanB 2 = some (s_d1 ci2 ci1 ci3, 3) := by native_decide
private theorem fdB_231 :
    drawCardL2 (fun _ _ => [ci2, ci3, ci1]) 2 s7_cleanB 2 = some (s_d1 ci2 ci3 ci1, 3) := by native_decide
private theorem fdB_123 :
    drawCardL2 (fun _ _ => [ci1, ci2, ci3]) 2 s7_cleanB 1 = some (s_d1 ci1 ci2 ci3, 3) := by native_decide
private theorem fdB_132 :
    drawCardL2 (fun _ _ => [ci1, ci3, ci2]) 2 s7_cleanB 1 = some (s_d1 ci1 ci3 ci2, 3) := by native_decide
private theorem fdB_321 :
    drawCardL2 (fun _ _ => [ci3, ci2, ci1]) 2 s7_cleanB 3 = some (s_d1 ci3 ci2 ci1, 3) := by native_decide
private theorem fdB_312 :
    drawCardL2 (fun _ _ => [ci3, ci1, ci2]) 2 s7_cleanB 3 = some (s_d1 ci3 ci1 ci2, 3) := by native_decide

-- ============================================================
-- SHARED DRAW LEMMAS (2nd and 3rd from 3-elem, oracle-independent)
-- ============================================================

private theorem sd2_oracle (oracle : ShuffleOracle) (a b c : CardInstance) :
    drawCardL2 oracle 3 (s_d1 a b c) b.id = some (s_d2 a b c, 3) := by
  simp [drawCardL2, s_d1, s_d2]

private theorem sd3_oracle (oracle : ShuffleOracle) (a b c : CardInstance) :
    drawCardL2 oracle 3 (s_d2 a b c) c.id = some (s_d3 a b c, 3) := by
  simp [drawCardL2, s_d2, s_d3]

private theorem hc_d1 (a b c : CardInstance) :
    resolveInUse cardDB (autoDrain cardDB (s_d1 a b c)) = s_d1 a b c := by
  simp [s_d1, autoDrain, resolveInUse]
private theorem hc_d2 (a b c : CardInstance) :
    resolveInUse cardDB (autoDrain cardDB (s_d2 a b c)) = s_d2 a b c := by
  simp [s_d2, autoDrain, resolveInUse]

-- (hc_d3 lemmas not needed: executeL2 handles cleanup internally in tail lemmas)

-- ============================================================
-- TAIL VERIFICATION
-- ============================================================

private theorem tail_213 :
    executeL2 cardDB (fun _ _ => []) 3 (s_d3 ci2 ci1 ci3)
      [.play 7, .play 8] = some (stateB_of ci2 ci1 ci3, 3) := by native_decide
private theorem tail_231 :
    executeL2 cardDB (fun _ _ => []) 3 (s_d3 ci2 ci3 ci1)
      [.play 7, .play 8] = some (stateB_of ci2 ci3 ci1, 3) := by native_decide
private theorem tail_123 :
    executeL2 cardDB (fun _ _ => []) 3 (s_d3 ci1 ci2 ci3)
      [.play 7, .play 8] = some (stateB_of ci1 ci2 ci3, 3) := by native_decide
private theorem tail_132 :
    executeL2 cardDB (fun _ _ => []) 3 (s_d3 ci1 ci3 ci2)
      [.play 7, .play 8] = some (stateB_of ci1 ci3 ci2, 3) := by native_decide
private theorem tail_321 :
    executeL2 cardDB (fun _ _ => []) 3 (s_d3 ci3 ci2 ci1)
      [.play 7, .play 8] = some (stateB_of ci3 ci2 ci1, 3) := by native_decide
private theorem tail_312 :
    executeL2 cardDB (fun _ _ => []) 3 (s_d3 ci3 ci1 ci2)
      [.play 7, .play 8] = some (stateB_of ci3 ci1 ci2, 3) := by native_decide

private theorem tail_oracle_indep (o1 o2 : ShuffleOracle) (idx : Nat) (s : GameState) :
    executeL2 cardDB o1 idx s [.play 7, .play 8] =
    executeL2 cardDB o2 idx s [.play 7, .play 8] := by
  simp only [executeL2, stepL2]

-- ============================================================
-- sameModAccum and dealtDamage
-- ============================================================

private theorem sm_213 : sameModAccum stateA (stateB_of ci2 ci1 ci3) = true := by native_decide
private theorem sm_231 : sameModAccum stateA (stateB_of ci2 ci3 ci1) = true := by native_decide
private theorem sm_123 : sameModAccum stateA (stateB_of ci1 ci2 ci3) = true := by native_decide
private theorem sm_132 : sameModAccum stateA (stateB_of ci1 ci3 ci2) = true := by native_decide
private theorem sm_321 : sameModAccum stateA (stateB_of ci3 ci2 ci1) = true := by native_decide
private theorem sm_312 : sameModAccum stateA (stateB_of ci3 ci1 ci2) = true := by native_decide

private theorem dd_213 : dealtDamage stateA (stateB_of ci2 ci1 ci3) = true := by native_decide
private theorem dd_231 : dealtDamage stateA (stateB_of ci2 ci3 ci1) = true := by native_decide
private theorem dd_123 : dealtDamage stateA (stateB_of ci1 ci2 ci3) = true := by native_decide
private theorem dd_132 : dealtDamage stateA (stateB_of ci1 ci3 ci2) = true := by native_decide
private theorem dd_321 : dealtDamage stateA (stateB_of ci3 ci2 ci1) = true := by native_decide
private theorem dd_312 : dealtDamage stateA (stateB_of ci3 ci1 ci2) = true := by native_decide

private theorem noEndTurn_draw_map (l : List CardInstance) :
    noEndTurn (List.map (fun c => Action.draw c.id) l) = true := by
  induction l with
  | nil => simp [noEndTurn]
  | cons _ _ ih => simp [List.map, noEndTurn, ih]

private theorem noEndTurn_append (l1 l2 : List Action)
    (h1 : noEndTurn l1 = true) (h2 : noEndTurn l2 = true) :
    noEndTurn (l1 ++ l2) = true := by
  induction l1 with
  | nil => exact h2
  | cons a rest ih =>
    simp [List.cons_append, noEndTurn]
    cases a <;> simp [noEndTurn] at h1 ⊢ <;> exact ih h1

private theorem noEndTurn_mkLoopTrace (p2 p3 : List CardInstance) :
    noEndTurn (mkLoopTrace p2 p3) = true := by
  unfold mkLoopTrace
  apply noEndTurn_append
  · apply noEndTurn_append
    · apply noEndTurn_append
      · apply noEndTurn_append
        · native_decide
        · exact noEndTurn_draw_map p2
      · native_decide
    · exact noEndTurn_draw_map p3
  · native_decide

-- ============================================================
-- PER-CASE LOOP PROOF (variant A: 2-elem perm [ci1, ci2])
-- ============================================================

private theorem loop_caseA (oracle : ShuffleOracle) (hv : validOracle oracle)
    (a b c : CardInstance)
    (h2 : oracle 1 [ci1, ci2] = [ci1, ci2])
    (h3 : oracle 2 [ci2, ci1, ci3] = [a, b, c])
    (h_fd3 : drawCardL2 (fun _ _ => [a, b, c]) 2 s7_cleanA a.id = some (s_d1 a b c, 3))
    (h_tail : executeL2 cardDB (fun _ _ => []) 3 (s_d3 a b c)
      [.play 7, .play 8] = some (stateB_of a b c, 3)) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace [ci1, ci2] [a, b, c]) = some (stateB_of a b c, 3) := by
  show executeL2 cardDB oracle 0 stateA
    ([.play 3, .draw 0, .failDraw, .discard 2, .discard 1,
      .draw 1, .draw 2, .failDraw, .play 0,
      .draw a.id, .draw b.id, .draw c.id,
      .play 7, .play 8]) = some (stateB_of a b c, 3)
  -- play Prepared+(3)
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs_play_prep)]
  -- draw SoS(0)
  rw [exL2_cons hc_s1 (sL2_draw (step_draw0 oracle hv))]
  -- failDraw
  rw [exL2_cons hc_s2 (sL2_step (by intro c; simp) hs_failDraw1)]
  -- discard Reflex(2)
  rw [exL2_cons hc_s3 (sL2_step (by intro c; simp) hs_discard2)]
  -- discard Tactician(1)
  rw [exL2_cons hc_s4 (sL2_step (by intro c; simp) hs_discard1)]
  -- draw ci1: 2-element shuffle
  have h2' := h2; simp only [ci1, ci2] at h2'
  have hd_d : drawCardL2 oracle 1 s4b 1 = some (s5_2 ci1 ci2, 2) := by
    unfold drawCardL2
    simp only [s4b, ci0, ci1, ci2, ci3]
    rw [h2']; exact fd2_12 ▸ rfl
  rw [exL2_cons hc_s4b (sL2_draw hd_d)]
  -- draw ci2: drawPile non-empty
  rw [exL2_cons (hc_s5_2 ci1 ci2) (sL2_draw (sd2_2elem_12 oracle))]
  -- failDraw
  rw [exL2_cons (hc_s5_3 ci1 ci2) (sL2_step (by intro c; simp) hs_failDraw2_12)]
  -- play SoS(0)
  rw [exL2_cons hc_s5_fd_12 (sL2_step (by intro c; simp) hs_play_storm_12)]
  -- draw a: 3-element shuffle
  have h3' := h3; simp only [ci1, ci2, ci3] at h3'
  have hd_a : drawCardL2 oracle 2 s7_cleanA a.id = some (s_d1 a b c, 3) := by
    unfold drawCardL2
    simp only [s7_cleanA, ci0, ci1, ci2, ci3]
    rw [h3']; exact h_fd3 ▸ rfl
  rw [exL2_cons hc_s7_raw_A (sL2_draw hd_a)]
  -- draw b
  rw [exL2_cons (hc_d1 a b c) (sL2_draw (sd2_oracle oracle a b c))]
  -- draw c
  rw [exL2_cons (hc_d2 a b c) (sL2_draw (sd3_oracle oracle a b c))]
  -- play Shiv7, play Shiv8
  rw [tail_oracle_indep oracle (fun _ _ => []) 3 (s_d3 a b c)]
  exact h_tail

-- ============================================================
-- PER-CASE LOOP PROOF (variant B: 2-elem perm [ci2, ci1])
-- ============================================================

private theorem loop_caseB (oracle : ShuffleOracle) (hv : validOracle oracle)
    (a b c : CardInstance)
    (h2 : oracle 1 [ci1, ci2] = [ci2, ci1])
    (h3 : oracle 2 [ci1, ci2, ci3] = [a, b, c])
    (h_fd3 : drawCardL2 (fun _ _ => [a, b, c]) 2 s7_cleanB a.id = some (s_d1 a b c, 3))
    (h_tail : executeL2 cardDB (fun _ _ => []) 3 (s_d3 a b c)
      [.play 7, .play 8] = some (stateB_of a b c, 3)) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace [ci2, ci1] [a, b, c]) = some (stateB_of a b c, 3) := by
  show executeL2 cardDB oracle 0 stateA
    ([.play 3, .draw 0, .failDraw, .discard 2, .discard 1,
      .draw 2, .draw 1, .failDraw, .play 0,
      .draw a.id, .draw b.id, .draw c.id,
      .play 7, .play 8]) = some (stateB_of a b c, 3)
  -- play Prepared+(3)
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs_play_prep)]
  -- draw SoS(0)
  rw [exL2_cons hc_s1 (sL2_draw (step_draw0 oracle hv))]
  -- failDraw
  rw [exL2_cons hc_s2 (sL2_step (by intro c; simp) hs_failDraw1)]
  -- discard Reflex(2)
  rw [exL2_cons hc_s3 (sL2_step (by intro c; simp) hs_discard2)]
  -- discard Tactician(1)
  rw [exL2_cons hc_s4 (sL2_step (by intro c; simp) hs_discard1)]
  -- draw ci2: 2-element shuffle
  have h2' := h2; simp only [ci1, ci2] at h2'
  have hd_d : drawCardL2 oracle 1 s4b 2 = some (s5_2 ci2 ci1, 2) := by
    unfold drawCardL2
    simp only [s4b, ci0, ci1, ci2, ci3]
    rw [h2']; exact fd2_21 ▸ rfl
  rw [exL2_cons hc_s4b (sL2_draw hd_d)]
  -- draw ci1: drawPile non-empty
  rw [exL2_cons (hc_s5_2 ci2 ci1) (sL2_draw (sd2_2elem_21 oracle))]
  -- failDraw
  rw [exL2_cons (hc_s5_3 ci2 ci1) (sL2_step (by intro c; simp) hs_failDraw2_21)]
  -- play SoS(0)
  rw [exL2_cons hc_s5_fd_21 (sL2_step (by intro c; simp) hs_play_storm_21)]
  -- draw a: 3-element shuffle
  have h3' := h3; simp only [ci1, ci2, ci3] at h3'
  have hd_a : drawCardL2 oracle 2 s7_cleanB a.id = some (s_d1 a b c, 3) := by
    unfold drawCardL2
    simp only [s7_cleanB, ci0, ci1, ci2, ci3]
    rw [h3']; exact h_fd3 ▸ rfl
  rw [exL2_cons hc_s7_raw_B (sL2_draw hd_a)]
  -- draw b
  rw [exL2_cons (hc_d1 a b c) (sL2_draw (sd2_oracle oracle a b c))]
  -- draw c
  rw [exL2_cons (hc_d2 a b c) (sL2_draw (sd3_oracle oracle a b c))]
  -- play Shiv7, play Shiv8
  rw [tail_oracle_indep oracle (fun _ _ => []) 3 (s_d3 a b c)]
  exact h_tail

-- ============================================================
-- MAIN THEOREM
-- ============================================================

theorem ComboStormOfSteel_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle h_valid
  -- 2-element shuffle at index 1
  have h_perm2 := h_valid 1 [ci1, ci2]
  have h_cases2 := perm_2_cases (oracle 1 [ci1, ci2]) h_perm2
  rcases h_cases2 with h2 | h2
  · -- Case A: oracle 1 [ci1, ci2] = [ci1, ci2]
    have h_perm3 := h_valid 2 [ci2, ci1, ci3]
    have h_cases3 := perm_3_cases (oracle 2 [ci2, ci1, ci3]) h_perm3
    rcases h_cases3 with h3 | h3 | h3 | h3 | h3 | h3
    · exact ⟨_, _, _, loop_caseA oracle h_valid ci2 ci1 ci3 h2 h3 fdA_213 tail_213, noEndTurn_mkLoopTrace _ _, sm_213, dd_213⟩
    · exact ⟨_, _, _, loop_caseA oracle h_valid ci2 ci3 ci1 h2 h3 fdA_231 tail_231, noEndTurn_mkLoopTrace _ _, sm_231, dd_231⟩
    · exact ⟨_, _, _, loop_caseA oracle h_valid ci1 ci2 ci3 h2 h3 fdA_123 tail_123, noEndTurn_mkLoopTrace _ _, sm_123, dd_123⟩
    · exact ⟨_, _, _, loop_caseA oracle h_valid ci1 ci3 ci2 h2 h3 fdA_132 tail_132, noEndTurn_mkLoopTrace _ _, sm_132, dd_132⟩
    · exact ⟨_, _, _, loop_caseA oracle h_valid ci3 ci2 ci1 h2 h3 fdA_321 tail_321, noEndTurn_mkLoopTrace _ _, sm_321, dd_321⟩
    · exact ⟨_, _, _, loop_caseA oracle h_valid ci3 ci1 ci2 h2 h3 fdA_312 tail_312, noEndTurn_mkLoopTrace _ _, sm_312, dd_312⟩
  · -- Case B: oracle 1 [ci1, ci2] = [ci2, ci1]
    have h_perm3 : (oracle 2 [ci1, ci2, ci3]).Perm [ci2, ci1, ci3] :=
      (h_valid 2 [ci1, ci2, ci3]).trans (by decide)
    have h_cases3 := perm_3_cases (oracle 2 [ci1, ci2, ci3]) h_perm3
    rcases h_cases3 with h3 | h3 | h3 | h3 | h3 | h3
    · exact ⟨_, _, _, loop_caseB oracle h_valid ci2 ci1 ci3 h2 h3 fdB_213 tail_213, noEndTurn_mkLoopTrace _ _, sm_213, dd_213⟩
    · exact ⟨_, _, _, loop_caseB oracle h_valid ci2 ci3 ci1 h2 h3 fdB_231 tail_231, noEndTurn_mkLoopTrace _ _, sm_231, dd_231⟩
    · exact ⟨_, _, _, loop_caseB oracle h_valid ci1 ci2 ci3 h2 h3 fdB_123 tail_123, noEndTurn_mkLoopTrace _ _, sm_123, dd_123⟩
    · exact ⟨_, _, _, loop_caseB oracle h_valid ci1 ci3 ci2 h2 h3 fdB_132 tail_132, noEndTurn_mkLoopTrace _ _, sm_132, dd_132⟩
    · exact ⟨_, _, _, loop_caseB oracle h_valid ci3 ci2 ci1 h2 h3 fdB_321 tail_321, noEndTurn_mkLoopTrace _ _, sm_321, dd_321⟩
    · exact ⟨_, _, _, loop_caseB oracle h_valid ci3 ci1 ci2 h2 h3 fdB_312 tail_312, noEndTurn_mkLoopTrace _ _, sm_312, dd_312⟩

end ComboStormOfSteel_L2
