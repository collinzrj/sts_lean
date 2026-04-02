/-
  Storm of Steel+ + Tactician+ + Reflex+ + Prepared+ (4 cards) - Level 2
  8 damage per loop (2 Shivs x 4 damage)

  v2 engine: CardInstance piles, sameModAccum, executeL2 with ShuffleOracle.

  Shuffle points in loop:
    0: discardPile = [SoS+(0)]          — singleton, deterministic
    1: discardPile = [Reflex+(2)]       — singleton, deterministic
    2: discardPile = [Reflex+(2), Tactician+(1), Prepared+(3)] — 3! = 6 perms
  All 6 permutations draw the same 3 cards; plays use findById so order is irrelevant.
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
-- LOOP TRACE (parameterized by the 3-card permutation at shuffle point 2)
-- ============================================================

def mkLoopTrace (perm : List CardInstance) : List Action :=
  [.play 3, .draw 0, .failDraw, .discard 2, .draw 2, .failDraw, .play 0] ++
  (perm.map fun c => Action.draw c.id) ++
  [.play 7, .play 8]

-- Final state: hand order depends on permutation
private def stateB_of (a b c : CardInstance) : GameState := {
  hand := [c, b, a]
  drawPile := []
  discardPile := [ci0]
  exhaustPile := [shiv8, shiv7] ++ exhaustBase
  inUse := []
  actionQueue := []
  energy := 5
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
-- PERMUTATION ENUMERATION (3-element)
-- ============================================================

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
-- All states here are RAW outputs of step (NOT cleaned),
-- except those marked as "cleaned" which are outputs of resolveInUse∘autoDrain.
-- The hc_* lemmas handle the cleanup transitions.
-- ============================================================

-- After play Prepared+(3): raw step output
private def s1 : GameState := {
  hand := [ci2, ci1]
  drawPile := []
  discardPile := [ci0]
  exhaustPile := exhaustBase
  inUse := [ci3]
  actionQueue := [.draw, .draw, .discardChoice]
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

-- After draw SoS(0): raw drawCardL2 output
private def s2 : GameState := {
  hand := [ci0, ci2, ci1]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustBase
  inUse := [ci3]
  actionQueue := [.draw, .discardChoice]
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

-- After failDraw: drops consecutive draws, leaves discardChoice
private def s3 : GameState := { s2 with actionQueue := [.discardChoice] }

-- After discard Reflex(2): Reflex trigger adds 3 draws (bottom)
private def s4 : GameState := {
  hand := [ci0, ci1]
  drawPile := []
  discardPile := [ci2]
  exhaustPile := exhaustBase
  inUse := [ci3]
  actionQueue := [.draw, .draw, .draw]
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

-- After draw Reflex(2): raw drawCardL2 output
private def s5 : GameState := {
  hand := [ci2, ci0, ci1]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustBase
  inUse := [ci3]
  actionQueue := [.draw, .draw]
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

-- After failDraw from s5: actionQueue=[], inUse=[ci3]
private def s5_fd : GameState := { s5 with actionQueue := [] }

-- After cleanup(s5_fd): Prepared+ moves from inUse to discard
-- This is the cleaned state BEFORE play SoS
private def s6 : GameState := {
  hand := [ci2, ci0, ci1]
  drawPile := []
  discardPile := [ci3]
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
  enemy := enemy
  activePowers := []
  nextId := 7
  noDraw := false
  corruptionActive := false
}

-- After play SoS(0): RAW step output (before autoDrain)
-- Storm creates 2 Shivs in hand, enqueues discardSpecific for Tact+Reflex
private def s7_raw : GameState := {
  hand := [shiv7, shiv8, ci2, ci1]
  drawPile := []
  discardPile := [ci3]
  exhaustPile := exhaustBase
  inUse := [ci0]
  actionQueue := [.discardSpecific 1, .discardSpecific 2]
  energy := 3
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

-- After cleanup(s7_raw): autoDrain processes discards (Tact+2E, Reflex+3draws),
-- resolveInUse does NOT fire (actionQueue non-empty after Reflex trigger)
-- Cleaned state for the draw step
private def s7_clean : GameState := {
  hand := [shiv7, shiv8]
  drawPile := []
  discardPile := [ci2, ci1, ci3]
  exhaustPile := exhaustBase
  inUse := [ci0]
  actionQueue := [.draw, .draw, .draw]
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

-- After first draw from 3-element shuffle
private def s_d1 (a b c : CardInstance) : GameState := {
  hand := [a, shiv7, shiv8]
  drawPile := [b, c]
  discardPile := []
  exhaustPile := exhaustBase
  inUse := [ci0]
  actionQueue := [.draw, .draw]
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

-- After second draw
private def s_d2 (a b c : CardInstance) : GameState := {
  hand := [b, a, shiv7, shiv8]
  drawPile := [c]
  discardPile := []
  exhaustPile := exhaustBase
  inUse := [ci0]
  actionQueue := [.draw]
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

-- After third draw: all 3 drawn, actionQueue=[], inUse=[ci0]
private def s_d3 (a b c : CardInstance) : GameState := {
  hand := [c, b, a, shiv7, shiv8]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustBase
  inUse := [ci0]
  actionQueue := []
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

-- After cleanup(s_d3): SoS goes to discard (resolveInUse)
private def s_resolved (a b c : CardInstance) : GameState := {
  hand := [c, b, a, shiv7, shiv8]
  drawPile := []
  discardPile := [ci0]
  exhaustPile := exhaustBase
  inUse := []
  actionQueue := []
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

-- ============================================================
-- STEP LEMMAS
-- ============================================================

private theorem hc_stateA : resolveInUse cardDB (autoDrain cardDB stateA) = stateA := by native_decide
private theorem hs_play_prep : step cardDB stateA (.play 3) = some s1 := by native_decide
private theorem hc_s1 : resolveInUse cardDB (autoDrain cardDB s1) = s1 := by native_decide

-- Draw SoS(0): singleton shuffle
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

-- Draw Reflex(2): singleton shuffle
private theorem step_draw2 (oracle : ShuffleOracle) (hv : validOracle oracle) :
    drawCardL2 oracle 1 s4 2 = some (s5, 2) := by
  have hp : oracle 1 [ci2] = [ci2] := perm_singleton_eq ci2 _ (hv 1 [ci2])
  simp only [ci2] at hp
  unfold drawCardL2
  simp only [s4, s5, ci0, ci1, ci2, ci3]
  rw [hp]
  native_decide

private theorem hc_s5 : resolveInUse cardDB (autoDrain cardDB s5) = s5 := by native_decide
private theorem hs_failDraw2 : step cardDB s5 .failDraw = some s5_fd := by native_decide
private theorem hc_s5_fd : resolveInUse cardDB (autoDrain cardDB s5_fd) = s6 := by native_decide
private theorem hs_play_storm : step cardDB s6 (.play 0) = some s7_raw := by native_decide
private theorem hc_s7_raw : resolveInUse cardDB (autoDrain cardDB s7_raw) = s7_clean := by native_decide

-- ============================================================
-- DRAW LEMMAS (3-element shuffle at index 2)
-- ============================================================

private theorem fd_213 :
    drawCardL2 (fun _ _ => [ci2, ci1, ci3]) 2 s7_clean 2 = some (s_d1 ci2 ci1 ci3, 3) := by
  native_decide
private theorem fd_231 :
    drawCardL2 (fun _ _ => [ci2, ci3, ci1]) 2 s7_clean 2 = some (s_d1 ci2 ci3 ci1, 3) := by
  native_decide
private theorem fd_123 :
    drawCardL2 (fun _ _ => [ci1, ci2, ci3]) 2 s7_clean 1 = some (s_d1 ci1 ci2 ci3, 3) := by
  native_decide
private theorem fd_132 :
    drawCardL2 (fun _ _ => [ci1, ci3, ci2]) 2 s7_clean 1 = some (s_d1 ci1 ci3 ci2, 3) := by
  native_decide
private theorem fd_321 :
    drawCardL2 (fun _ _ => [ci3, ci2, ci1]) 2 s7_clean 3 = some (s_d1 ci3 ci2 ci1, 3) := by
  native_decide
private theorem fd_312 :
    drawCardL2 (fun _ _ => [ci3, ci1, ci2]) 2 s7_clean 3 = some (s_d1 ci3 ci1 ci2, 3) := by
  native_decide

-- Second draw: drawPile non-empty → oracle-independent
private theorem sd2_oracle (oracle : ShuffleOracle) (a b c : CardInstance) :
    drawCardL2 oracle 3 (s_d1 a b c) b.id = some (s_d2 a b c, 3) := by
  simp [drawCardL2, s_d1, s_d2]

-- Third draw: drawPile non-empty → oracle-independent
private theorem sd3_oracle (oracle : ShuffleOracle) (a b c : CardInstance) :
    drawCardL2 oracle 3 (s_d2 a b c) c.id = some (s_d3 a b c, 3) := by
  simp [drawCardL2, s_d2, s_d3]

-- Cleanup lemmas for draw states (no discardSpecific, inUse non-empty but actionQueue non-empty)
private theorem hc_d1 (a b c : CardInstance) :
    resolveInUse cardDB (autoDrain cardDB (s_d1 a b c)) = s_d1 a b c := by
  simp [s_d1, autoDrain, resolveInUse]
private theorem hc_d2 (a b c : CardInstance) :
    resolveInUse cardDB (autoDrain cardDB (s_d2 a b c)) = s_d2 a b c := by
  simp [s_d2, autoDrain, resolveInUse]

-- After third draw: inUse=[ci0], actionQueue=[] → resolveInUse fires
private theorem hc_d3_213 :
    resolveInUse cardDB (autoDrain cardDB (s_d3 ci2 ci1 ci3)) = s_resolved ci2 ci1 ci3 := by
  native_decide
private theorem hc_d3_231 :
    resolveInUse cardDB (autoDrain cardDB (s_d3 ci2 ci3 ci1)) = s_resolved ci2 ci3 ci1 := by
  native_decide
private theorem hc_d3_123 :
    resolveInUse cardDB (autoDrain cardDB (s_d3 ci1 ci2 ci3)) = s_resolved ci1 ci2 ci3 := by
  native_decide
private theorem hc_d3_132 :
    resolveInUse cardDB (autoDrain cardDB (s_d3 ci1 ci3 ci2)) = s_resolved ci1 ci3 ci2 := by
  native_decide
private theorem hc_d3_321 :
    resolveInUse cardDB (autoDrain cardDB (s_d3 ci3 ci2 ci1)) = s_resolved ci3 ci2 ci1 := by
  native_decide
private theorem hc_d3_312 :
    resolveInUse cardDB (autoDrain cardDB (s_d3 ci3 ci1 ci2)) = s_resolved ci3 ci1 ci2 := by
  native_decide

-- ============================================================
-- TAIL VERIFICATION (play Shiv7, play Shiv8 — oracle independent)
-- ============================================================

-- Tail stated from s_d3 (executeL2 will cleanup via resolveInUse before each step)
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

-- Oracle independence for tail
private theorem tail_oracle_indep (o1 o2 : ShuffleOracle) (idx : Nat) (s : GameState) :
    executeL2 cardDB o1 idx s [.play 7, .play 8] =
    executeL2 cardDB o2 idx s [.play 7, .play 8] := by
  simp only [executeL2, stepL2]

-- sameModAccum and dealtDamage for each perm's final state
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

-- ============================================================
-- PER-CASE LOOP PROOF
-- ============================================================

private theorem loop_case (oracle : ShuffleOracle) (hv : validOracle oracle)
    (a b c : CardInstance)
    (h : oracle 2 [ci2, ci1, ci3] = [a, b, c])
    (h_fd : drawCardL2 (fun _ _ => [a, b, c]) 2 s7_clean a.id = some (s_d1 a b c, 3))
    (h_tail : executeL2 cardDB (fun _ _ => []) 3 (s_d3 a b c)
      [.play 7, .play 8] = some (stateB_of a b c, 3)) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace [a, b, c]) = some (stateB_of a b c, 3) := by
  show executeL2 cardDB oracle 0 stateA
    ([.play 3, .draw 0, .failDraw, .discard 2, .draw 2, .failDraw, .play 0,
      .draw a.id, .draw b.id, .draw c.id,
      .play 7, .play 8]) = some (stateB_of a b c, 3)
  -- play Prepared+(3)
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs_play_prep)]
  -- draw SoS(0) — singleton shuffle
  rw [exL2_cons hc_s1 (sL2_draw (step_draw0 oracle hv))]
  -- failDraw
  rw [exL2_cons hc_s2 (sL2_step (by intro c; simp) hs_failDraw1)]
  -- discard Reflex(2)
  rw [exL2_cons hc_s3 (sL2_step (by intro c; simp) hs_discard2)]
  -- draw Reflex(2) — singleton shuffle
  rw [exL2_cons hc_s4 (sL2_draw (step_draw2 oracle hv))]
  -- failDraw → s5_fd
  rw [exL2_cons hc_s5 (sL2_step (by intro c; simp) hs_failDraw2)]
  -- play SoS(0) → s7_raw (cleanup s5_fd → s6, then step s6 → s7_raw)
  rw [exL2_cons hc_s5_fd (sL2_step (by intro c; simp) hs_play_storm)]
  -- draw a: oracle-dependent, 3-element shuffle
  have hd_a : drawCardL2 oracle 2 s7_clean a.id = some (s_d1 a b c, 3) := by
    unfold drawCardL2
    simp only [s7_clean]
    rw [h]; exact h_fd ▸ rfl
  rw [exL2_cons hc_s7_raw (sL2_draw hd_a)]
  -- draw b (oracle-independent)
  rw [exL2_cons (hc_d1 a b c) (sL2_draw (sd2_oracle oracle a b c))]
  -- draw c (oracle-independent)
  rw [exL2_cons (hc_d2 a b c) (sL2_draw (sd3_oracle oracle a b c))]
  -- play Shiv7, play Shiv8 (oracle-independent, resolveInUse handled inside executeL2)
  rw [tail_oracle_indep oracle (fun _ _ => []) 3 (s_d3 a b c)]
  exact h_tail

-- ============================================================
-- MAIN THEOREM
-- ============================================================

theorem ComboStormOfSteel_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle h_valid
  have h_perm := h_valid 2 [ci2, ci1, ci3]
  have h_cases := perm_3_cases (oracle 2 [ci2, ci1, ci3]) h_perm
  rcases h_cases with h | h | h | h | h | h
  · exact ⟨_, _, _, loop_case oracle h_valid ci2 ci1 ci3 h fd_213 tail_213, sm_213, dd_213⟩
  · exact ⟨_, _, _, loop_case oracle h_valid ci2 ci3 ci1 h fd_231 tail_231, sm_231, dd_231⟩
  · exact ⟨_, _, _, loop_case oracle h_valid ci1 ci2 ci3 h fd_123 tail_123, sm_123, dd_123⟩
  · exact ⟨_, _, _, loop_case oracle h_valid ci1 ci3 ci2 h fd_132 tail_132, sm_132, dd_132⟩
  · exact ⟨_, _, _, loop_case oracle h_valid ci3 ci2 ci1 h fd_321 tail_321, sm_321, dd_321⟩
  · exact ⟨_, _, _, loop_case oracle h_valid ci3 ci1 ci2 h fd_312 tail_312, sm_312, dd_312⟩

end ComboStormOfSteel_L2
