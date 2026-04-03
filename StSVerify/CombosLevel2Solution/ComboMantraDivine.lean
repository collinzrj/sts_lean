/-
  観者 - 真言/神格混合無限 (Level 2)
  Cards: 12

  v2 engine: CardInstance piles, sameModAccum(stateA, stateB),
  execute cardDB, ShuffleOracle on List CardInstance, drawCardL2 top-card,
  resolveInUse instead of resolveLimbo.

  Shuffle point: discardPile = [ci3:Eruption+, ci8:Flurry+, ci4:InnerPeace]
  3! = 6 permutations. All draw the same 3 cards, and playCard uses findById,
  so all 6 cases produce the same final state.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboMantraDivine_L2

-- ============================================================
-- CARD INSTANCES
-- ============================================================

private def ci3  : CardInstance := { id := 3,  name := EruptionPlus,       cost := 1, damage := 9 }
private def ci4  : CardInstance := { id := 4,  name := InnerPeace,         cost := 1, damage := 0 }
private def ci8  : CardInstance := { id := 8,  name := FlurryOfBlowsPlus,  cost := 0, damage := 6 }

-- ============================================================
-- FRAMEWORK-GENERATED
-- ============================================================

def cards : List (CardName × Nat) :=
  [ (Rushdown, 2), (MentalFortressPlus, 1), (EruptionPlus, 1),
    (InnerPeace, 1), (PrayPlus, 1), (ProstatePlus, 1),
    (EmptyMindPlus, 1), (FlurryOfBlowsPlus, 1), (Scrawl, 1),
    (VaultPlus, 1), (DeusExMachina, 1), (OmnisciencePlus, 1) ]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- ============================================================
-- SETUP
-- ============================================================

def setupTrace : List Action := [
  .draw 9, .draw 0, .draw 1, .draw 10, .draw 11,
  .resolveDrawTrigger 11,
  .play 13, .play 14,
  .play 0, .play 1,
  .play 9,
  .draw 2, .draw 3, .draw 4, .draw 5,
  .draw 6, .draw 7, .draw 8, .draw 12,
  .failDraw,
  .play 2,
  .recycleChoose 5, .recycleChoose 7, .recycleChoose 6,
  .recycleChoose 12, .recycleChoose 10,
  .play 4,
  .play 8
]

def stateA : GameState := {
  hand := [ ci3 ]
  drawPile := []
  discardPile := [ ci8, ci4 ]
  exhaustPile := [ { id := 10, name := VaultPlus, cost := 2, damage := 0 },
                   { id := 12, name := OmnisciencePlus, cost := 3, damage := 0 },
                   { id := 6, name := ProstatePlus, cost := 0, damage := 0 },
                   { id := 7, name := EmptyMindPlus, cost := 1, damage := 0 },
                   { id := 5, name := PrayPlus, cost := 1, damage := 0 },
                   { id := 9, name := Scrawl, cost := 1, damage := 0 },
                   { id := 14, name := Miracle, cost := 0, damage := 0 },
                   { id := 13, name := Miracle, cost := 0, damage := 0 },
                   { id := 11, name := DeusExMachina, cost := 0, damage := 0 } ]
  inUse := []
  actionQueue := []
  energy := 7
  damage := 6
  block := 6
  stance := .Calm
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 15
  noDraw := false
  corruptionActive := false
}

def mkLoopTrace (perm : List CardInstance) : List Action :=
  [.play 3, .resolveRushdown, .autoPlayFlurry 8] ++
  (perm.map fun c => Action.draw c.id) ++
  [.failDraw, .play 8, .play 4, .autoPlayFlurry 8]

-- All 6 permutations produce the same stateB
def stateB : GameState := {
  hand := [ ci3 ]
  drawPile := []
  discardPile := [ ci4, ci8 ]
  exhaustPile := stateA.exhaustPile
  inUse := []
  actionQueue := []
  energy := 7
  damage := 45
  block := 18
  stance := .Calm
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 15
  noDraw := false
  corruptionActive := false
}

-- ============================================================
-- BASIC VERIFICATION
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

theorem same_mod : sameModAccum stateA stateB = true := by native_decide
theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

private theorem no_end_384 : noEndTurn (mkLoopTrace [ci3, ci8, ci4]) = true := by native_decide
private theorem no_end_348 : noEndTurn (mkLoopTrace [ci3, ci4, ci8]) = true := by native_decide
private theorem no_end_834 : noEndTurn (mkLoopTrace [ci8, ci3, ci4]) = true := by native_decide
private theorem no_end_843 : noEndTurn (mkLoopTrace [ci8, ci4, ci3]) = true := by native_decide
private theorem no_end_438 : noEndTurn (mkLoopTrace [ci4, ci3, ci8]) = true := by native_decide
private theorem no_end_483 : noEndTurn (mkLoopTrace [ci4, ci8, ci3]) = true := by native_decide

-- ============================================================
-- PERMUTATION ENUMERATION (3-element)
-- ============================================================

private theorem perm_384_cases (l : List CardInstance) (hp : l.Perm [ci3, ci8, ci4]) :
    l = [ci3, ci8, ci4] ∨ l = [ci3, ci4, ci8] ∨ l = [ci8, ci3, ci4] ∨
    l = [ci8, ci4, ci3] ∨ l = [ci4, ci3, ci8] ∨ l = [ci4, ci8, ci3] := by
  have hlen := hp.length_eq
  simp at hlen
  match l, hlen with
  | [x, y, z], _ =>
    have hx : x ∈ [ci3, ci8, ci4] := hp.mem_iff.mp (by simp)
    have hy : y ∈ [ci3, ci8, ci4] := hp.mem_iff.mp (by simp)
    have hz : z ∈ [ci3, ci8, ci4] := hp.mem_iff.mp (by simp)
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

-- After play c3 (Eruption+): dealDamage 9 first (Calm, no mult), then Calm→Wrath +2E +6 block
-- card in inUse
private def s1 : GameState := {
  hand := []
  drawPile := []
  discardPile := [ci8, ci4]
  exhaustPile := stateA.exhaustPile
  inUse := [ci3]
  actionQueue := []
  energy := 8
  damage := 15
  block := 12
  stance := .Wrath
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 15
  noDraw := false
  corruptionActive := false
}

-- resolveInUse: ci3 → discard (not exhaust, not shuffle)
private def s1r : GameState := {
  s1 with
  discardPile := [ci3, ci8, ci4]
  inUse := []
}

-- After resolveRushdown: +4 draws
private def s2 : GameState := { s1r with actionQueue := [.draw, .draw, .draw, .draw] }

-- After autoPlayFlurry c8: Flurry in disc, 6*2 Wrath = 12 dmg → 15+12=27
private def s3 : GameState := { s2 with damage := 27 }

-- Shuffle states: after first draw.  drawPile was [], disc=[ci3,ci8,ci4]
-- Oracle shuffles to permutation. Draw top card.
-- For perm [a,b,c]: drawPile = [b,c] after drawing a
private def s_after_draw1 (a b c : CardInstance) : GameState := {
  hand := [a]
  drawPile := [b, c]
  discardPile := []
  exhaustPile := stateA.exhaustPile
  inUse := []
  actionQueue := [.draw, .draw, .draw]
  energy := 8
  damage := 27
  block := 12
  stance := .Wrath
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 15
  noDraw := false
  corruptionActive := false
}

private def s_after_draw2 (a b c : CardInstance) : GameState := {
  hand := [b, a]
  drawPile := [c]
  discardPile := []
  exhaustPile := stateA.exhaustPile
  inUse := []
  actionQueue := [.draw, .draw]
  energy := 8
  damage := 27
  block := 12
  stance := .Wrath
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 15
  noDraw := false
  corruptionActive := false
}

private def s_after_draw3 (a b c : CardInstance) : GameState := {
  hand := [c, b, a]
  drawPile := []
  discardPile := []
  exhaustPile := stateA.exhaustPile
  inUse := []
  actionQueue := [.draw]
  energy := 8
  damage := 27
  block := 12
  stance := .Wrath
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 15
  noDraw := false
  corruptionActive := false
}

-- ============================================================
-- STEP LEMMAS
-- ============================================================

private theorem hc_stateA : resolveInUse cardDB (autoDrain cardDB stateA) = stateA := by native_decide
private theorem hs_play_c3 : step cardDB stateA (.play 3) = some s1 := by native_decide
private theorem hc_s1 : resolveInUse cardDB (autoDrain cardDB s1) = s1r := by native_decide
private theorem hs_rushdown : step cardDB s1r .resolveRushdown = some s2 := by native_decide
private theorem hc_s2 : resolveInUse cardDB (autoDrain cardDB s2) = s2 := by native_decide
private theorem hs_flurry : step cardDB s2 (.autoPlayFlurry 8) = some s3 := by native_decide
private theorem hc_s3 : resolveInUse cardDB (autoDrain cardDB s3) = s3 := by native_decide

-- Cleanup lemmas for draw states
private theorem hc_s_after_draw1 (a b c : CardInstance) :
    resolveInUse cardDB (autoDrain cardDB (s_after_draw1 a b c)) = s_after_draw1 a b c := by
  simp [s_after_draw1, autoDrain, resolveInUse]
private theorem hc_s_after_draw2 (a b c : CardInstance) :
    resolveInUse cardDB (autoDrain cardDB (s_after_draw2 a b c)) = s_after_draw2 a b c := by
  simp [s_after_draw2, autoDrain, resolveInUse]
private theorem hc_s_after_draw3 (a b c : CardInstance) :
    resolveInUse cardDB (autoDrain cardDB (s_after_draw3 a b c)) = s_after_draw3 a b c := by
  simp [s_after_draw3, autoDrain, resolveInUse]

-- ============================================================
-- DRAW STEP LEMMAS
-- ============================================================

-- First draw: shuffle [ci3,ci8,ci4] via oracle. Each perm gives different top card.
private theorem fd_384 :
    drawCardL2 (fun _ _ => [ci3, ci8, ci4]) 0 s3 3 = some (s_after_draw1 ci3 ci8 ci4, 1) := by
  native_decide
private theorem fd_348 :
    drawCardL2 (fun _ _ => [ci3, ci4, ci8]) 0 s3 3 = some (s_after_draw1 ci3 ci4 ci8, 1) := by
  native_decide
private theorem fd_834 :
    drawCardL2 (fun _ _ => [ci8, ci3, ci4]) 0 s3 8 = some (s_after_draw1 ci8 ci3 ci4, 1) := by
  native_decide
private theorem fd_843 :
    drawCardL2 (fun _ _ => [ci8, ci4, ci3]) 0 s3 8 = some (s_after_draw1 ci8 ci4 ci3, 1) := by
  native_decide
private theorem fd_438 :
    drawCardL2 (fun _ _ => [ci4, ci3, ci8]) 0 s3 4 = some (s_after_draw1 ci4 ci3 ci8, 1) := by
  native_decide
private theorem fd_483 :
    drawCardL2 (fun _ _ => [ci4, ci8, ci3]) 0 s3 4 = some (s_after_draw1 ci4 ci8 ci3, 1) := by
  native_decide

-- Second draw: drawPile = [b,c] non-empty → oracle-independent
private theorem sd2_oracle (oracle : ShuffleOracle) (a b c : CardInstance) :
    drawCardL2 oracle 1 (s_after_draw1 a b c) b.id = some (s_after_draw2 a b c, 1) := by
  simp [drawCardL2, s_after_draw1, s_after_draw2]

-- Third draw: drawPile = [c] non-empty → oracle-independent
private theorem sd3_oracle (oracle : ShuffleOracle) (a b c : CardInstance) :
    drawCardL2 oracle 1 (s_after_draw2 a b c) c.id = some (s_after_draw3 a b c, 1) := by
  simp [drawCardL2, s_after_draw2, s_after_draw3]

-- ============================================================
-- TAIL VERIFICATION
-- ============================================================

-- After drawing all 3 cards, failDraw + play c8 + play c4 + autoPlayFlurry c8
-- All 6 perms produce the same stateB (hand has same set, plays use findById)
private theorem tail_384 :
    executeL2 cardDB (fun _ _ => []) 1 (s_after_draw3 ci3 ci8 ci4)
      [.failDraw, .play 8, .play 4, .autoPlayFlurry 8] = some (stateB, 1) := by
  native_decide
private theorem tail_348 :
    executeL2 cardDB (fun _ _ => []) 1 (s_after_draw3 ci3 ci4 ci8)
      [.failDraw, .play 8, .play 4, .autoPlayFlurry 8] = some (stateB, 1) := by
  native_decide
private theorem tail_834 :
    executeL2 cardDB (fun _ _ => []) 1 (s_after_draw3 ci8 ci3 ci4)
      [.failDraw, .play 8, .play 4, .autoPlayFlurry 8] = some (stateB, 1) := by
  native_decide
private theorem tail_843 :
    executeL2 cardDB (fun _ _ => []) 1 (s_after_draw3 ci8 ci4 ci3)
      [.failDraw, .play 8, .play 4, .autoPlayFlurry 8] = some (stateB, 1) := by
  native_decide
private theorem tail_438 :
    executeL2 cardDB (fun _ _ => []) 1 (s_after_draw3 ci4 ci3 ci8)
      [.failDraw, .play 8, .play 4, .autoPlayFlurry 8] = some (stateB, 1) := by
  native_decide
private theorem tail_483 :
    executeL2 cardDB (fun _ _ => []) 1 (s_after_draw3 ci4 ci8 ci3)
      [.failDraw, .play 8, .play 4, .autoPlayFlurry 8] = some (stateB, 1) := by
  native_decide

-- Tail is oracle-independent (all steps are non-draw)
private theorem tail_oracle_indep (o1 o2 : ShuffleOracle) (idx : Nat) (s : GameState) :
    executeL2 cardDB o1 idx s
      [.failDraw, .play 8, .play 4, .autoPlayFlurry 8] =
    executeL2 cardDB o2 idx s
      [.failDraw, .play 8, .play 4, .autoPlayFlurry 8] := by
  simp only [executeL2, stepL2]

-- ============================================================
-- PER-CASE LOOP PROOFS
-- ============================================================

private theorem loop_case (oracle : ShuffleOracle) (a b c : CardInstance)
    (h : oracle 0 [ci3, ci8, ci4] = [a, b, c])
    (h_fd : drawCardL2 (fun _ _ => [a, b, c]) 0 s3 a.id = some (s_after_draw1 a b c, 1))
    (h_tail : executeL2 cardDB (fun _ _ => []) 1 (s_after_draw3 a b c)
      [.failDraw, .play 8, .play 4, .autoPlayFlurry 8] = some (stateB, 1)) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace [a, b, c]) = some (stateB, 1) := by
  show executeL2 cardDB oracle 0 stateA
    ([.play 3, .resolveRushdown, .autoPlayFlurry 8,
      .draw a.id, .draw b.id, .draw c.id,
      .failDraw, .play 8, .play 4, .autoPlayFlurry 8]) = some (stateB, 1)
  -- Step 1: play c3 → s1
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs_play_c3)]
  -- Step 2: resolveRushdown → s2
  rw [exL2_cons hc_s1 (sL2_step (by intro c; simp) hs_rushdown)]
  -- Step 3: autoPlayFlurry c8 → s3
  rw [exL2_cons hc_s2 (sL2_step (by intro c; simp) hs_flurry)]
  -- Step 4: draw a (oracle-dependent, shuffle from [ci3,ci8,ci4])
  have hd_a : drawCardL2 oracle 0 s3 a.id = some (s_after_draw1 a b c, 1) := by
    unfold drawCardL2
    simp only [s3, s2, s1r, s1]
    rw [h]; exact h_fd ▸ rfl
  rw [exL2_cons hc_s3 (sL2_draw hd_a)]
  -- Step 5: draw b (oracle-independent, drawPile ≠ [])
  rw [exL2_cons (hc_s_after_draw1 a b c) (sL2_draw (sd2_oracle oracle a b c))]
  -- Step 6: draw c (oracle-independent, drawPile ≠ [])
  rw [exL2_cons (hc_s_after_draw2 a b c) (sL2_draw (sd3_oracle oracle a b c))]
  -- Steps 7-10: tail (oracle-independent)
  rw [tail_oracle_indep oracle (fun _ _ => []) 1 (s_after_draw3 a b c)]
  exact h_tail

-- ============================================================
-- MAIN THEOREM
-- ============================================================

theorem ComboMantraDivine_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle h_valid
  have h_perm := h_valid 0 [ci3, ci8, ci4]
  have h_cases := perm_384_cases (oracle 0 [ci3, ci8, ci4]) h_perm
  rcases h_cases with h | h | h | h | h | h
  · exact ⟨_, _, _, loop_case oracle ci3 ci8 ci4 h fd_384 tail_384, no_end_384, same_mod, dealt_dmg⟩
  · exact ⟨_, _, _, loop_case oracle ci3 ci4 ci8 h fd_348 tail_348, no_end_348, same_mod, dealt_dmg⟩
  · exact ⟨_, _, _, loop_case oracle ci8 ci3 ci4 h fd_834 tail_834, no_end_834, same_mod, dealt_dmg⟩
  · exact ⟨_, _, _, loop_case oracle ci8 ci4 ci3 h fd_843 tail_843, no_end_843, same_mod, dealt_dmg⟩
  · exact ⟨_, _, _, loop_case oracle ci4 ci3 ci8 h fd_438 tail_438, no_end_438, same_mod, dealt_dmg⟩
  · exact ⟨_, _, _, loop_case oracle ci4 ci8 ci3 h fd_483 tail_483, no_end_483, same_mod, dealt_dmg⟩

end ComboMantraDivine_L2
