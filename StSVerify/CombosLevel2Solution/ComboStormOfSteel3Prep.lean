/-
  Storm of Steel+ + Tactician+ + Reflex+ + 3x Prepared+ (6 cards) - Level 2

  RESULT: Guaranteed infinite at Level 2.

  Same strategy as 2Prep but with one extra Prepared+.
  After SoS discards 4 cards, the 5-card discard pile is shuffled (idx 0).
  Oracle draws 3, stranding 2 in drawPile. Prep rescues both stranded cards.
  Discarding Tact + Reflex triggers draw 3 from a 3-card shuffle (idx 1)
  which always draws all 3 (SoS, Tact, Reflex).

  Shuffle points:
    0: [ci1, ci2, ci4, ci5, ci3] (5 cards) -- 5! = 120 perms, draw 3
    1: [ci2, ci1, ci0] (3 cards) -- 3! = 6 perms, draw all 3

  All 120 x 6 = 720 oracle behaviors verified.
  Uses drawCondBool bridge pattern.
-/

import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB

open CardName Action

namespace ComboStormOfSteel3Prep_L2

private def ci0 : CardInstance := { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }
private def ci1 : CardInstance := { id := 1, name := TacticianPlus, cost := 0, damage := 0 }
private def ci2 : CardInstance := { id := 2, name := ReflexPlus, cost := 0, damage := 0 }
private def ci3 : CardInstance := { id := 3, name := PreparedPlus, cost := 0, damage := 0 }
private def ci4 : CardInstance := { id := 4, name := PreparedPlus, cost := 0, damage := 0 }
private def ci5 : CardInstance := { id := 5, name := PreparedPlus, cost := 0, damage := 0 }

def cards : List (CardName × Nat) := [
  (StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1), (PreparedPlus, 3)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0,
  .draw 5, .draw 4, .draw 3,
  .play 6, .play 7, .play 8, .play 9,
  .play 3,
  .draw 2, .draw 1,
  .discard 1, .discard 2,
  .draw 2, .draw 1, .draw 0
]

def stateA : GameState := {
  hand := [ci0, ci1, ci2, ci4, ci5]
  drawPile := []
  discardPile := [ci3]
  exhaustPile := [{ id := 9, name := Shiv, cost := 0, damage := 4 },
                  { id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 }]
  inUse := []
  actionQueue := []
  energy := 6
  damage := 16
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := enemy
  activePowers := []
  nextId := 10
  noDraw := false
  corruptionActive := false
}

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- ============================================================
-- LOOP TRACE
-- ============================================================

private def pile0 : List CardInstance := [ci1, ci2, ci4, ci5, ci3]
private def pile1 : List CardInstance := [ci2, ci1, ci0]

/-- Pick which Prep to play from the top 3 drawn cards.
    The top 3 are from the 5-card shuffle. We always play a Prep that's in hand.
    After play SoS + draw 3 + play shivs, hand = [top3]. We play the first Prep found. -/
private def pickPrep (a b c : CardInstance) : CId :=
  if a.name == PreparedPlus then a.id
  else if b.name == PreparedPlus then b.id
  else c.id  -- at least one of top3 must be a Prep (out of 5 cards, 3 are Preps)

def mkLoopTrace (sh0 sh1 : List CardInstance) : List Action :=
  match sh0 with
  | a :: b :: c :: [d, e] =>
    let prepId := pickPrep a b c
    [.play 0,
     .draw a.id, .draw b.id, .draw c.id,
     .play 10, .play 11, .play 12, .play 13,
     .play prepId,
     .draw d.id, .draw e.id,
     .discard 1, .discard 2] ++
    (sh1.map fun x => Action.draw x.id)
  | _ => []

def fixedOracle (sh0 sh1 : List CardInstance) : ShuffleOracle := fun idx pile =>
  if idx == 0 then sh0 else if idx == 1 then sh1 else pile

-- ============================================================
-- PERMUTATION HELPERS
-- ============================================================

private def permsOf : List CardInstance → List (List CardInstance)
  | [] => [[]]
  | x :: xs =>
    let ps := permsOf xs
    ps.bind fun p => (List.range (p.length + 1)).map fun i =>
      p.take i ++ [x] ++ p.drop i

/-- DecidableEq-based list membership check (avoids needing LawfulBEq). -/
private def listMemDec [DecidableEq α] (x : α) (xs : List α) : Bool :=
  xs.any (fun y => decide (x = y))

private theorem listMemDec_sound [DecidableEq α] (x : α) (xs : List α)
    (h : listMemDec x xs = true) : x ∈ xs := by
  unfold listMemDec at h
  rw [List.any_eq_true] at h
  obtain ⟨y, hyin, hxy⟩ := h
  simp [decide_eq_true_eq] at hxy
  rwa [hxy]

private def allPerms3 : List (List CardInstance) :=
  [[ci2, ci1, ci0], [ci1, ci2, ci0], [ci1, ci0, ci2],
   [ci2, ci0, ci1], [ci0, ci2, ci1], [ci0, ci1, ci2]]

-- Generate allPerms5 computationally but define as a concrete list for decidability
private def allPerms5 : List (List CardInstance) := permsOf [ci1, ci2, ci4, ci5, ci3]

private theorem perm3_mem (l : List CardInstance) (hp : l.Perm pile1) :
    l ∈ allPerms3 := by
  have hlen := hp.length_eq; simp [pile1] at hlen
  have hmem : ∀ x ∈ l, x = ci2 ∨ x = ci1 ∨ x = ci0 := by
    intro x hx; have := hp.subset hx; simp [pile1, List.mem_cons, List.mem_nil_iff] at this; exact this
  have hnd : l.Nodup := hp.nodup_iff.mpr (by decide)
  match l, hlen with
  | [a, b, c], _ =>
    have ha := hmem a (by simp); have hb := hmem b (by simp); have hc := hmem c (by simp)
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or, List.not_mem_nil,
               not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hab, hac⟩, hbc, _⟩ := hnd
    rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    (try exact absurd rfl hab) <;>
    rcases hc with rfl | rfl | rfl <;>
    (try exact absurd rfl hac) <;>
    (try exact absurd rfl hbc) <;>
    exact listMemDec_sound _ _ (by native_decide)

private theorem perm5_mem (l : List CardInstance) (hp : l.Perm pile0) :
    l ∈ allPerms5 := by
  have hlen := hp.length_eq; simp [pile0] at hlen
  have hmem : ∀ x ∈ l, x = ci1 ∨ x = ci2 ∨ x = ci4 ∨ x = ci5 ∨ x = ci3 := by
    intro x hx; have := hp.subset hx; simp [pile0, List.mem_cons, List.mem_nil_iff] at this; exact this
  have hnd : l.Nodup := hp.nodup_iff.mpr (by decide)
  match l, hlen with
  | [a, b, c, d, e], _ =>
    have ha := hmem a (by simp); have hb := hmem b (by simp)
    have hc := hmem c (by simp); have hd := hmem d (by simp)
    have he := hmem e (by simp)
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or, List.not_mem_nil,
               not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde, _⟩ := hnd
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl hab) <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl hac) <;>
    (try exact absurd rfl hbc) <;>
    rcases hd with rfl | rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl had) <;>
    (try exact absurd rfl hbd) <;>
    (try exact absurd rfl hcd) <;>
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl hae) <;>
    (try exact absurd rfl hbe) <;>
    (try exact absurd rfl hce) <;>
    (try exact absurd rfl hde) <;>
    exact listMemDec_sound _ _ (by native_decide)

-- ============================================================
-- DRAW-ONLY ORACLE BRIDGE
-- ============================================================

private def drawCondBool (fo : ShuffleOracle) (p0 p1 : List CardInstance)
    (si : Nat) (s : GameState) : List Action → Bool
  | [] => true
  | a :: rest =>
    let sc := resolveInUse cardDB (autoDrain cardDB s)
    let dpOk := match a with
      | .draw _ => sc.drawPile.length > 0 ||
                   (decide (si = 0) && decide (sc.discardPile = p0)) ||
                   (decide (si = 1) && decide (sc.discardPile = p1))
      | _ => true
    match stepL2 cardDB fo si sc a with
    | some (s', si') => dpOk && drawCondBool fo p0 p1 si' s' rest
    | none => false

private theorem drawCondBool_bridge (oracle fo : ShuffleOracle) (p0 p1 : List CardInstance)
    (h0 : oracle 0 p0 = fo 0 p0)
    (h1 : oracle 1 p1 = fo 1 p1)
    (si : Nat) (s : GameState) (trace : List Action)
    (hb : drawCondBool fo p0 p1 si s trace = true) :
    executeL2 cardDB oracle si s trace = executeL2 cardDB fo si s trace := by
  induction trace generalizing si s with
  | nil => rfl
  | cons a rest ih =>
    simp only [drawCondBool] at hb
    match hfo : stepL2 cardDB fo si (resolveInUse cardDB (autoDrain cardDB s)) a with
    | none => rw [hfo] at hb; simp at hb
    | some (s', si') =>
      rw [hfo] at hb; simp only [Bool.and_eq_true] at hb; obtain ⟨hdpOk, hrest⟩ := hb
      have h_step_eq : stepL2 cardDB oracle si (resolveInUse cardDB (autoDrain cardDB s)) a =
                       stepL2 cardDB fo si (resolveInUse cardDB (autoDrain cardDB s)) a := by
        cases a with
        | draw c =>
          apply stepL2_oracle_cond
          by_cases hdp : (resolveInUse cardDB (autoDrain cardDB s)).drawPile = []
          · right
            simp only [hdp, List.length_nil, Nat.lt_irrefl, gt_iff_lt, false_or,
                       Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hdpOk
            rcases hdpOk with ⟨hsi, hdisc⟩ | ⟨hsi, hdisc⟩ <;> simp_all
          · left; exact hdp
        | _ => rfl
      change (let sc := resolveInUse cardDB (autoDrain cardDB s)
              match stepL2 cardDB oracle si sc a with
              | none => none | some (s'', si'') => executeL2 cardDB oracle si'' s'' rest) =
             (let sc := resolveInUse cardDB (autoDrain cardDB s)
              match stepL2 cardDB fo si sc a with
              | none => none | some (s'', si'') => executeL2 cardDB fo si'' s'' rest)
      simp only [h_step_eq, hfo]
      exact ih si' s' hrest

-- ============================================================
-- CONCRETE VERIFICATION
-- ============================================================

private def verifyOne (sh0 sh1 : List CardInstance) : Bool :=
  match executeL2 cardDB (fixedOracle sh0 sh1) 0 stateA (mkLoopTrace sh0 sh1) with
  | some (stateB, _) =>
    sameModAccum stateA stateB && dealtDamage stateA stateB &&
    drawCondBool (fixedOracle sh0 sh1) pile0 pile1 0 stateA (mkLoopTrace sh0 sh1) &&
    noEndTurn (mkLoopTrace sh0 sh1)
  | none => false

private def verifyAll : Bool :=
  allPerms5.all fun sh0 => allPerms3.all fun sh1 => verifyOne sh0 sh1

set_option maxHeartbeats 4000000 in
theorem all_verified : verifyAll = true := by native_decide

private theorem verifyOne_of_mem (sh0 sh1 : List CardInstance)
    (h0 : sh0 ∈ allPerms5) (h1 : sh1 ∈ allPerms3) :
    verifyOne sh0 sh1 = true := by
  have hva := all_verified
  unfold verifyAll at hva
  rw [List.all_eq_true] at hva
  have h0' := hva sh0 h0
  rw [List.all_eq_true] at h0'
  exact h0' sh1 h1

-- ============================================================
-- CASE HANDLER
-- ============================================================

private theorem case_handler (sh0 sh1 : List CardInstance)
    (hmem0 : sh0 ∈ allPerms5) (hmem1 : sh1 ∈ allPerms3)
    (oracle : ShuffleOracle)
    (ho0 : oracle 0 pile0 = sh0)
    (ho1 : oracle 1 pile1 = sh1) :
    ∃ (loopTrace : List Action) (stateB : GameState) (finalIdx : Nat),
      executeL2 cardDB oracle 0 stateA loopTrace = some (stateB, finalIdx)
      ∧ noEndTurn loopTrace = true
      ∧ sameModAccum stateA stateB = true
      ∧ dealtDamage stateA stateB = true := by
  have hv := verifyOne_of_mem sh0 sh1 hmem0 hmem1
  unfold verifyOne at hv
  have hf0 : oracle 0 pile0 = fixedOracle sh0 sh1 0 pile0 := by
    simp only [fixedOracle]; exact ho0
  have hf1 : oracle 1 pile1 = fixedOracle sh0 sh1 1 pile1 := by
    simp only [fixedOracle]; exact ho1
  generalize hres : executeL2 cardDB (fixedOracle sh0 sh1) 0 stateA (mkLoopTrace sh0 sh1) = result at hv
  match result, hv with
  | some (stB, fIdx), hv =>
    simp only [Bool.and_eq_true] at hv
    obtain ⟨⟨⟨hsm, hdd⟩, hdc⟩, hne⟩ := hv
    have hbridge := drawCondBool_bridge oracle (fixedOracle sh0 sh1) pile0 pile1 hf0 hf1 0 stateA
      (mkLoopTrace sh0 sh1) hdc
    exact ⟨mkLoopTrace sh0 sh1, stB, fIdx, hbridge ▸ hres, hne, hsm, hdd⟩
  | none, hv => simp at hv

-- ============================================================
-- MAIN THEOREM
-- ============================================================

set_option maxHeartbeats 8000000 in
theorem ComboStormOfSteel3Prep_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  have hPerm0 : List.Perm (oracle 0 pile0) pile0 := hValid 0 pile0
  have hPerm1 : List.Perm (oracle 1 pile1) pile1 := hValid 1 pile1
  exact case_handler (oracle 0 pile0) (oracle 1 pile1)
    (perm5_mem _ hPerm0) (perm3_mem _ hPerm1) oracle rfl rfl

end ComboStormOfSteel3Prep_L2
