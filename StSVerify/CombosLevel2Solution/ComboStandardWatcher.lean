/-
  観者 - 標準沙雕無限 (Level 2)
  Two 2-element shuffle points → 4 oracle cases total.
  Uses drawCondBool bridge pattern to lift concrete oracle verification
  to abstract oracle proofs.
-/

import StSVerify.CombosSpecL2.ComboStandardWatcher
import StSVerify.EngineHelperLemmas

open CardName Action

namespace ComboStandardWatcher_L2

private def ci3  : CardInstance := { id := 3,  name := EruptionPlus,       cost := 1, damage := 9 }
private def ci4  : CardInstance := { id := 4,  name := TantrumPlus,        cost := 1, damage := 12 }
private def ci5  : CardInstance := { id := 5,  name := InnerPeacePlus,     cost := 1, damage := 0 }
private def ci6  : CardInstance := { id := 6,  name := FearNoEvilPlus,     cost := 1, damage := 11 }
private def ci7  : CardInstance := { id := 7,  name := FlurryOfBlowsPlus,  cost := 0, damage := 6 }



def setupTrace : List Action := [
  .draw 10, .resolveDrawTrigger 10,
  .draw 0, .draw 1, .draw 2, .draw 5,
  .play 0, .play 1, .play 2,
  .play 12, .play 13,
  .play 5,
  .endTurn,
  .draw 4, .draw 6, .draw 11, .draw 9, .draw 8,
  .play 4,
  .draw 4, .draw 3, .draw 7, .draw 5,
  .play 11, .play 9, .play 8,
  .failDraw,
  .endTurn,
  .draw 5, .draw 7, .draw 3, .draw 4, .draw 6,
  .play 6, .play 3,
  .draw 3, .draw 6,
  .failDraw,
  .play 7, .play 5
]

private def exhaustPileConst : List CardInstance :=
  [ { id := 8,  name := Scrawl,             cost := 1, damage := 0 },
    { id := 9,  name := VaultPlus,           cost := 2, damage := 0 },
    { id := 11, name := TalkToTheHandPlus,   cost := 1, damage := 7 },
    { id := 13, name := Miracle,             cost := 0, damage := 0 },
    { id := 12, name := Miracle,             cost := 0, damage := 0 },
    { id := 10, name := DeusExMachina,       cost := 0, damage := 0 } ]

def stateA : GameState := {
  hand := [ci6, ci3, ci4]
  drawPile := []
  discardPile := [ci5, ci7]
  exhaustPile := exhaustPileConst
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

-- Shuffle piles
private def pile0 : List CardInstance := [ci5, ci7]
private def pile1 : List CardInstance := [ci3, ci6]

-- ============================================================
-- SETUP VERIFICATION
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- ============================================================
-- ORACLE-ADAPTIVE LOOP TRACE
-- ============================================================

def mkLoopTrace (sh0 : List CardInstance) (sh1 : List CardInstance) : List Action :=
  match sh0, sh1 with
  | d0a :: d0b :: _, d1a :: d1b :: _ =>
    [ .play 4,
      .draw 4, .draw d0a.id, .draw d0b.id,
      .failDraw,
      .play 6, .play 3,
      .draw d1a.id, .draw d1b.id,
      .failDraw,
      .play 7, .play 5 ]
  | _, _ => []

-- ============================================================
-- FIXED ORACLE AND drawCondBool BRIDGE
-- ============================================================

private def fixedOracle (sh0 sh1 : List CardInstance) : ShuffleOracle :=
  fun idx _ => if idx == 0 then sh0 else if idx == 1 then sh1 else []

-- drawCondBool: at each draw step, either drawPile is non-empty or
-- the oracle is at a known (shIdx, discardPile) pair
private def drawCondBool (fo : ShuffleOracle) (si : Nat) (s : GameState)
    : List Action → Bool
  | [] => true
  | a :: rest =>
    let sc := autoDrain cardDB s
    let dpOk := match a with
      | .draw _ => sc.drawPile.length > 0 ||
                   (decide (si = 0) && decide (sc.discardPile = pile0)) ||
                   (decide (si = 1) && decide (sc.discardPile = pile1))
      | _ => true
    match stepL2 cardDB fo si sc a with
    | some (s', si') => dpOk && drawCondBool fo si' s' rest
    | none => false

-- Bridge: if drawCondBool holds with fo, then executeL2 with any oracle
-- that agrees on the relevant piles gives the same result
private theorem drawCondBool_bridge (oracle fo : ShuffleOracle)
    (h0 : oracle 0 pile0 = fo 0 pile0) (h1 : oracle 1 pile1 = fo 1 pile1)
    (si : Nat) (s : GameState) (trace : List Action)
    (hb : drawCondBool fo si s trace = true) :
    executeL2 cardDB oracle si s trace = executeL2 cardDB fo si s trace := by
  induction trace generalizing si s with
  | nil => rfl
  | cons a rest ih =>
    simp only [drawCondBool] at hb
    match hfo : stepL2 cardDB fo si (autoDrain cardDB s) a with
    | none => rw [hfo] at hb; simp at hb
    | some (s', si') =>
      rw [hfo] at hb; simp only [Bool.and_eq_true] at hb; obtain ⟨hdpOk, hrest⟩ := hb
      have h_step_eq : stepL2 cardDB oracle si (autoDrain cardDB s) a =
                       stepL2 cardDB fo si (autoDrain cardDB s) a := by
        cases a with
        | draw c =>
          apply stepL2_oracle_cond
          by_cases hdp : (autoDrain cardDB s).drawPile = []
          · right
            simp only [hdp, List.length_nil, Nat.lt_irrefl, gt_iff_lt, false_or,
                       Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hdpOk
            rcases hdpOk with ⟨hsi, hdisc⟩ | ⟨hsi, hdisc⟩
            · rw [hsi, hdisc]; exact h0
            · rw [hsi, hdisc]; exact h1
          · left; exact hdp
        | _ => rfl
      show (let sc := autoDrain cardDB s
            match stepL2 cardDB oracle si sc a with
            | none => none | some (s'', si'') => executeL2 cardDB oracle si'' s'' rest) =
           (let sc := autoDrain cardDB s
            match stepL2 cardDB fo si sc a with
            | none => none | some (s'', si'') => executeL2 cardDB fo si'' s'' rest)
      simp only [h_step_eq, hfo]; exact ih si' s' hrest

-- ============================================================
-- PERMUTATION ENUMERATION
-- ============================================================

-- All permutations of 2-element lists
private def allPerms2_0 : List (List CardInstance) :=
  [ [ci5, ci7], [ci7, ci5] ]

private def allPerms2_1 : List (List CardInstance) :=
  [ [ci3, ci6], [ci6, ci3] ]

-- All 4 combinations
private def allCombos : List (List CardInstance × List CardInstance) :=
  allPerms2_0.flatMap fun sh0 => allPerms2_1.map fun sh1 => (sh0, sh1)

-- ============================================================
-- VERIFICATION FUNCTION
-- ============================================================

private def verifyOne (sh0 sh1 : List CardInstance) : Bool :=
  let fo := fixedOracle sh0 sh1
  let trace := mkLoopTrace sh0 sh1
  match executeL2 cardDB fo 0 stateA trace with
  | some (stB, _) =>
    sameModAccum stateA stB && dealtDamage stateA stB &&
    drawCondBool fo 0 stateA trace && noEndTurn trace
  | none => false

private def verifyAll : Bool :=
  allCombos.all fun (sh0, sh1) => verifyOne sh0 sh1

set_option maxHeartbeats 8000000 in
theorem all_verified : verifyAll = true := by native_decide

-- ============================================================
-- PERMUTATION MEMBERSHIP
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

private theorem perm2_mem_0 (l : List CardInstance) (hp : l.Perm pile0) :
    l ∈ allPerms2_0 := by
  have h := perm_2_ci l ci5 ci7 (by decide) hp
  rcases h with rfl | rfl <;> simp [allPerms2_0]

private theorem perm2_mem_1 (l : List CardInstance) (hp : l.Perm pile1) :
    l ∈ allPerms2_1 := by
  have h := perm_2_ci l ci3 ci6 (by decide) hp
  rcases h with rfl | rfl <;> simp [allPerms2_1]

-- ============================================================
-- CASE HANDLER
-- ============================================================

private theorem handle_case (sh0 sh1 : List CardInstance)
    (hmem : (sh0, sh1) ∈ allCombos)
    (oracle : ShuffleOracle)
    (h0 : oracle 0 pile0 = sh0) (h1 : oracle 1 pile1 = sh1) :
    ∃ t sB fi, executeL2 cardDB oracle 0 stateA t = some (sB, fi)
      ∧ noEndTurn t = true ∧ sameModAccum stateA sB = true ∧ dealtDamage stateA sB = true := by
  have hva := all_verified; unfold verifyAll at hva; rw [List.all_eq_true] at hva
  have hv := hva (sh0, sh1) hmem
  simp only [verifyOne] at hv
  split at hv
  · next stB fIdx heq =>
    simp only [Bool.and_eq_true] at hv; obtain ⟨⟨⟨hsm, hdd⟩, hdc⟩, hne⟩ := hv
    have hf0 : oracle 0 pile0 = fixedOracle sh0 sh1 0 pile0 := by
      simp [fixedOracle]; exact h0
    have hf1 : oracle 1 pile1 = fixedOracle sh0 sh1 1 pile1 := by
      simp [fixedOracle]; exact h1
    exact ⟨_, stB, fIdx,
      (drawCondBool_bridge oracle _ hf0 hf1 0 stateA _ hdc) ▸ heq,
      hne, hsm, hdd⟩
  · simp at hv

-- ============================================================
-- MAIN THEOREM
-- ============================================================

set_option maxHeartbeats 16000000 in
theorem ComboStandardWatcher_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  have hp0 := hValid 0 pile0
  have hp1 := hValid 1 pile1
  have hm0 := perm2_mem_0 (oracle 0 pile0) hp0
  have hm1 := perm2_mem_1 (oracle 1 pile1) hp1
  -- Enumerate all 4 cases
  simp only [allPerms2_0, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hm0
  simp only [allPerms2_1, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hm1
  rcases hm0 with h0 | h0 <;> rcases hm1 with h1 | h1
  · exact handle_case _ _ (by simp [allCombos, allPerms2_0, allPerms2_1]) oracle h0 h1
  · exact handle_case _ _ (by simp [allCombos, allPerms2_0, allPerms2_1]) oracle h0 h1
  · exact handle_case _ _ (by simp [allCombos, allPerms2_0, allPerms2_1]) oracle h0 h1
  · exact handle_case _ _ (by simp [allCombos, allPerms2_0, allPerms2_1]) oracle h0 h1

theorem proof : GuaranteedInfiniteCombo cardDB cards enemy := ComboStandardWatcher_guaranteed_infinite

end ComboStandardWatcher_L2
