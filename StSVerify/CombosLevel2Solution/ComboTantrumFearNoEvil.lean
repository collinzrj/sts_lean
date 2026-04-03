/-
  Watcher - Tantrum+ + 2×FearNoEvil+ + 2×FlurryOfBlows+ (Level 2, Strict)
  Total: 24 × 2 = 48 oracle permutation pairs.

  Strict L2 proof:
  - native_decide ONLY for engine helper lemmas with fully concrete inputs
  - NO native_decide in main proof, loop_case, oracle bridge, or permutation reasoning
-/

import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB

open CardName Action

namespace ComboTantrumFearNoEvil_L2_Strict

-- ============================================================
-- CARD INSTANCES
-- ============================================================

private def fne4  : CardInstance := { id := 4, name := FearNoEvilPlus, cost := 1, damage := 11 }
private def fne5  : CardInstance := { id := 5, name := FearNoEvilPlus, cost := 1, damage := 11 }
private def flr6  : CardInstance := { id := 6, name := FlurryOfBlowsPlus, cost := 0, damage := 6 }
private def flr7  : CardInstance := { id := 7, name := FlurryOfBlowsPlus, cost := 0, damage := 6 }
private def tant3 : CardInstance := { id := 3, name := TantrumPlus, cost := 1, damage := 12 }

private def exhaustConst : List CardInstance :=
  [{ id := 8, name := Scrawl, cost := 1, damage := 0 },
   { id := 9, name := VaultPlus, cost := 2, damage := 0 },
   { id := 12, name := Miracle, cost := 0, damage := 0 },
   { id := 11, name := Miracle, cost := 0, damage := 0 },
   { id := 10, name := DeusExMachina, cost := 0, damage := 0 }]
private def powersConst : List CardName := [MentalFortressPlus, Rushdown, Rushdown]
private def enemyConst : EnemyState := { vulnerable := 0, weak := 0, intending := true }

-- ============================================================
-- FRAMEWORK
-- ============================================================

def cards : List (CardName × Nat) :=
  [ (Rushdown, 2), (MentalFortressPlus, 1), (TantrumPlus, 1),
    (FearNoEvilPlus, 2), (FlurryOfBlowsPlus, 2), (Scrawl, 1),
    (VaultPlus, 1), (DeusExMachina, 1) ]

def enemy : EnemyState := enemyConst

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0, .play 1, .play 2,
  .endTurn,
  .draw 10, .resolveDrawTrigger 10,
  .draw 9, .draw 8, .draw 5, .draw 6,
  .play 11, .play 12, .play 9, .play 8,
  .draw 7, .draw 3, .draw 4, .failDraw,
  .changeStance .Calm,
  .play 3, .resolveRushdown, .draw 3, .failDraw,
  .play 4, .play 5, .play 6, .play 7
]

def stateA : GameState := {
  hand := [tant3], drawPile := [], discardPile := [flr7, flr6, fne5, fne4]
  exhaustPile := exhaustConst, inUse := [], actionQueue := []
  energy := 1, damage := 57, block := 18, stance := .Calm
  orbs := [], orbSlots := 3, focus := 0, enemy := enemyConst
  activePowers := powersConst, nextId := 13, noDraw := false, corruptionActive := false
}

-- ============================================================
-- SETUP VERIFICATION (concrete engine computation)
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- ============================================================
-- LOOP TRACE (adaptive, depends on oracle output)
-- ============================================================

private def pile1 : List CardInstance := [flr7, flr6, fne5, fne4]

private def isFNE (c : CardInstance) : Bool := c.name == CardName.FearNoEvilPlus
private def isFlurry (c : CardInstance) : Bool := c.name == CardName.FlurryOfBlowsPlus
private def pickFirstFNE (a b c : CardInstance) : CardInstance :=
  if isFNE a then a else if isFNE b then b else c
private def pickFirstFlurry (a b c : CardInstance) : CardInstance :=
  if isFlurry a then a else if isFlurry b then b else c
private def pickOther (a b c fne1 flurry1 : CardInstance) : CardInstance :=
  if a.id != fne1.id && a.id != flurry1.id then a
  else if b.id != fne1.id && b.id != flurry1.id then b
  else c
private def findFNE4 (a b c d : CardInstance) : CardInstance :=
  if isFNE a then a else if isFNE b then b else if isFNE c then c else d

def mkLoopTrace (sh1 sh2 : List CardInstance) : List Action :=
  match sh1 with
  | a :: b :: c :: d :: _ =>
    let fne1 := pickFirstFNE a b c
    let flurry1 := pickFirstFlurry a b c
    let other := pickOther a b c fne1 flurry1
    match sh2 with
    | e :: f :: _ =>
      let fne2 := findFNE4 other d e f
      let rest := [other, d, e, f].filter (fun x => x.id != fne2.id)
      match rest with
      | [r1, r2, r3] =>
        [.play 3, .resolveRushdown,
         .draw 3, .draw a.id, .draw b.id, .draw c.id,
         .play fne1.id, .play flurry1.id,
         .changeStance .Wrath, .resolveRushdown,
         .draw d.id, .draw e.id, .draw f.id, .failDraw,
         .play fne2.id, .play r1.id, .play r2.id, .play r3.id]
      | _ => []
    | _ => []
  | _ => []

def mkPile2 (sh1 : List CardInstance) : List CardInstance :=
  match sh1 with
  | a :: b :: c :: _ => [pickFirstFlurry a b c, pickFirstFNE a b c]
  | _ => []

def fixedOracle (sh1 sh2 : List CardInstance) : ShuffleOracle := fun idx _ =>
  if idx == 0 then sh1 else if idx == 1 then sh2 else []

-- ============================================================
-- PERMUTATION HELPERS (no native_decide)
-- ============================================================

set_option maxHeartbeats 800000 in
private theorem perm_4_ci (l : List CardInstance)
    (hp : List.Perm l [flr7, flr6, fne5, fne4]) :
    l = [fne4, fne5, flr6, flr7] ∨ l = [fne4, fne5, flr7, flr6] ∨
    l = [fne4, flr6, fne5, flr7] ∨ l = [fne4, flr6, flr7, fne5] ∨
    l = [fne4, flr7, fne5, flr6] ∨ l = [fne4, flr7, flr6, fne5] ∨
    l = [fne5, fne4, flr6, flr7] ∨ l = [fne5, fne4, flr7, flr6] ∨
    l = [fne5, flr6, fne4, flr7] ∨ l = [fne5, flr6, flr7, fne4] ∨
    l = [fne5, flr7, fne4, flr6] ∨ l = [fne5, flr7, flr6, fne4] ∨
    l = [flr6, fne4, fne5, flr7] ∨ l = [flr6, fne4, flr7, fne5] ∨
    l = [flr6, fne5, fne4, flr7] ∨ l = [flr6, fne5, flr7, fne4] ∨
    l = [flr6, flr7, fne4, fne5] ∨ l = [flr6, flr7, fne5, fne4] ∨
    l = [flr7, fne4, fne5, flr6] ∨ l = [flr7, fne4, flr6, fne5] ∨
    l = [flr7, fne5, fne4, flr6] ∨ l = [flr7, fne5, flr6, fne4] ∨
    l = [flr7, flr6, fne4, fne5] ∨ l = [flr7, flr6, fne5, fne4] := by
  have hlen := hp.length_eq; simp at hlen
  have hmem : ∀ x ∈ l, x = flr7 ∨ x = flr6 ∨ x = fne5 ∨ x = fne4 := by
    intro x hx; have hm := hp.subset hx; simp [List.mem_cons, List.mem_nil_iff, or_false] at hm; exact hm
  have hnd : l.Nodup := hp.nodup_iff.mpr (by decide)
  match l, hlen with
  | [a, b, c, d], _ =>
    have ha := hmem a (by simp); have hb := hmem b (by simp)
    have hc := hmem c (by simp); have hd := hmem d (by simp)
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or, List.not_mem_nil,
               not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd, _⟩ := hnd
    rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl hab) <;>
    rcases hc with rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl hac) <;>
    (try exact absurd rfl hbc) <;>
    rcases hd with rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl had) <;>
    (try exact absurd rfl hbd) <;>
    (try exact absurd rfl hcd) <;>
    simp [fne4, fne5, flr6, flr7]

private theorem perm_2_ci (l : List CardInstance) (x y : CardInstance) (hne : x ≠ y)
    (hp : List.Perm l [x, y]) : l = [x, y] ∨ l = [y, x] := by
  have hlen := hp.length_eq; simp at hlen
  match l, hlen with
  | [a, b], _ =>
    have hx : x ∈ [a, b] := hp.mem_iff.mpr (by simp)
    have hy : y ∈ [a, b] := hp.mem_iff.mpr (by simp)
    simp [List.mem_cons, List.mem_nil_iff] at hx hy
    have hnd : [a, b].Nodup := hp.nodup_iff.mpr (by simp [hne])
    rw [List.nodup_cons] at hnd; simp [List.mem_cons, List.mem_nil_iff] at hnd
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> (first | simp_all | omega)

-- ============================================================
-- DRAW-ONLY ORACLE BRIDGE
-- ============================================================

/-- At each draw step along the fixed oracle execution where drawPile is empty,
    check that we're at a known shuffle point. Non-draw steps are always OK. -/
private def drawCondBool (fo : ShuffleOracle) (p1 p2 : List CardInstance)
    (si : Nat) (s : GameState) : List Action → Bool
  | [] => true
  | a :: rest =>
    let sc := autoDrain cardDB s
    let dpOk := match a with
      | .draw _ => sc.drawPile.length > 0 ||
                   (decide (si = 0) && decide (sc.discardPile = p1)) ||
                   (decide (si = 1) && decide (sc.discardPile = p2))
      | _ => true
    match stepL2 cardDB fo si sc a with
    | some (s', si') => dpOk && drawCondBool fo p1 p2 si' s' rest
    | none => false

/-- Oracle bridge: if drawCondBool passes and oracle agrees at shuffle points,
    then executeL2 gives the same result for both oracles. -/
private theorem drawCondBool_bridge (oracle fo : ShuffleOracle) (p1 p2 : List CardInstance)
    (h0 : oracle 0 p1 = fo 0 p1)
    (h1 : oracle 1 p2 = fo 1 p2)
    (si : Nat) (s : GameState) (trace : List Action)
    (hb : drawCondBool fo p1 p2 si s trace = true) :
    executeL2 cardDB oracle si s trace = executeL2 cardDB fo si s trace := by
  induction trace generalizing si s with
  | nil => rfl
  | cons a rest ih =>
    simp only [drawCondBool] at hb
    -- stepL2 fo must succeed
    match hfo : stepL2 cardDB fo si (autoDrain cardDB s) a with
    | none => rw [hfo] at hb; simp at hb
    | some (s', si') =>
      rw [hfo] at hb; simp only [Bool.and_eq_true] at hb; obtain ⟨hdpOk, hrest⟩ := hb
      -- stepL2 oracle = stepL2 fo
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
      -- Rewrite
      change (let sc := autoDrain cardDB s
              match stepL2 cardDB oracle si sc a with
              | none => none | some (s'', si'') => executeL2 cardDB oracle si'' s'' rest) =
             (let sc := autoDrain cardDB s
              match stepL2 cardDB fo si sc a with
              | none => none | some (s'', si'') => executeL2 cardDB fo si'' s'' rest)
      simp only [h_step_eq, hfo]
      exact ih si' s' hrest

-- ============================================================
-- CONCRETE VERIFICATION (native_decide on fully concrete inputs)
-- ============================================================

private def verifyOne (s1 s2 : List CardInstance) : Bool :=
  match executeL2 cardDB (fixedOracle s1 s2) 0 stateA (mkLoopTrace s1 s2) with
  | some (stateB, _) =>
    sameModAccum stateA stateB && dealtDamage stateA stateB &&
    drawCondBool (fixedOracle s1 s2) pile1 (mkPile2 s1) 0 stateA (mkLoopTrace s1 s2) &&
    noEndTurn (mkLoopTrace s1 s2)
  | none => false

private def allPerms4 : List (List CardInstance) :=
  [ [fne4, fne5, flr6, flr7], [fne4, fne5, flr7, flr6],
    [fne4, flr6, fne5, flr7], [fne4, flr6, flr7, fne5],
    [fne4, flr7, fne5, flr6], [fne4, flr7, flr6, fne5],
    [fne5, fne4, flr6, flr7], [fne5, fne4, flr7, flr6],
    [fne5, flr6, fne4, flr7], [fne5, flr6, flr7, fne4],
    [fne5, flr7, fne4, flr6], [fne5, flr7, flr6, fne4],
    [flr6, fne4, fne5, flr7], [flr6, fne4, flr7, fne5],
    [flr6, fne5, fne4, flr7], [flr6, fne5, flr7, fne4],
    [flr6, flr7, fne4, fne5], [flr6, flr7, fne5, fne4],
    [flr7, fne4, fne5, flr6], [flr7, fne4, flr6, fne5],
    [flr7, fne5, fne4, flr6], [flr7, fne5, flr6, fne4],
    [flr7, flr6, fne4, fne5], [flr7, flr6, fne5, fne4] ]

private def allPerms2 (sh1 : List CardInstance) : List (List CardInstance) :=
  let p2 := mkPile2 sh1
  match p2 with
  | [x, y] => [[x, y], [y, x]]
  | _ => []

private def verifyAll : Bool :=
  allPerms4.all fun sh1 => (allPerms2 sh1).all fun sh2 => verifyOne sh1 sh2

-- Single native_decide for all 48 cases (concrete engine computation)
theorem all_verified : verifyAll = true := by native_decide

-- Extract individual case
private theorem verifyOne_of_mem (sh1 sh2 : List CardInstance)
    (h1 : sh1 ∈ allPerms4) (h2 : sh2 ∈ allPerms2 sh1) :
    verifyOne sh1 sh2 = true := by
  have hva := all_verified
  unfold verifyAll at hva
  rw [List.all_eq_true] at hva
  have h1' := hva sh1 h1
  rw [List.all_eq_true] at h1'
  exact h1' sh2 h2

-- ============================================================
-- CASE HANDLER
-- ============================================================

/-- Given concrete sh1 and sh2 with membership proofs, and proofs that oracle agrees,
    produce the existential witness. p2 is the concrete pile for the second shuffle. -/
private theorem case_handler (sh1 sh2 p2 : List CardInstance)
    (hmem1 : sh1 ∈ allPerms4) (hmem2 : sh2 ∈ allPerms2 sh1)
    (hp2 : mkPile2 sh1 = p2)
    (oracle : ShuffleOracle)
    (h0 : oracle 0 pile1 = sh1)
    (h1 : oracle 1 p2 = sh2) :
    ∃ (loopTrace : List Action) (stateB : GameState) (finalIdx : Nat),
      executeL2 cardDB oracle 0 stateA loopTrace = some (stateB, finalIdx)
      ∧ noEndTurn loopTrace = true
      ∧ sameModAccum stateA stateB = true
      ∧ dealtDamage stateA stateB = true := by
  have hv := verifyOne_of_mem sh1 sh2 hmem1 hmem2
  unfold verifyOne at hv
  have hf0 : oracle 0 pile1 = fixedOracle sh1 sh2 0 pile1 := by
    simp only [fixedOracle]; exact h0
  have hf1 : oracle 1 (mkPile2 sh1) = fixedOracle sh1 sh2 1 (mkPile2 sh1) := by
    simp only [fixedOracle]; rw [hp2]; exact h1
  generalize hres : executeL2 cardDB (fixedOracle sh1 sh2) 0 stateA (mkLoopTrace sh1 sh2) = result at hv
  match result, hv with
  | some (stB, fIdx), hv =>
    simp only [Bool.and_eq_true] at hv
    obtain ⟨⟨⟨hsm, hdd⟩, hdc⟩, hne⟩ := hv
    have hbridge := drawCondBool_bridge oracle (fixedOracle sh1 sh2) pile1 (mkPile2 sh1) hf0 hf1 0 stateA
      (mkLoopTrace sh1 sh2) hdc
    exact ⟨mkLoopTrace sh1 sh2, stB, fIdx, hbridge ▸ hres, hne, hsm, hdd⟩
  | none, hv => simp at hv



-- ============================================================
-- MAIN THEOREM
-- ============================================================

set_option maxHeartbeats 8000000 in
theorem ComboTantrumFearNoEvil_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  have hPerm1 : List.Perm (oracle 0 pile1) pile1 := hValid 0 pile1
  have h4 := perm_4_ci (oracle 0 pile1) hPerm1
  rcases h4 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 |
                 h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 |
                 h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> (
    have hPerm2 : (oracle 1 (mkPile2 (oracle 0 pile1))).Perm (mkPile2 (oracle 0 pile1)) :=
      hValid 1 (mkPile2 (oracle 0 pile1))
    rw [h1] at hPerm2
    simp (config := { decide := true }) only [mkPile2, pickFirstFlurry, pickFirstFNE, isFlurry, isFNE,
      fne4, fne5, flr6, flr7, ite_true, ite_false] at hPerm2
    have h2cases := perm_2_ci _ _ _ (by decide) hPerm2
    rcases h2cases with h2 | h2 <;> (
      -- h2 : oracle 1 [concrete_p2] = [concrete_sh2]
      -- case_handler needs: sh1 (from h1), sh2 (from h2's RHS), p2 (from h2's LHS), hp2 : mkPile2 sh1 = p2
      -- sh1, sh2, p2 are all inferred from h1 and h2
      -- hp2 is proved by decide (both sides are concrete after sh1 is known)
      exact case_handler _ _ _
        (by simp only [allPerms4, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false]; simp)
        (by simp (config := { decide := true }) only [allPerms2, mkPile2, pickFirstFlurry,
              pickFirstFNE, isFlurry, isFNE, fne4, fne5, flr6, flr7, ite_true, ite_false,
              List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false])
        (by simp (config := { decide := true }) only [mkPile2, pickFirstFlurry,
              pickFirstFNE, isFlurry, isFNE, fne4, fne5, flr6, flr7, ite_true, ite_false])
        oracle h1 h2
    )
  )

end ComboTantrumFearNoEvil_L2_Strict
