/-
  Storm of Steel+ + Tactician+ + Reflex+ + Prepared+ (4 cards) - Level 2
  v3 engine: resolveCard via autoDrain.
  stateA: all 4 in hand. Two loop variants depending on oracle.
-/

import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB

open CardName Action

namespace ComboStormOfSteel_L2

private def ci0 : CardInstance := { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }
private def ci1 : CardInstance := { id := 1, name := TacticianPlus, cost := 0, damage := 0 }
private def ci2 : CardInstance := { id := 2, name := ReflexPlus, cost := 0, damage := 0 }
private def ci3 : CardInstance := { id := 3, name := PreparedPlus, cost := 0, damage := 0 }

def cards : List (CardName × Nat) := [
  (StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1), (PreparedPlus, 1)]
def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .failDraw,
  .play 0, .draw 1, .draw 2, .draw 3,
  .play 4, .play 5, .play 6,
  .play 3, .draw 0, .failDraw, .discard 2, .discard 1,
  .draw 3, .draw 1, .draw 2
]

def stateA : GameState := {
  hand := [ci2, ci1, ci3, ci0], drawPile := [], discardPile := []
  exhaustPile := [{ id := 6, name := Shiv, cost := 0, damage := 4 },
                  { id := 5, name := Shiv, cost := 0, damage := 4 },
                  { id := 4, name := Shiv, cost := 0, damage := 4 }]
  inUse := [], actionQueue := []
  energy := 6, damage := 12, block := 0, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [], nextId := 7, noDraw := false, corruptionActive := false
}

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- Piles
private def pile0 : List CardInstance := [ci0, ci2, ci1, ci3]
private def pile1_ns : List CardInstance := [ci3, ci1, ci2]
private def pile2_ps : List CardInstance := [ci3, ci1, ci2]
private def mkPile1_ps (sh0 : List CardInstance) : List CardInstance :=
  match sh0 with
  | [a, b, c, _] => ci0 :: removeById [c, b, a] 0
  | _ => []

-- Traces
def mkLoopTrace_ns (sh0 sh1 : List CardInstance) : List Action :=
  match sh0, sh1 with
  | [a, b, c, d], [e, f, g] =>
    [.play 0, .draw a.id, .draw b.id, .draw c.id,
     .play 7, .play 8, .play 9,
     .play 3, .draw d.id, .failDraw, .discard 2, .discard 1,
     .draw e.id, .draw f.id, .draw g.id]
  | _, _ => []

def mkLoopTrace_ps (sh0 sh1 sh2 : List CardInstance) : List Action :=
  match sh0, sh1, sh2 with
  | [a, b, c, _], [d, e, f], [g, h, i] =>
    [.play 0, .draw a.id, .draw b.id, .draw c.id,
     .play 7, .play 8, .play 9,
     .play 0, .draw 3, .draw d.id, .draw e.id,
     .play 10, .play 11,
     .play 3, .draw f.id, .failDraw, .discard 2, .discard 1,
     .draw g.id, .draw h.id, .draw i.id]
  | _, _, _ => []

-- Fixed oracles
def fixedOracle_ns (sh0 sh1 : List CardInstance) : ShuffleOracle := fun idx _ =>
  if idx == 0 then sh0 else if idx == 1 then sh1 else []
def fixedOracle_ps (sh0 sh1 sh2 : List CardInstance) : ShuffleOracle := fun idx _ =>
  if idx == 0 then sh0 else if idx == 1 then sh1 else if idx == 2 then sh2 else []

-- drawCondBool NS
private def drawCondBool_ns (fo : ShuffleOracle) (si : Nat) (s : GameState)
    : List Action → Bool
  | [] => true
  | a :: rest =>
    let sc := autoDrain cardDB s
    let dpOk := match a with
      | .draw _ => sc.drawPile.length > 0 ||
                   (decide (si = 0) && decide (sc.discardPile = pile0)) ||
                   (decide (si = 1) && decide (sc.discardPile = pile1_ns))
      | _ => true
    match stepL2 cardDB fo si sc a with
    | some (s', si') => dpOk && drawCondBool_ns fo si' s' rest
    | none => false

-- drawCondBool PS
private def drawCondBool_ps (fo : ShuffleOracle) (p1 : List CardInstance)
    (si : Nat) (s : GameState) : List Action → Bool
  | [] => true
  | a :: rest =>
    let sc := autoDrain cardDB s
    let dpOk := match a with
      | .draw _ => sc.drawPile.length > 0 ||
                   (decide (si = 0) && decide (sc.discardPile = pile0)) ||
                   (decide (si = 1) && decide (sc.discardPile = p1)) ||
                   (decide (si = 2) && decide (sc.discardPile = pile2_ps))
      | _ => true
    match stepL2 cardDB fo si sc a with
    | some (s', si') => dpOk && drawCondBool_ps fo p1 si' s' rest
    | none => false

-- Bridge NS
private theorem drawCondBool_ns_bridge (oracle fo : ShuffleOracle)
    (h0 : oracle 0 pile0 = fo 0 pile0) (h1 : oracle 1 pile1_ns = fo 1 pile1_ns)
    (si : Nat) (s : GameState) (trace : List Action)
    (hb : drawCondBool_ns fo si s trace = true) :
    executeL2 cardDB oracle si s trace = executeL2 cardDB fo si s trace := by
  induction trace generalizing si s with
  | nil => rfl
  | cons a rest ih =>
    simp only [drawCondBool_ns] at hb
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

-- Bridge PS
private theorem drawCondBool_ps_bridge (oracle fo : ShuffleOracle) (p1 : List CardInstance)
    (h0 : oracle 0 pile0 = fo 0 pile0) (h1 : oracle 1 p1 = fo 1 p1)
    (h2 : oracle 2 pile2_ps = fo 2 pile2_ps)
    (si : Nat) (s : GameState) (trace : List Action)
    (hb : drawCondBool_ps fo p1 si s trace = true) :
    executeL2 cardDB oracle si s trace = executeL2 cardDB fo si s trace := by
  induction trace generalizing si s with
  | nil => rfl
  | cons a rest ih =>
    simp only [drawCondBool_ps] at hb
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
            rcases hdpOk with (⟨h_si, h_disc⟩ | ⟨h_si, h_disc⟩) | ⟨h_si, h_disc⟩
            · subst h_si; rw [h_disc]; exact h0
            · subst h_si; rw [h_disc]; exact h1
            · subst h_si; rw [h_disc]; exact h2
          · left; exact hdp
        | _ => rfl
      show (let sc := autoDrain cardDB s
            match stepL2 cardDB oracle si sc a with
            | none => none | some (s'', si'') => executeL2 cardDB oracle si'' s'' rest) =
           (let sc := autoDrain cardDB s
            match stepL2 cardDB fo si sc a with
            | none => none | some (s'', si'') => executeL2 cardDB fo si'' s'' rest)
      simp only [h_step_eq, hfo]; exact ih si' s' hrest

-- Enumeration (all possible oracle outputs)
private def isPS (sh0 : List CardInstance) : Bool :=
  match sh0 with | [_, _, _, d] => d == ci3 | _ => false

private def allPerms4 : List (List CardInstance) :=
  [ [ci0,ci2,ci1,ci3],[ci0,ci2,ci3,ci1],[ci0,ci1,ci2,ci3],[ci0,ci1,ci3,ci2],[ci0,ci3,ci2,ci1],[ci0,ci3,ci1,ci2],
    [ci2,ci0,ci1,ci3],[ci2,ci0,ci3,ci1],[ci2,ci1,ci0,ci3],[ci2,ci1,ci3,ci0],[ci2,ci3,ci0,ci1],[ci2,ci3,ci1,ci0],
    [ci1,ci0,ci2,ci3],[ci1,ci0,ci3,ci2],[ci1,ci2,ci0,ci3],[ci1,ci2,ci3,ci0],[ci1,ci3,ci0,ci2],[ci1,ci3,ci2,ci0],
    [ci3,ci0,ci2,ci1],[ci3,ci0,ci1,ci2],[ci3,ci2,ci0,ci1],[ci3,ci2,ci1,ci0],[ci3,ci1,ci0,ci2],[ci3,ci1,ci2,ci0] ]

private def allPerms3 : List (List CardInstance) :=
  [ [ci3,ci1,ci2],[ci3,ci2,ci1],[ci1,ci3,ci2],[ci1,ci2,ci3],[ci2,ci3,ci1],[ci2,ci1,ci3] ]

private def allPerms3of (pile : List CardInstance) : List (List CardInstance) :=
  match pile with
  | [a, b, c] => [ [a,b,c],[a,c,b],[b,a,c],[b,c,a],[c,a,b],[c,b,a] ]
  | _ => []

private def verifyOne_ns (sh0 sh1 : List CardInstance) : Bool :=
  let fo := fixedOracle_ns sh0 sh1
  let trace := mkLoopTrace_ns sh0 sh1
  match executeL2 cardDB fo 0 stateA trace with
  | some (stateB, _) =>
    sameModAccum stateA stateB && dealtDamage stateA stateB &&
    drawCondBool_ns fo 0 stateA trace && noEndTurn trace
  | none => false

private def verifyOne_ps (sh0 sh1 sh2 : List CardInstance) : Bool :=
  let p1 := mkPile1_ps sh0
  let fo := fixedOracle_ps sh0 sh1 sh2
  let trace := mkLoopTrace_ps sh0 sh1 sh2
  match executeL2 cardDB fo 0 stateA trace with
  | some (stateB, _) =>
    sameModAccum stateA stateB && dealtDamage stateA stateB &&
    drawCondBool_ps fo p1 0 stateA trace && noEndTurn trace
  | none => false

private def verifyAll : Bool :=
  allPerms4.all fun sh0 =>
    if isPS sh0 then
      (allPerms3of (mkPile1_ps sh0)).all fun sh1 =>
        allPerms3.all fun sh2 => verifyOne_ps sh0 sh1 sh2
    else
      allPerms3.all fun sh1 => verifyOne_ns sh0 sh1

set_option maxHeartbeats 16000000 in
theorem all_verified : verifyAll = true := by native_decide

-- Perm membership
set_option maxHeartbeats 800000 in
private theorem perm4_mem (l : List CardInstance) (hp : l.Perm pile0) : l ∈ allPerms4 := by
  have hlen := hp.length_eq; simp [pile0] at hlen
  match l, hlen with
  | [a, b, c, d], _ =>
    have hmem : ∀ x ∈ [a, b, c, d], x = ci0 ∨ x = ci2 ∨ x = ci1 ∨ x = ci3 := by
      intro x hx; have hm := hp.subset hx
      simp [pile0, List.mem_cons, List.mem_nil_iff, or_false] at hm; exact hm
    have ha := hmem a (by simp); have hb := hmem b (by simp)
    have hc := hmem c (by simp); have hd := hmem d (by simp)
    have hnd : [a, b, c, d].Nodup := hp.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or,
               List.not_mem_nil, not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd, _⟩ := hnd
    rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> (try exact absurd rfl hab) <;>
    rcases hc with rfl | rfl | rfl | rfl <;> (try exact absurd rfl hac) <;> (try exact absurd rfl hbc) <;>
    rcases hd with rfl | rfl | rfl | rfl <;> (try exact absurd rfl had) <;> (try exact absurd rfl hbd) <;> (try exact absurd rfl hcd) <;>
    simp [allPerms4, ci0, ci1, ci2, ci3]

set_option maxHeartbeats 800000 in
private theorem perm3_mem (l : List CardInstance) (hp : l.Perm pile1_ns) : l ∈ allPerms3 := by
  have hlen := hp.length_eq; simp [pile1_ns] at hlen
  match l, hlen with
  | [x, y, z], _ =>
    have hx : x ∈ pile1_ns := hp.mem_iff.mp (by simp)
    have hy : y ∈ pile1_ns := hp.mem_iff.mp (by simp)
    have hz : z ∈ pile1_ns := hp.mem_iff.mp (by simp)
    simp only [pile1_ns, ci1, ci2, ci3, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy hz
    have hnd : [x, y, z].Nodup := hp.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or, List.not_mem_nil,
               not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hxy, hxz⟩, hyz, _⟩ := hnd
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      (try exact absurd rfl hxy) <;> rcases hz with rfl | rfl | rfl <;>
      (try exact absurd rfl hxz) <;> (try exact absurd rfl hyz) <;>
      simp [allPerms3, ci1, ci2, ci3]

-- PS pile membership: mkPile1_ps sh0 only produces 2 possible piles.
-- We prove membership by first showing mkPile1_ps sh0 is one of two concrete values,
-- then proving perm membership for each.
-- Both piles have the same elements {ci0,ci1,ci2}, so we unify via a single perm3 lemma.
private def pile_012 : List CardInstance := [ci0, ci1, ci2]

set_option maxHeartbeats 800000 in
private theorem mkPile1_ps_is_perm_012 (sh0 : List CardInstance) (hsh0 : sh0 ∈ allPerms4)
    (hps : isPS sh0 = true) : (mkPile1_ps sh0).Perm pile_012 := by
  simp only [allPerms4, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hsh0
  rcases hsh0 with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | native_decide | (exfalso; revert hps; native_decide)

set_option maxHeartbeats 800000 in
private theorem perm3_mem_012 (l : List CardInstance) (hp : l.Perm pile_012) : l ∈ allPerms3of pile_012 := by
  have hlen := hp.length_eq; simp [pile_012] at hlen
  match l, hlen with
  | [x, y, z], _ =>
    have hx := hp.mem_iff.mp (List.mem_cons_self x _)
    have hy := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_self y _))
    have hz := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self z _)))
    simp only [pile_012, ci0, ci1, ci2, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy hz
    have hnd : [x, y, z].Nodup := hp.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or, List.not_mem_nil,
               not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hxy, hxz⟩, hyz, _⟩ := hnd
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      (try exact absurd rfl hxy) <;> rcases hz with rfl | rfl | rfl <;>
      (try exact absurd rfl hxz) <;> (try exact absurd rfl hyz) <;>
      simp [allPerms3of, pile_012, ci0, ci1, ci2]

-- The allPerms3of (mkPile1_ps sh0) = allPerms3of pile_012 when mkPile1_ps sh0 is a perm of pile_012
-- We prove: l ∈ allPerms3of (mkPile1_ps sh0) via the perm relationship.
-- Actually we need: if l.Perm (mkPile1_ps sh0), then l ∈ allPerms3of (mkPile1_ps sh0).
-- Since mkPile1_ps sh0 is a perm of pile_012, l is also a perm of pile_012.
-- But allPerms3of (mkPile1_ps sh0) lists perms of that specific list.
-- We need a separate approach: enumerate allPerms3of for each concrete mkPile1_ps value.
-- Since verifyAll already validates all combinations, we just need membership.
-- Let's use native_decide on the concrete membership check.

-- For PS cases, prove l ∈ allPerms3of (mkPile1_ps sh0) using the same 3-element approach
-- but for each concrete mkPile1_ps value.
-- mkPile1_ps for the 6 PS sh0 values gives either [ci0,ci1,ci2] or [ci0,ci2,ci1].
-- We handle each concretely.

set_option maxHeartbeats 6400000 in
private theorem perm3of_mem_ps (sh0 l : List CardInstance)
    (hsh0 : sh0 ∈ allPerms4) (hps : isPS sh0 = true)
    (hp : l.Perm (mkPile1_ps sh0)) : l ∈ allPerms3of (mkPile1_ps sh0) := by
  -- Concretize sh0, prove mkPile1_ps sh0 = concrete, rewrite, then prove perm membership
  simp only [allPerms4, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hsh0
  rcases hsh0 with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> (
    first
    | (exfalso; revert hps; native_decide)
    | (-- Prove mkPile1_ps [concrete] = [concrete] and rewrite
       simp (config := { decide := true }) only [mkPile1_ps, removeById, findById, ci0, ci1, ci2, ci3, ite_true, ite_false] at hp ⊢
       -- Now hp : l.Perm [concrete list], goal : l ∈ allPerms3of [concrete list]
       -- allPerms3of [a,b,c] reduces to 6-element list. Use perm3 membership.
       have hlen := hp.length_eq; simp at hlen
       match l, hlen with
       | [x, y, z], _ =>
         have hx := hp.mem_iff.mp (List.mem_cons_self x _)
         have hy := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_self y _))
         have hz := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self z _)))
         simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy hz
         have hnd : [x, y, z].Nodup := hp.nodup_iff.mpr (by decide)
         simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or,
                    List.not_mem_nil, not_false_eq_true, and_true, and_self] at hnd
         obtain ⟨⟨hxy, hxz⟩, hyz, _⟩ := hnd
         rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
           (try exact absurd rfl hxy) <;> rcases hz with rfl | rfl | rfl <;>
           (try exact absurd rfl hxz) <;> (try exact absurd rfl hyz) <;>
           simp [allPerms3of])
  )

-- Case handlers (same as before)
private theorem handle_ns (sh0 sh1 : List CardInstance)
    (hmem0 : sh0 ∈ allPerms4) (hns : isPS sh0 = false) (hmem1 : sh1 ∈ allPerms3)
    (oracle : ShuffleOracle)
    (h0 : oracle 0 pile0 = sh0) (h1 : oracle 1 pile1_ns = sh1) :
    ∃ t sB fi, executeL2 cardDB oracle 0 stateA t = some (sB, fi)
      ∧ noEndTurn t = true ∧ sameModAccum stateA sB = true ∧ dealtDamage stateA sB = true := by
  have hva := all_verified; unfold verifyAll at hva; rw [List.all_eq_true] at hva
  have h0' := hva sh0 hmem0; simp only [hns, List.all_eq_true, show (false = true) = False from by decide, ite_false] at h0'
  have hv := h0' sh1 hmem1
  simp only [verifyOne_ns] at hv
  split at hv
  · next stB fIdx heq =>
    simp only [Bool.and_eq_true] at hv; obtain ⟨⟨⟨hsm, hdd⟩, hdc⟩, hne⟩ := hv
    have hf0 : oracle 0 pile0 = fixedOracle_ns sh0 sh1 0 pile0 := by simp [fixedOracle_ns]; exact h0
    have hf1 : oracle 1 pile1_ns = fixedOracle_ns sh0 sh1 1 pile1_ns := by simp [fixedOracle_ns]; exact h1
    exact ⟨_, stB, fIdx, (drawCondBool_ns_bridge oracle _ hf0 hf1 0 stateA _ hdc) ▸ heq, hne, hsm, hdd⟩
  · simp at hv

private theorem handle_ps (sh0 sh1 sh2 : List CardInstance)
    (hmem0 : sh0 ∈ allPerms4) (hps : isPS sh0 = true)
    (hmem1 : sh1 ∈ allPerms3of (mkPile1_ps sh0)) (hmem2 : sh2 ∈ allPerms3)
    (oracle : ShuffleOracle)
    (h0 : oracle 0 pile0 = sh0) (h1 : oracle 1 (mkPile1_ps sh0) = sh1) (h2 : oracle 2 pile2_ps = sh2) :
    ∃ t sB fi, executeL2 cardDB oracle 0 stateA t = some (sB, fi)
      ∧ noEndTurn t = true ∧ sameModAccum stateA sB = true ∧ dealtDamage stateA sB = true := by
  have hva := all_verified; unfold verifyAll at hva; rw [List.all_eq_true] at hva
  have h0' := hva sh0 hmem0; simp only [hps, List.all_eq_true, show (true = true) = True from by decide, ite_true] at h0'
  have hv := h0' sh1 hmem1 sh2 hmem2
  simp only [verifyOne_ps] at hv
  split at hv
  · next stB fIdx heq =>
    simp only [Bool.and_eq_true] at hv; obtain ⟨⟨⟨hsm, hdd⟩, hdc⟩, hne⟩ := hv
    have hf0 : oracle 0 pile0 = fixedOracle_ps sh0 sh1 sh2 0 pile0 := by simp [fixedOracle_ps]; exact h0
    have hf1 : oracle 1 (mkPile1_ps sh0) = fixedOracle_ps sh0 sh1 sh2 1 (mkPile1_ps sh0) := by
      simp [fixedOracle_ps]; exact h1
    have hf2 : oracle 2 pile2_ps = fixedOracle_ps sh0 sh1 sh2 2 pile2_ps := by simp [fixedOracle_ps]; exact h2
    exact ⟨_, stB, fIdx, (drawCondBool_ps_bridge oracle _ _ hf0 hf1 hf2 0 stateA _ hdc) ▸ heq, hne, hsm, hdd⟩
  · simp at hv

-- Main theorem
theorem ComboStormOfSteel_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  have hsh0_mem := perm4_mem (oracle 0 pile0) (hValid 0 pile0)
  cases hps : isPS (oracle 0 pile0)
  · have hsh1_mem := perm3_mem (oracle 1 pile1_ns) (hValid 1 pile1_ns)
    exact handle_ns _ _ hsh0_mem hps hsh1_mem oracle rfl rfl
  · have hsh1_mem := perm3of_mem_ps (oracle 0 pile0) (oracle 1 (mkPile1_ps (oracle 0 pile0)))
      hsh0_mem hps (hValid 1 (mkPile1_ps (oracle 0 pile0)))
    have hsh2_mem := perm3_mem (oracle 2 pile2_ps) (hValid 2 pile2_ps)
    exact handle_ps _ _ _ hsh0_mem hps hsh1_mem hsh2_mem oracle rfl rfl rfl

end ComboStormOfSteel_L2
