/-
  Storm of Steel+ + Tactician+ + Reflex+ + 2x Prepared+ (5 cards) - Level 2
  v3 engine: resolveCard via autoDrain.
  stateA: all 5 in hand. Two loop variants depending on oracle.
  Adaptive double-SoS strategy:
    Variant A (NS): draw 3 includes >= 1 Prep. Play SoS once, then Prep.
    Variant B (PS): draw 3 includes 0 Preps. Play SoS twice, then Prep.
-/

import StSVerify.CombosSpecL2.ComboStormOfSteel2Prep
import StSVerify.EngineHelperLemmas

open CardName Action

namespace ComboStormOfSteel2Prep_L2

private def ci0 : CardInstance := { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }
private def ci1 : CardInstance := { id := 1, name := TacticianPlus, cost := 0, damage := 0 }
private def ci2 : CardInstance := { id := 2, name := ReflexPlus, cost := 0, damage := 0 }
private def ci3 : CardInstance := { id := 3, name := PreparedPlus, cost := 0, damage := 0 }
private def ci4 : CardInstance := { id := 4, name := PreparedPlus, cost := 0, damage := 0 }

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4
]

def stateA : GameState := {
  hand := [ci4, ci3, ci2, ci1, ci0], drawPile := [], discardPile := []
  exhaustPile := []
  inUse := [], actionQueue := []
  energy := 3, damage := 0, block := 0, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [], nextId := 5, noDraw := false, corruptionActive := false
}

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- ============================================================
-- Pile definitions
-- ============================================================

-- Discard pile when shuffle #0 fires (after SoS play, all 5 cards)
private def pile0 : List CardInstance := [ci0, ci4, ci3, ci2, ci1]

-- NS: pile1 depends on which Prep is played (the first Prep in top 3)
private def pile1_ns3 : List CardInstance := [ci3, ci1, ci2]
private def pile1_ns4 : List CardInstance := [ci4, ci1, ci2]

-- NS pile1 computed from sh0
private def mkPile1_ns (sh0 : List CardInstance) : List CardInstance :=
  match sh0 with
  | [a, b, c, _, _] =>
    let prep := if a.name == PreparedPlus then a
                else if b.name == PreparedPlus then b else c
    [prep, ci1, ci2]
  | _ => []

-- PS: pile1 depends on sh0 (discard after 2nd SoS)
private def mkPile1_ps (sh0 : List CardInstance) : List CardInstance :=
  match sh0 with
  | [a, b, c, _, _] => ci0 :: removeById [c, b, a] 0
  | _ => []

-- PS: pile2 depends on which Prep is at sh0[3] (the first stranded Prep played)
private def mkPile2_ps (sh0 : List CardInstance) : List CardInstance :=
  match sh0 with
  | [_, _, _, d, _] => [d, ci1, ci2]
  | _ => []

-- ============================================================
-- Case classification
-- ============================================================

-- PS: no Prep in top 3 of shuffle
private def isPS (sh0 : List CardInstance) : Bool :=
  match sh0 with
  | [a, b, c, _, _] => a.name != PreparedPlus && b.name != PreparedPlus && c.name != PreparedPlus
  | _ => false

-- ============================================================
-- Trace constructors
-- ============================================================

-- NS trace: play SoS once, then Prep
def mkLoopTrace_ns (sh0 sh1 : List CardInstance) : List Action :=
  match sh0, sh1 with
  | [a, b, c, d, e], [f, g, h] =>
    let prepId := if a.name == PreparedPlus then a.id
                  else if b.name == PreparedPlus then b.id else c.id
    [.play 0,                                -- SoS: 4 Shivs + triggers, draw 3
     .draw a.id, .draw b.id, .draw c.id,    -- draw top 3
     .play 5, .play 6, .play 7, .play 8,    -- play 4 Shivs
     .play prepId,                           -- play first Prep in top 3
     .draw d.id, .draw e.id,                -- draw 2 stranded
     .discard 2, .discard 1,                -- discard Reflex, Tact (triggers)
     .draw f.id, .draw g.id, .draw h.id]    -- draw 3 from shuffle#1
  | _, _ => []

-- PS trace: play SoS twice, then Prep
def mkLoopTrace_ps (sh0 sh1 sh2 : List CardInstance) : List Action :=
  match sh0, sh1, sh2 with
  | [a, b, c, d, e], [f, g, h], [i, j, k] =>
    [.play 0,                                -- SoS#1: 4 Shivs + triggers
     .draw a.id, .draw b.id, .draw c.id,    -- draw top 3 (no Preps)
     .play 5, .play 6, .play 7, .play 8,    -- play 4 Shivs
     .play 0,                                -- SoS#2: 2 Shivs + triggers
     .draw d.id, .draw e.id,                -- draw 2 stranded Preps from drawPile
     .draw f.id,                             -- draw 1 from shuffle#1
     .play 9, .play 10,                     -- play 2 Shivs
     .play d.id,                             -- play first stranded Prep
     .draw g.id, .draw h.id,                -- draw 2 remaining from shuffle#1
     .discard 2, .discard 1,                -- discard Reflex, Tact (triggers)
     .draw i.id, .draw j.id, .draw k.id]    -- draw 3 from shuffle#2
  | _, _, _ => []

-- ============================================================
-- Fixed oracles
-- ============================================================

def fixedOracle_ns (sh0 sh1 : List CardInstance) : ShuffleOracle := fun idx _ =>
  if idx == 0 then sh0 else if idx == 1 then sh1 else []

def fixedOracle_ps (sh0 sh1 sh2 : List CardInstance) : ShuffleOracle := fun idx _ =>
  if idx == 0 then sh0 else if idx == 1 then sh1 else if idx == 2 then sh2 else []

-- ============================================================
-- drawCondBool bridges
-- ============================================================

private def drawCondBool_ns (fo : ShuffleOracle) (p1 : List CardInstance)
    (si : Nat) (s : GameState) : List Action → Bool
  | [] => true
  | a :: rest =>
    let sc := autoDrain cardDB s
    let dpOk := match a with
      | .draw _ => sc.drawPile.length > 0 ||
                   (decide (si = 0) && decide (sc.discardPile = pile0)) ||
                   (decide (si = 1) && decide (sc.discardPile = p1))
      | _ => true
    match stepL2 cardDB fo si sc a with
    | some (s', si') => dpOk && drawCondBool_ns fo p1 si' s' rest
    | none => false

private def drawCondBool_ps (fo : ShuffleOracle) (p1 p2 : List CardInstance)
    (si : Nat) (s : GameState) : List Action → Bool
  | [] => true
  | a :: rest =>
    let sc := autoDrain cardDB s
    let dpOk := match a with
      | .draw _ => sc.drawPile.length > 0 ||
                   (decide (si = 0) && decide (sc.discardPile = pile0)) ||
                   (decide (si = 1) && decide (sc.discardPile = p1)) ||
                   (decide (si = 2) && decide (sc.discardPile = p2))
      | _ => true
    match stepL2 cardDB fo si sc a with
    | some (s', si') => dpOk && drawCondBool_ps fo p1 p2 si' s' rest
    | none => false

-- Bridge NS
private theorem drawCondBool_ns_bridge (oracle fo : ShuffleOracle) (p1 : List CardInstance)
    (h0 : oracle 0 pile0 = fo 0 pile0) (h1 : oracle 1 p1 = fo 1 p1)
    (si : Nat) (s : GameState) (trace : List Action)
    (hb : drawCondBool_ns fo p1 si s trace = true) :
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
private theorem drawCondBool_ps_bridge (oracle fo : ShuffleOracle) (p1 p2 : List CardInstance)
    (h0 : oracle 0 pile0 = fo 0 pile0) (h1 : oracle 1 p1 = fo 1 p1)
    (h2 : oracle 2 p2 = fo 2 p2)
    (si : Nat) (s : GameState) (trace : List Action)
    (hb : drawCondBool_ps fo p1 p2 si s trace = true) :
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

-- ============================================================
-- Permutation enumeration
-- ============================================================

private def allPerms5 : List (List CardInstance) :=
  [ [ci0,ci1,ci2,ci3,ci4],[ci0,ci1,ci2,ci4,ci3],[ci0,ci1,ci3,ci2,ci4],[ci0,ci1,ci3,ci4,ci2],
    [ci0,ci1,ci4,ci2,ci3],[ci0,ci1,ci4,ci3,ci2],[ci0,ci2,ci1,ci3,ci4],[ci0,ci2,ci1,ci4,ci3],
    [ci0,ci2,ci3,ci1,ci4],[ci0,ci2,ci3,ci4,ci1],[ci0,ci2,ci4,ci1,ci3],[ci0,ci2,ci4,ci3,ci1],
    [ci0,ci3,ci1,ci2,ci4],[ci0,ci3,ci1,ci4,ci2],[ci0,ci3,ci2,ci1,ci4],[ci0,ci3,ci2,ci4,ci1],
    [ci0,ci3,ci4,ci1,ci2],[ci0,ci3,ci4,ci2,ci1],[ci0,ci4,ci1,ci2,ci3],[ci0,ci4,ci1,ci3,ci2],
    [ci0,ci4,ci2,ci1,ci3],[ci0,ci4,ci2,ci3,ci1],[ci0,ci4,ci3,ci1,ci2],[ci0,ci4,ci3,ci2,ci1],
    [ci1,ci0,ci2,ci3,ci4],[ci1,ci0,ci2,ci4,ci3],[ci1,ci0,ci3,ci2,ci4],[ci1,ci0,ci3,ci4,ci2],
    [ci1,ci0,ci4,ci2,ci3],[ci1,ci0,ci4,ci3,ci2],[ci1,ci2,ci0,ci3,ci4],[ci1,ci2,ci0,ci4,ci3],
    [ci1,ci2,ci3,ci0,ci4],[ci1,ci2,ci3,ci4,ci0],[ci1,ci2,ci4,ci0,ci3],[ci1,ci2,ci4,ci3,ci0],
    [ci1,ci3,ci0,ci2,ci4],[ci1,ci3,ci0,ci4,ci2],[ci1,ci3,ci2,ci0,ci4],[ci1,ci3,ci2,ci4,ci0],
    [ci1,ci3,ci4,ci0,ci2],[ci1,ci3,ci4,ci2,ci0],[ci1,ci4,ci0,ci2,ci3],[ci1,ci4,ci0,ci3,ci2],
    [ci1,ci4,ci2,ci0,ci3],[ci1,ci4,ci2,ci3,ci0],[ci1,ci4,ci3,ci0,ci2],[ci1,ci4,ci3,ci2,ci0],
    [ci2,ci0,ci1,ci3,ci4],[ci2,ci0,ci1,ci4,ci3],[ci2,ci0,ci3,ci1,ci4],[ci2,ci0,ci3,ci4,ci1],
    [ci2,ci0,ci4,ci1,ci3],[ci2,ci0,ci4,ci3,ci1],[ci2,ci1,ci0,ci3,ci4],[ci2,ci1,ci0,ci4,ci3],
    [ci2,ci1,ci3,ci0,ci4],[ci2,ci1,ci3,ci4,ci0],[ci2,ci1,ci4,ci0,ci3],[ci2,ci1,ci4,ci3,ci0],
    [ci2,ci3,ci0,ci1,ci4],[ci2,ci3,ci0,ci4,ci1],[ci2,ci3,ci1,ci0,ci4],[ci2,ci3,ci1,ci4,ci0],
    [ci2,ci3,ci4,ci0,ci1],[ci2,ci3,ci4,ci1,ci0],[ci2,ci4,ci0,ci1,ci3],[ci2,ci4,ci0,ci3,ci1],
    [ci2,ci4,ci1,ci0,ci3],[ci2,ci4,ci1,ci3,ci0],[ci2,ci4,ci3,ci0,ci1],[ci2,ci4,ci3,ci1,ci0],
    [ci3,ci0,ci1,ci2,ci4],[ci3,ci0,ci1,ci4,ci2],[ci3,ci0,ci2,ci1,ci4],[ci3,ci0,ci2,ci4,ci1],
    [ci3,ci0,ci4,ci1,ci2],[ci3,ci0,ci4,ci2,ci1],[ci3,ci1,ci0,ci2,ci4],[ci3,ci1,ci0,ci4,ci2],
    [ci3,ci1,ci2,ci0,ci4],[ci3,ci1,ci2,ci4,ci0],[ci3,ci1,ci4,ci0,ci2],[ci3,ci1,ci4,ci2,ci0],
    [ci3,ci2,ci0,ci1,ci4],[ci3,ci2,ci0,ci4,ci1],[ci3,ci2,ci1,ci0,ci4],[ci3,ci2,ci1,ci4,ci0],
    [ci3,ci2,ci4,ci0,ci1],[ci3,ci2,ci4,ci1,ci0],[ci3,ci4,ci0,ci1,ci2],[ci3,ci4,ci0,ci2,ci1],
    [ci3,ci4,ci1,ci0,ci2],[ci3,ci4,ci1,ci2,ci0],[ci3,ci4,ci2,ci0,ci1],[ci3,ci4,ci2,ci1,ci0],
    [ci4,ci0,ci1,ci2,ci3],[ci4,ci0,ci1,ci3,ci2],[ci4,ci0,ci2,ci1,ci3],[ci4,ci0,ci2,ci3,ci1],
    [ci4,ci0,ci3,ci1,ci2],[ci4,ci0,ci3,ci2,ci1],[ci4,ci1,ci0,ci2,ci3],[ci4,ci1,ci0,ci3,ci2],
    [ci4,ci1,ci2,ci0,ci3],[ci4,ci1,ci2,ci3,ci0],[ci4,ci1,ci3,ci0,ci2],[ci4,ci1,ci3,ci2,ci0],
    [ci4,ci2,ci0,ci1,ci3],[ci4,ci2,ci0,ci3,ci1],[ci4,ci2,ci1,ci0,ci3],[ci4,ci2,ci1,ci3,ci0],
    [ci4,ci2,ci3,ci0,ci1],[ci4,ci2,ci3,ci1,ci0],[ci4,ci3,ci0,ci1,ci2],[ci4,ci3,ci0,ci2,ci1],
    [ci4,ci3,ci1,ci0,ci2],[ci4,ci3,ci1,ci2,ci0],[ci4,ci3,ci2,ci0,ci1],[ci4,ci3,ci2,ci1,ci0] ]

private def allPerms3of (pile : List CardInstance) : List (List CardInstance) :=
  match pile with
  | [a, b, c] => [ [a,b,c],[a,c,b],[b,a,c],[b,c,a],[c,a,b],[c,b,a] ]
  | _ => []

-- ============================================================
-- Verification functions
-- ============================================================

private def verifyOne_ns (sh0 sh1 : List CardInstance) : Bool :=
  let p1 := mkPile1_ns sh0
  let fo := fixedOracle_ns sh0 sh1
  let trace := mkLoopTrace_ns sh0 sh1
  match executeL2 cardDB fo 0 stateA trace with
  | some (stateB, _) =>
    sameModAccum stateA stateB && dealtDamage stateA stateB &&
    drawCondBool_ns fo p1 0 stateA trace && noEndTurn trace
  | none => false

private def verifyOne_ps (sh0 sh1 sh2 : List CardInstance) : Bool :=
  let p1 := mkPile1_ps sh0
  let p2 := mkPile2_ps sh0
  let fo := fixedOracle_ps sh0 sh1 sh2
  let trace := mkLoopTrace_ps sh0 sh1 sh2
  match executeL2 cardDB fo 0 stateA trace with
  | some (stateB, _) =>
    sameModAccum stateA stateB && dealtDamage stateA stateB &&
    drawCondBool_ps fo p1 p2 0 stateA trace && noEndTurn trace
  | none => false

private def verifyAll : Bool :=
  allPerms5.all fun sh0 =>
    if isPS sh0 then
      (allPerms3of (mkPile1_ps sh0)).all fun sh1 =>
        (allPerms3of (mkPile2_ps sh0)).all fun sh2 => verifyOne_ps sh0 sh1 sh2
    else
      (allPerms3of (mkPile1_ns sh0)).all fun sh1 => verifyOne_ns sh0 sh1

set_option maxHeartbeats 80000000 in
theorem all_verified : verifyAll = true := by native_decide

-- ============================================================
-- Perm membership lemmas
-- ============================================================

set_option maxHeartbeats 3200000 in
private theorem perm5_mem (l : List CardInstance) (hp : l.Perm pile0) : l ∈ allPerms5 := by
  have hlen := hp.length_eq; simp [pile0] at hlen
  match l, hlen with
  | [a, b, c, d, e], _ =>
    have hmem : ∀ x ∈ [a, b, c, d, e], x = ci0 ∨ x = ci4 ∨ x = ci3 ∨ x = ci2 ∨ x = ci1 := by
      intro x hx; have hm := hp.subset hx
      simp [pile0, List.mem_cons, List.mem_nil_iff, or_false] at hm; exact hm
    have ha := hmem a (by simp); have hb := hmem b (by simp)
    have hc := hmem c (by simp); have hd := hmem d (by simp)
    have he := hmem e (by simp)
    have hnd : [a, b, c, d, e].Nodup := hp.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or,
               List.not_mem_nil, not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde, _⟩ := hnd
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> (try exact absurd rfl hab) <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> (try exact absurd rfl hac) <;> (try exact absurd rfl hbc) <;>
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> (try exact absurd rfl had) <;> (try exact absurd rfl hbd) <;> (try exact absurd rfl hcd) <;>
    rcases he with rfl | rfl | rfl | rfl | rfl <;> (try exact absurd rfl hae) <;> (try exact absurd rfl hbe) <;> (try exact absurd rfl hce) <;> (try exact absurd rfl hde) <;>
    simp [allPerms5, ci0, ci1, ci2, ci3, ci4]

-- NS: mkPile1_ns sh0 is either pile1_ns3 or pile1_ns4
set_option maxHeartbeats 6400000 in
private theorem mkPile1_ns_eq (sh0 : List CardInstance) (hsh0 : sh0 ∈ allPerms5)
    (hns : isPS sh0 = false) :
    mkPile1_ns sh0 = pile1_ns3 ∨ mkPile1_ns sh0 = pile1_ns4 := by
  simp only [allPerms5, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hsh0
  rcases hsh0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
  | (exfalso; revert hns; native_decide)
  | (left; native_decide)
  | (right; native_decide)

-- Perm3 membership for pile1_ns3 = [ci3, ci1, ci2]
set_option maxHeartbeats 800000 in
private theorem perm3_mem_312 (l : List CardInstance) (hp : l.Perm pile1_ns3) : l ∈ allPerms3of pile1_ns3 := by
  have hlen := hp.length_eq; simp [pile1_ns3] at hlen
  match l, hlen with
  | [x, y, z], _ =>
    have hx := hp.mem_iff.mp (List.mem_cons_self x _)
    have hy := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_self y _))
    have hz := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self z _)))
    simp only [pile1_ns3, ci1, ci2, ci3, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy hz
    have hnd : [x, y, z].Nodup := hp.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or, List.not_mem_nil,
               not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hxy, hxz⟩, hyz, _⟩ := hnd
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      (try exact absurd rfl hxy) <;> rcases hz with rfl | rfl | rfl <;>
      (try exact absurd rfl hxz) <;> (try exact absurd rfl hyz) <;>
      simp [allPerms3of, pile1_ns3, ci1, ci2, ci3]

-- Perm3 membership for pile1_ns4 = [ci4, ci1, ci2]
set_option maxHeartbeats 800000 in
private theorem perm3_mem_412 (l : List CardInstance) (hp : l.Perm pile1_ns4) : l ∈ allPerms3of pile1_ns4 := by
  have hlen := hp.length_eq; simp [pile1_ns4] at hlen
  match l, hlen with
  | [x, y, z], _ =>
    have hx := hp.mem_iff.mp (List.mem_cons_self x _)
    have hy := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_self y _))
    have hz := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self z _)))
    simp only [pile1_ns4, ci1, ci2, ci4, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy hz
    have hnd : [x, y, z].Nodup := hp.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or, List.not_mem_nil,
               not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hxy, hxz⟩, hyz, _⟩ := hnd
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      (try exact absurd rfl hxy) <;> rcases hz with rfl | rfl | rfl <;>
      (try exact absurd rfl hxz) <;> (try exact absurd rfl hyz) <;>
      simp [allPerms3of, pile1_ns4, ci1, ci2, ci4]

-- NS: perm membership for mkPile1_ns sh0
private theorem perm3of_mem_ns (sh0 l : List CardInstance)
    (hsh0 : sh0 ∈ allPerms5) (hns : isPS sh0 = false)
    (hp : l.Perm (mkPile1_ns sh0)) : l ∈ allPerms3of (mkPile1_ns sh0) := by
  rcases mkPile1_ns_eq sh0 hsh0 hns with h | h <;> rw [h] at hp ⊢
  · exact perm3_mem_312 l hp
  · exact perm3_mem_412 l hp

-- PS pile1 membership
set_option maxHeartbeats 12800000 in
private theorem perm3of_mem_ps1 (sh0 l : List CardInstance)
    (hsh0 : sh0 ∈ allPerms5) (hps : isPS sh0 = true)
    (hp : l.Perm (mkPile1_ps sh0)) : l ∈ allPerms3of (mkPile1_ps sh0) := by
  simp only [allPerms5, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hsh0
  rcases hsh0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (
    first
    | (exfalso; revert hps; native_decide)
    | (simp (config := { decide := true }) only [mkPile1_ps, removeById, findById, ci0, ci1, ci2, ci3, ci4, ite_true, ite_false] at hp ⊢
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

-- PS pile2 membership: mkPile2_ps sh0 is either [ci3,ci1,ci2] or [ci4,ci1,ci2]
private theorem mkPile2_ps_eq (sh0 : List CardInstance) (hsh0 : sh0 ∈ allPerms5)
    (hps : isPS sh0 = true) :
    mkPile2_ps sh0 = pile1_ns3 ∨ mkPile2_ps sh0 = pile1_ns4 := by
  simp only [allPerms5, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hsh0
  rcases hsh0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
  | (exfalso; revert hps; native_decide)
  | (left; native_decide)
  | (right; native_decide)

private theorem perm3of_mem_ps2 (sh0 l : List CardInstance)
    (hsh0 : sh0 ∈ allPerms5) (hps : isPS sh0 = true)
    (hp : l.Perm (mkPile2_ps sh0)) : l ∈ allPerms3of (mkPile2_ps sh0) := by
  rcases mkPile2_ps_eq sh0 hsh0 hps with h | h <;> rw [h] at hp ⊢
  · exact perm3_mem_312 l hp
  · exact perm3_mem_412 l hp

-- ============================================================
-- Case handlers
-- ============================================================

private theorem handle_ns (sh0 sh1 : List CardInstance)
    (hmem0 : sh0 ∈ allPerms5) (hns : isPS sh0 = false) (hmem1 : sh1 ∈ allPerms3of (mkPile1_ns sh0))
    (oracle : ShuffleOracle)
    (h0 : oracle 0 pile0 = sh0) (h1 : oracle 1 (mkPile1_ns sh0) = sh1) :
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
    have hf1 : oracle 1 (mkPile1_ns sh0) = fixedOracle_ns sh0 sh1 1 (mkPile1_ns sh0) := by simp [fixedOracle_ns]; exact h1
    exact ⟨_, stB, fIdx, (drawCondBool_ns_bridge oracle _ _ hf0 hf1 0 stateA _ hdc) ▸ heq, hne, hsm, hdd⟩
  · simp at hv

private theorem handle_ps (sh0 sh1 sh2 : List CardInstance)
    (hmem0 : sh0 ∈ allPerms5) (hps : isPS sh0 = true)
    (hmem1 : sh1 ∈ allPerms3of (mkPile1_ps sh0)) (hmem2 : sh2 ∈ allPerms3of (mkPile2_ps sh0))
    (oracle : ShuffleOracle)
    (h0 : oracle 0 pile0 = sh0) (h1 : oracle 1 (mkPile1_ps sh0) = sh1)
    (h2 : oracle 2 (mkPile2_ps sh0) = sh2) :
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
    have hf2 : oracle 2 (mkPile2_ps sh0) = fixedOracle_ps sh0 sh1 sh2 2 (mkPile2_ps sh0) := by simp [fixedOracle_ps]; exact h2
    exact ⟨_, stB, fIdx, (drawCondBool_ps_bridge oracle _ _ _ hf0 hf1 hf2 0 stateA _ hdc) ▸ heq, hne, hsm, hdd⟩
  · simp at hv

-- ============================================================
-- Main theorem
-- ============================================================

theorem ComboStormOfSteel2Prep_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  have hsh0_mem := perm5_mem (oracle 0 pile0) (hValid 0 pile0)
  cases hps : isPS (oracle 0 pile0)
  · -- NS case: at least one Prep in top 3
    have hsh1_mem := perm3of_mem_ns (oracle 0 pile0) (oracle 1 (mkPile1_ns (oracle 0 pile0)))
      hsh0_mem hps (hValid 1 (mkPile1_ns (oracle 0 pile0)))
    exact handle_ns _ _ hsh0_mem hps hsh1_mem oracle rfl rfl
  · -- PS case: no Prep in top 3, play SoS twice
    have hsh1_mem := perm3of_mem_ps1 (oracle 0 pile0) (oracle 1 (mkPile1_ps (oracle 0 pile0)))
      hsh0_mem hps (hValid 1 (mkPile1_ps (oracle 0 pile0)))
    have hsh2_mem := perm3of_mem_ps2 (oracle 0 pile0) (oracle 2 (mkPile2_ps (oracle 0 pile0)))
      hsh0_mem hps (hValid 2 (mkPile2_ps (oracle 0 pile0)))
    exact handle_ps _ _ _ hsh0_mem hps hsh1_mem hsh2_mem oracle rfl rfl rfl

theorem proof : GuaranteedInfiniteCombo cardDB cards enemy := ComboStormOfSteel2Prep_guaranteed_infinite

end ComboStormOfSteel2Prep_L2
