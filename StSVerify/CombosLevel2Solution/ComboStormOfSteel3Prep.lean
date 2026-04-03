/-
  Storm of Steel+ + Tactician+ + Reflex+ + 3x Prepared+ (6 cards) - Level 2
  v3 engine: resolveCard via autoDrain.
  stateA: all 6 in hand. Adaptive double-SoS strategy.
  Proof via case analysis (NS1/NS2/PS_fast/PS_slow) with drawCondBool bridges.
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
  .play 0, .draw 5, .draw 1, .draw 2,
  .play 6, .play 7, .play 8, .play 9,
  .play 5, .draw 0, .draw 4, .discard 2, .discard 1,
  .draw 3, .draw 2, .draw 1,
  .play 3, .draw 5, .failDraw, .discard 2, .discard 1,
  .draw 3, .draw 2, .draw 1]

def stateA : GameState := {
  hand := [ci1, ci2, ci3, ci5, ci4, ci0], drawPile := [], discardPile := []
  exhaustPile := [{ id := 9, name := Shiv, cost := 0, damage := 4 },
                  { id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 }]
  inUse := [], actionQueue := []
  energy := 8, damage := 16, block := 0, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [], nextId := 10, noDraw := false, corruptionActive := false
}

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- ============================================================
-- Definitions
-- ============================================================

private def pile0 : List CardInstance := [ci0, ci1, ci2, ci3, ci5, ci4]
private def isPrep (c : CardInstance) : Bool := c.name == PreparedPlus
private def isPS (sh0 : List CardInstance) : Bool :=
  match sh0 with | [a, b, c, _, _, _] => !isPrep a && !isPrep b && !isPrep c | _ => false
private def isNS2 (sh0 : List CardInstance) : Bool :=
  match sh0 with | [_, _, _, _, _, f] => f == ci2 | _ => false
private def firstPrepInTop3 (sh0 : List CardInstance) : CardInstance :=
  match sh0 with | [a, b, c, _, _, _] => if isPrep a then a else if isPrep b then b else c | _ => ci3
private def secondPrep (hand : List CardInstance) (first : CardInstance) : CardInstance :=
  match hand.find? (fun c => isPrep c && c.id != first.id) with | some p => p | none => ci4

private def allPerms6 : List (List CardInstance) :=
  let es := [ci0, ci1, ci2, ci3, ci4, ci5]
  es.flatMap fun a => (es.filter (· != a)).flatMap fun b =>
    (es.filter (fun c => c != a && c != b)).flatMap fun c =>
      (es.filter (fun d => d != a && d != b && d != c)).flatMap fun d =>
        (es.filter (fun e => e != a && e != b && e != c && e != d)).flatMap fun e =>
          (es.filter (fun f => f != a && f != b && f != c && f != d && f != e)).map fun f =>
            [a, b, c, d, e, f]

private def allPerms3of (pile : List CardInstance) : List (List CardInstance) :=
  match pile with | [a, b, c] => [[a,b,c],[a,c,b],[b,a,c],[b,c,a],[c,a,b],[c,b,a]] | _ => []

private def fixedOracle (shs : List (List CardInstance)) : ShuffleOracle := fun idx _ =>
  shs.getD idx []

-- ============================================================
-- Traces
-- ============================================================

def mkLoopTrace_ns1 (sh0 sh1 sh2 : List CardInstance) : List Action :=
  match sh0, sh1, sh2 with
  | [a, b, c, d, e, f], [g, h, i], [j, k, l] =>
    let p1 := firstPrepInTop3 sh0; let hand4 := [e, d] ++ removeById [c, b, a] p1.id
    let dOther := (hand4.find? (fun c => c.id != 2 && !isPrep c)).getD ci0
    let hand2 := hand4.filter (fun c => c.id != 2 && c.id != dOther.id)
    let hand5 := [h, g, f] ++ hand2; let p2 := secondPrep hand5 p1
    [.play 0, .draw a.id, .draw b.id, .draw c.id, .play 10, .play 11, .play 12, .play 13, .play 14,
     .play p1.id, .draw d.id, .draw e.id, .discard 2, .discard dOther.id,
     .draw f.id, .draw g.id, .draw h.id, .play p2.id, .draw i.id, .failDraw,
     .discard 1, .discard 2, .draw j.id, .draw k.id, .draw l.id]
  | _, _, _ => []

def mkLoopTrace_ns2 (sh0 sh1 sh2 sh3 : List CardInstance) : List Action :=
  match sh0, sh1, sh2, sh3 with
  | [a, b, c, d, e, _f], [g, h, i], [j, k, l], [m, n, o] =>
    let p1 := firstPrepInTop3 sh0; let hand4 := [e, d] ++ removeById [c, b, a] p1.id
    let hand2 := hand4.filter (fun c => c.id != 1 && c.id != 0)
    let p2 := match hand2.find? isPrep with | some p => p | none => ci4
    let kept := match hand2.filter (fun c => c.id != p2.id) with | [x] => x | _ => ci5
    let p3 := match ([j, kept] : List CardInstance).find?
        (fun c => isPrep c && c.id != p1.id && c.id != p2.id) with
      | some p => p | none => match ([j, kept] : List CardInstance).find? isPrep with
        | some p => p | none => ci5
    [.play 0, .draw a.id, .draw b.id, .draw c.id, .play 10, .play 11, .play 12, .play 13, .play 14,
     .play p1.id, .draw d.id, .draw e.id, .discard 1, .discard 0,
     .play p2.id, .draw 2, .draw g.id, .discard 2, .discard g.id,
     .draw h.id, .draw i.id, .draw j.id, .play p3.id, .draw k.id, .draw l.id,
     .discard 1, .discard 2, .draw m.id, .draw n.id, .draw o.id]
  | _, _, _, _ => []

def mkLoopTrace_ps_fast (sh0 sh1 sh2 sh3 : List CardInstance) : List Action :=
  match sh0, sh1, sh2, sh3 with
  | [a, b, c, d, e, f], [g, h, i], [j, k, l], [m, n, o] =>
    [.play 0, .draw a.id, .draw b.id, .draw c.id, .play 10, .play 11, .play 12, .play 13, .play 14,
     .play 0, .draw d.id, .draw e.id, .draw f.id, .play 15, .play 16,
     .play d.id, .draw g.id, .draw h.id, .discard g.id, .discard h.id,
     .draw i.id, .draw j.id, .draw k.id, .play e.id, .draw l.id, .failDraw,
     .discard 1, .discard 2, .draw m.id, .draw n.id, .draw o.id]
  | _, _, _, _ => []

def mkLoopTrace_ps_slow (sh0 sh1 sh2 sh3 sh4 : List CardInstance) : List Action :=
  match sh0, sh1, sh2, sh3, sh4 with
  | [a, b, c, d, e, f], [g, h, _i], [j, k, l], [m, n, o], [p, q, r] =>
    [.play 0, .draw a.id, .draw b.id, .draw c.id, .play 10, .play 11, .play 12, .play 13, .play 14,
     .play 0, .draw d.id, .draw e.id, .draw f.id, .play 15, .play 16,
     .play d.id, .draw g.id, .draw h.id, .discard 1, .discard 0,
     .play e.id, .draw 2, .draw j.id, .discard 2, .discard j.id,
     .draw k.id, .draw l.id, .draw m.id, .play f.id, .draw n.id, .draw o.id,
     .discard 1, .discard 2, .draw p.id, .draw q.id, .draw r.id]
  | _, _, _, _, _ => []

-- ============================================================
-- Piles
-- ============================================================

private def mkPile1_ns1 (sh0 : List CardInstance) : List CardInstance :=
  match sh0 with
  | [a, b, c, d, e, _f] => let p1 := firstPrepInTop3 sh0
    let hand4 := [e, d] ++ removeById [c, b, a] p1.id
    let dOther := (hand4.find? (fun c => c.id != 2 && !isPrep c)).getD ci0; [p1, dOther, ci2]
  | _ => []
private def mkPile2_ns1 (sh0 sh1 : List CardInstance) : List CardInstance :=
  match sh0, sh1 with
  | [a, b, c, d, e, f], [g, h, _i] => let p1 := firstPrepInTop3 sh0
    let hand4 := [e, d] ++ removeById [c, b, a] p1.id
    let dOther := (hand4.find? (fun c => c.id != 2 && !isPrep c)).getD ci0
    let hand2 := hand4.filter (fun c => c.id != 2 && c.id != dOther.id)
    let hand5 := [h, g, f] ++ hand2; let p2 := secondPrep hand5 p1; [p2, ci2, ci1]
  | _, _ => []
private def mkPile1_ns2 (sh0 : List CardInstance) : List CardInstance :=
  match sh0 with | [_, _, _, _, _, _] => [firstPrepInTop3 sh0, ci0, ci1] | _ => []
private def mkPile2_ns2 (sh0 sh1 : List CardInstance) : List CardInstance :=
  match sh0, sh1 with
  | [a, b, c, d, e, _f], [g, _, _] => let p1 := firstPrepInTop3 sh0
    let hand4 := [e, d] ++ removeById [c, b, a] p1.id
    let hand2 := hand4.filter (fun c => c.id != 1 && c.id != 0)
    let p2 := match hand2.find? isPrep with | some p => p | none => ci4; [p2, g, ci2]
  | _, _ => []
private def mkPile3_ns2 (sh0 sh1 sh2 : List CardInstance) : List CardInstance :=
  match sh0, sh1, sh2 with
  | [a, b, c, d, e, _f], [_g, h, i], [j, _k, _l] =>
    let p1 := firstPrepInTop3 sh0; let hand4 := [e, d] ++ removeById [c, b, a] p1.id
    let hand2 := hand4.filter (fun c => c.id != 1 && c.id != 0)
    let p2 := match hand2.find? isPrep with | some p => p | none => ci4
    let kept := match hand2.filter (fun c => c.id != p2.id) with | [x] => x | _ => ci5
    let p3 := match ([j, kept] : List CardInstance).find?
        (fun c => isPrep c && c.id != p1.id && c.id != p2.id) with
      | some p => p | none => match ([j, kept] : List CardInstance).find? isPrep with
        | some p => p | none => ci5
    [p3, ci2, ci1]
  | _, _, _ => []
private def mkPile1_ps (sh0 : List CardInstance) : List CardInstance :=
  match sh0 with | [a, b, c, _, _, _] => [ci0] ++ removeById [c, b, a] 0 | _ => []
private def mkPile2_ps (sh0 sh1 : List CardInstance) : List CardInstance :=
  match sh0, sh1 with | [_, _, _, d, _, _], [g, h, _] => [d, h, g] | _, _ => []
private def mkPile3_ps_fast (sh0 : List CardInstance) : List CardInstance :=
  match sh0 with | [_, _, _, _, e, _] => [e, ci2, ci1] | _ => []
private def mkPile2_ps_slow (sh0 : List CardInstance) : List CardInstance :=
  match sh0 with | [_, _, _, d, _, _] => [d, ci0, ci1] | _ => []
private def mkPile3_ps_slow (sh0 sh2 : List CardInstance) : List CardInstance :=
  match sh0, sh2 with | [_, _, _, _, e, _], [j, _, _] => [e, j, ci2] | _, _ => []
private def mkPile4_ps_slow (sh0 : List CardInstance) : List CardInstance :=
  match sh0 with | [_, _, _, _, _, f] => [f, ci2, ci1] | _ => []

-- ============================================================
-- drawCondBool (generic N-pile version using List.getD)
-- ============================================================

private def drawCondBoolN (fo : ShuffleOracle) (piles : List (List CardInstance))
    (si : Nat) (s : GameState) : List Action → Bool
  | [] => true
  | a :: rest =>
    let sc := autoDrain cardDB s
    let dpOk := match a with
      | .draw _ => sc.drawPile.length > 0 ||
        (si < piles.length && decide (sc.discardPile = piles.getD si []))
      | _ => true
    match stepL2 cardDB fo si sc a with
    | some (s', si') => dpOk && drawCondBoolN fo piles si' s' rest
    | none => false

private theorem drawCondBoolN_bridge (oracle fo : ShuffleOracle) (piles : List (List CardInstance))
    (hagree : ∀ i, i < piles.length → oracle i (piles.getD i []) = fo i (piles.getD i []))
    (si : Nat) (s : GameState) (trace : List Action)
    (hb : drawCondBoolN fo piles si s trace = true) :
    executeL2 cardDB oracle si s trace = executeL2 cardDB fo si s trace := by
  induction trace generalizing si s with
  | nil => rfl
  | cons a rest ih =>
    simp only [drawCondBoolN] at hb
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
            have : (autoDrain cardDB s).drawPile.length = 0 := by rw [hdp]; rfl
            simp only [this, Nat.lt_irrefl, decide_false, Bool.false_or] at hdpOk
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hdpOk
            rw [hdpOk.2]; exact hagree si hdpOk.1
          · left; exact hdp
        | _ => rfl
      show executeL2 cardDB oracle si s (a :: rest) = executeL2 cardDB fo si s (a :: rest)
      simp only [executeL2, h_step_eq, hfo]
      exact ih si' s' hrest

-- ============================================================
-- Verification (execution + drawCondBool combined)
-- ============================================================

private def verifyAll_ns : Bool :=
  allPerms6.all fun sh0 =>
    if isPS sh0 then true
    else if isNS2 sh0 then
      let p1 := mkPile1_ns2 sh0
      (allPerms3of p1).all fun sh1 =>
        let p2 := mkPile2_ns2 sh0 sh1
        (allPerms3of p2).all fun sh2 =>
          let p3 := mkPile3_ns2 sh0 sh1 sh2
          (allPerms3of p3).all fun sh3 =>
            let fo := fixedOracle [sh0, sh1, sh2, sh3]
            let tr := mkLoopTrace_ns2 sh0 sh1 sh2 sh3
            let piles := [pile0, p1, p2, p3]
            match executeL2 cardDB fo 0 stateA tr with
            | some (stateB, _) => sameModAccum stateA stateB && dealtDamage stateA stateB &&
                noEndTurn tr && drawCondBoolN fo piles 0 stateA tr
            | none => false
    else
      let p1 := mkPile1_ns1 sh0
      (allPerms3of p1).all fun sh1 =>
        let p2 := mkPile2_ns1 sh0 sh1
        (allPerms3of p2).all fun sh2 =>
          let fo := fixedOracle [sh0, sh1, sh2]
          let tr := mkLoopTrace_ns1 sh0 sh1 sh2
          let piles := [pile0, p1, p2]
          match executeL2 cardDB fo 0 stateA tr with
          | some (stateB, _) => sameModAccum stateA stateB && dealtDamage stateA stateB &&
              noEndTurn tr && drawCondBoolN fo piles 0 stateA tr
          | none => false

private def verifyAll_ps : Bool :=
  (allPerms6.filter isPS).all fun sh0 =>
    let pile1 := mkPile1_ps sh0
    (allPerms3of pile1).all fun sh1 =>
      let refInFirst2 := match sh1 with | [g, h, _] => g.id == 2 || h.id == 2 | _ => false
      if refInFirst2 then
        let p2 := mkPile2_ps sh0 sh1; let p3 := mkPile3_ps_fast sh0
        (allPerms3of p2).all fun sh2 =>
          (allPerms3of p3).all fun sh3 =>
            let fo := fixedOracle [sh0, sh1, sh2, sh3]
            let tr := mkLoopTrace_ps_fast sh0 sh1 sh2 sh3
            match executeL2 cardDB fo 0 stateA tr with
            | some (stateB, _) => sameModAccum stateA stateB && dealtDamage stateA stateB &&
                noEndTurn tr && drawCondBoolN fo [pile0, pile1, p2, p3] 0 stateA tr
            | none => false
      else
        let p2s := mkPile2_ps_slow sh0; let p4s := mkPile4_ps_slow sh0
        (allPerms3of p2s).all fun sh2 =>
          let p3s := mkPile3_ps_slow sh0 sh2
          (allPerms3of p3s).all fun sh3 =>
            (allPerms3of p4s).all fun sh4 =>
              let fo := fixedOracle [sh0, sh1, sh2, sh3, sh4]
              let tr := mkLoopTrace_ps_slow sh0 sh1 sh2 sh3 sh4
              match executeL2 cardDB fo 0 stateA tr with
              | some (stateB, _) => sameModAccum stateA stateB && dealtDamage stateA stateB &&
                  noEndTurn tr && drawCondBoolN fo [pile0, pile1, p2s, p3s, p4s] 0 stateA tr
              | none => false

set_option maxHeartbeats 800000000 in
theorem v_ns : verifyAll_ns = true := by native_decide

set_option maxHeartbeats 800000000 in
theorem v_ps : verifyAll_ps = true := by native_decide

-- ============================================================
-- Perm membership
-- ============================================================

set_option maxHeartbeats 80000000 in
private theorem perm6_mem (l : List CardInstance) (hp : l.Perm pile0) : l ∈ allPerms6 := by
  have hlen := hp.length_eq; simp [pile0] at hlen
  match l, hlen with
  | [a, b, c, d, e, f], _ =>
    have hmem : ∀ x ∈ [a, b, c, d, e, f],
        x = ci0 ∨ x = ci1 ∨ x = ci2 ∨ x = ci3 ∨ x = ci5 ∨ x = ci4 := by
      intro x hx; have hm := hp.subset hx
      simp [pile0, List.mem_cons, List.mem_nil_iff, or_false] at hm; exact hm
    have ha := hmem a (by simp); have hb := hmem b (by simp)
    have hc := hmem c (by simp); have hd := hmem d (by simp)
    have he := hmem e (by simp); have hf := hmem f (by simp)
    have hnd : [a, b, c, d, e, f].Nodup := hp.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or,
               List.not_mem_nil, not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef, _⟩ := hnd
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> (try exact absurd rfl hab) <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> (try exact absurd rfl hac) <;> (try exact absurd rfl hbc) <;>
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> (try exact absurd rfl had) <;> (try exact absurd rfl hbd) <;> (try exact absurd rfl hcd) <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> (try exact absurd rfl hae) <;> (try exact absurd rfl hbe) <;> (try exact absurd rfl hce) <;> (try exact absurd rfl hde) <;>
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> (try exact absurd rfl haf) <;> (try exact absurd rfl hbf) <;> (try exact absurd rfl hcf) <;> (try exact absurd rfl hdf) <;> (try exact absurd rfl hef) <;>
    simp [allPerms6, ci0, ci1, ci2, ci3, ci4, ci5]

private theorem perm3of_mem_nodup (l pile : List CardInstance) (hp : l.Perm pile)
    (hlen : pile.length = 3) (hnd_pile : pile.Nodup) :
    l ∈ allPerms3of pile := by
  match pile, hlen with
  | [pa, pb, pc], _ =>
    have hlen' := hp.length_eq; simp at hlen'
    match l, hlen' with
    | [x, y, z], _ =>
      have hx := hp.mem_iff.mp (List.mem_cons_self x _)
      have hy := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_self y _))
      have hz := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self z _)))
      simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy hz
      have hnd : [x, y, z].Nodup := hp.nodup_iff.mpr hnd_pile
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or,
                 List.not_mem_nil, not_false_eq_true, and_true, and_self] at hnd
      obtain ⟨⟨hxy, hxz⟩, hyz, _⟩ := hnd
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        (try exact absurd rfl hxy) <;> rcases hz with rfl | rfl | rfl <;>
        (try exact absurd rfl hxz) <;> (try exact absurd rfl hyz) <;>
        simp [allPerms3of]

-- Pile property check (length=3, Nodup) for all computed piles
private def checkAllPiles : Bool :=
  allPerms6.all fun sh0 =>
    if isPS sh0 then
      let p1 := mkPile1_ps sh0; let p2s := mkPile2_ps_slow sh0; let p4s := mkPile4_ps_slow sh0
      p1.length == 3 && p1.Nodup && p2s.length == 3 && p2s.Nodup &&
      p4s.length == 3 && p4s.Nodup &&
      (allPerms3of p1).all (fun sh1 =>
        let p2f := mkPile2_ps sh0 sh1; let p3f := mkPile3_ps_fast sh0
        p2f.length == 3 && p2f.Nodup && p3f.length == 3 && p3f.Nodup) &&
      (allPerms3of p2s).all (fun sh2 => let p3s := mkPile3_ps_slow sh0 sh2; p3s.length == 3 && p3s.Nodup)
    else if isNS2 sh0 then
      let p1 := mkPile1_ns2 sh0
      p1.length == 3 && p1.Nodup &&
      (allPerms3of p1).all (fun sh1 => let p2 := mkPile2_ns2 sh0 sh1; p2.length == 3 && p2.Nodup &&
        (allPerms3of p2).all (fun sh2 => let p3 := mkPile3_ns2 sh0 sh1 sh2; p3.length == 3 && p3.Nodup))
    else
      let p1 := mkPile1_ns1 sh0; p1.length == 3 && p1.Nodup &&
      (allPerms3of p1).all (fun sh1 => let p2 := mkPile2_ns1 sh0 sh1; p2.length == 3 && p2.Nodup)

set_option maxHeartbeats 400000000 in
private theorem piles_ok : checkAllPiles = true := by native_decide

-- Helper to extract pile properties
private def getPileProps (sh0 : List CardInstance) (hmem : sh0 ∈ allPerms6)
    (f : List CardInstance → List CardInstance)
    (hcheck : allPerms6.all (fun s => (f s).length == 3 && (f s).Nodup) = true) :
    (f sh0).length = 3 ∧ (f sh0).Nodup := by
  rw [List.all_eq_true] at hcheck
  have h := hcheck sh0 hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h

-- ============================================================
-- Main theorem
-- ============================================================

-- We avoid separate handle_* and instead inline the proof
theorem ComboStormOfSteel3Prep_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  have hsh0_mem := perm6_mem (oracle 0 pile0) (hValid 0 pile0)
  -- Extract all pile length/nodup properties at once
  have hpiles := piles_ok
  cases hps : isPS (oracle 0 pile0)
  · -- Not PS
    cases hns2 : isNS2 (oracle 0 pile0)
    · -- NS1
      -- Extract verified facts
      have hv := v_ns; unfold verifyAll_ns at hv; rw [List.all_eq_true] at hv
      have hv0 := hv (oracle 0 pile0) hsh0_mem
      simp only [hps, hns2, ite_false, List.all_eq_true] at hv0
      -- Pile 1 properties
      unfold checkAllPiles at hpiles; rw [List.all_eq_true] at hpiles
      have hp0 := hpiles (oracle 0 pile0) hsh0_mem
      simp only [hps, hns2, ite_false, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hp0
      obtain ⟨hlen1, hnd1, hrest_p⟩ := hp0
      -- Get sh1 membership
      let sh1 := oracle 1 (mkPile1_ns1 (oracle 0 pile0))
      have hmem1 := perm3of_mem_nodup sh1 _ (hValid 1 _) hlen1 hnd1
      have hv1 := hv0 sh1 hmem1; rw [List.all_eq_true] at hv1
      -- Pile 2 properties
      have hp1 := hrest_p sh1 hmem1
      simp only [Bool.and_eq_true, beq_iff_eq] at hp1
      let sh2 := oracle 2 (mkPile2_ns1 (oracle 0 pile0) sh1)
      have hmem2 := perm3of_mem_nodup sh2 _ (hValid 2 _) hp1.1 hp1.2
      have hv2 := hv1 sh2 hmem2
      -- Extract execution result
      simp only [] at hv2
      split at hv2
      · next stB fIdx heq =>
        simp only [Bool.and_eq_true] at hv2; obtain ⟨⟨⟨hsm, hdd⟩, hne⟩, hdc⟩ := hv2
        -- Bridge: oracle agrees with fixedOracle at used piles
        have hbridge := drawCondBoolN_bridge oracle (fixedOracle [oracle 0 pile0, sh1, sh2])
          [pile0, mkPile1_ns1 (oracle 0 pile0), mkPile2_ns1 (oracle 0 pile0) sh1]
          (by simp only [List.length_cons, List.length_nil]; intro i hi
              match i with
              | 0 => simp [fixedOracle, List.getD]
              | 1 => simp [fixedOracle, List.getD]
              | 2 => simp [fixedOracle, List.getD]
              | 3 => simp [fixedOracle, List.getD]
              | 4 => simp [fixedOracle, List.getD]
              | n + 5 => omega)
          0 stateA _ hdc
        exact ⟨_, stB, fIdx, hbridge ▸ heq, hne, hsm, hdd⟩
      · simp at hv2
    · -- NS2
      have hv := v_ns; unfold verifyAll_ns at hv; rw [List.all_eq_true] at hv
      have hv0 := hv (oracle 0 pile0) hsh0_mem
      simp only [hps, hns2, ite_false, ite_true, List.all_eq_true] at hv0
      unfold checkAllPiles at hpiles; rw [List.all_eq_true] at hpiles
      have hp0 := hpiles (oracle 0 pile0) hsh0_mem
      simp only [hps, hns2, ite_false, ite_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hp0
      obtain ⟨hlen1, hnd1, hrest_p⟩ := hp0
      let sh1 := oracle 1 (mkPile1_ns2 (oracle 0 pile0))
      have hmem1 := perm3of_mem_nodup sh1 _ (hValid 1 _) hlen1 hnd1
      have hv1 := hv0 sh1 hmem1; rw [List.all_eq_true] at hv1
      have hp1 := hrest_p sh1 hmem1
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hp1
      let sh2 := oracle 2 (mkPile2_ns2 (oracle 0 pile0) sh1)
      have hmem2 := perm3of_mem_nodup sh2 _ (hValid 2 _) hp1.1 hp1.2.1
      have hv2 := hv1 sh2 hmem2; rw [List.all_eq_true] at hv2
      have hp2 := hp1.2.2 sh2 hmem2
      simp only [Bool.and_eq_true, beq_iff_eq] at hp2
      let sh3 := oracle 3 (mkPile3_ns2 (oracle 0 pile0) sh1 sh2)
      have hmem3 := perm3of_mem_nodup sh3 _ (hValid 3 _) hp2.1 hp2.2
      have hv3 := hv2 sh3 hmem3
      simp only [] at hv3
      split at hv3
      · next stB fIdx heq =>
        simp only [Bool.and_eq_true] at hv3; obtain ⟨⟨⟨hsm, hdd⟩, hne⟩, hdc⟩ := hv3
        have hbridge := drawCondBoolN_bridge oracle
          (fixedOracle [oracle 0 pile0, sh1, sh2, sh3])
          [pile0, mkPile1_ns2 (oracle 0 pile0), mkPile2_ns2 (oracle 0 pile0) sh1,
           mkPile3_ns2 (oracle 0 pile0) sh1 sh2]
          (by simp only [List.length_cons, List.length_nil]; intro i hi
              match i with
              | 0 => simp [fixedOracle, List.getD]
              | 1 => simp [fixedOracle, List.getD]
              | 2 => simp [fixedOracle, List.getD]
              | 3 => simp [fixedOracle, List.getD]
              | 4 => simp [fixedOracle, List.getD]
              | n + 5 => omega)
          0 stateA _ hdc
        exact ⟨_, stB, fIdx, hbridge ▸ heq, hne, hsm, hdd⟩
      · simp at hv3
  · -- PS
    have hv := v_ps; unfold verifyAll_ps at hv; rw [List.all_eq_true] at hv
    have hps_mem : (oracle 0 pile0) ∈ allPerms6.filter isPS := List.mem_filter.mpr ⟨hsh0_mem, hps⟩
    have hv0 := hv (oracle 0 pile0) hps_mem; simp only [List.all_eq_true] at hv0
    unfold checkAllPiles at hpiles; rw [List.all_eq_true] at hpiles
    have hp0 := hpiles (oracle 0 pile0) hsh0_mem
    simp only [hps, ite_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hp0
    obtain ⟨hlen1, hnd1, hlen2s, hnd2s, hlen4s, hnd4s, hrest_pf, hrest_ps⟩ := hp0
    let sh1 := oracle 1 (mkPile1_ps (oracle 0 pile0))
    have hmem1 := perm3of_mem_nodup sh1 _ (hValid 1 _) hlen1 hnd1
    have hv1 := hv0 sh1 hmem1
    by_cases href : (match sh1 with | [g, h, _] => g.id == 2 || h.id == 2 | _ => false) = true
    · -- PS fast
      simp only [href, ite_true, List.all_eq_true] at hv1
      have hpf := hrest_pf sh1 hmem1
      simp only [Bool.and_eq_true, beq_iff_eq] at hpf
      let sh2 := oracle 2 (mkPile2_ps (oracle 0 pile0) sh1)
      have hmem2 := perm3of_mem_nodup sh2 _ (hValid 2 _) hpf.1 hpf.2.1
      have hv2 := hv1 sh2 hmem2; rw [List.all_eq_true] at hv2
      let sh3 := oracle 3 (mkPile3_ps_fast (oracle 0 pile0))
      have hmem3 := perm3of_mem_nodup sh3 _ (hValid 3 _) hpf.2.2.1 hpf.2.2.2
      have hv3 := hv2 sh3 hmem3
      simp only [] at hv3
      split at hv3
      · next stB fIdx heq =>
        simp only [Bool.and_eq_true] at hv3; obtain ⟨⟨⟨hsm, hdd⟩, hne⟩, hdc⟩ := hv3
        have hbridge := drawCondBoolN_bridge oracle
          (fixedOracle [oracle 0 pile0, sh1, sh2, sh3])
          [pile0, mkPile1_ps (oracle 0 pile0), mkPile2_ps (oracle 0 pile0) sh1,
           mkPile3_ps_fast (oracle 0 pile0)]
          (by simp only [List.length_cons, List.length_nil]; intro i hi
              match i with
              | 0 => simp [fixedOracle, List.getD]
              | 1 => simp [fixedOracle, List.getD]
              | 2 => simp [fixedOracle, List.getD]
              | 3 => simp [fixedOracle, List.getD]
              | 4 => simp [fixedOracle, List.getD]
              | n + 5 => omega)
          0 stateA _ hdc
        exact ⟨_, stB, fIdx, hbridge ▸ heq, hne, hsm, hdd⟩
      · simp at hv3
    · -- PS slow
      have hnslow : (match sh1 with | [g, h, _] => !(g.id == 2 || h.id == 2) | _ => true) = true := by
        cases sh1 with | nil => simp | cons g t => cases t with | nil => simp | cons h t =>
          cases t with | nil => simp | cons i t => cases t <;>
            simp [Bool.not_eq_true] at href ⊢ <;> exact href
      simp only [show (match sh1 with | [g, h, _] => g.id == 2 || h.id == 2 | _ => false) = false from by
        cases sh1 with | nil => simp | cons g t => cases t with | nil => simp | cons h t =>
          cases t with | nil => simp | cons i t => cases t <;>
            simp at href ⊢ <;> exact href, ite_false, List.all_eq_true] at hv1
      let sh2 := oracle 2 (mkPile2_ps_slow (oracle 0 pile0))
      have hmem2 := perm3of_mem_nodup sh2 _ (hValid 2 _) hlen2s hnd2s
      have hv2 := hv1 sh2 hmem2; rw [List.all_eq_true] at hv2
      have hps2 := hrest_ps sh2 hmem2
      simp only [Bool.and_eq_true, beq_iff_eq] at hps2
      let sh3 := oracle 3 (mkPile3_ps_slow (oracle 0 pile0) sh2)
      have hmem3 := perm3of_mem_nodup sh3 _ (hValid 3 _) hps2.1 hps2.2
      have hv3 := hv2 sh3 hmem3; rw [List.all_eq_true] at hv3
      let sh4 := oracle 4 (mkPile4_ps_slow (oracle 0 pile0))
      have hmem4 := perm3of_mem_nodup sh4 _ (hValid 4 _) hlen4s hnd4s
      have hv4 := hv3 sh4 hmem4
      simp only [] at hv4
      split at hv4
      · next stB fIdx heq =>
        simp only [Bool.and_eq_true] at hv4; obtain ⟨⟨⟨hsm, hdd⟩, hne⟩, hdc⟩ := hv4
        have hbridge := drawCondBoolN_bridge oracle
          (fixedOracle [oracle 0 pile0, sh1, sh2, sh3, sh4])
          [pile0, mkPile1_ps (oracle 0 pile0), mkPile2_ps_slow (oracle 0 pile0),
           mkPile3_ps_slow (oracle 0 pile0) sh2, mkPile4_ps_slow (oracle 0 pile0)]
          (by simp only [List.length_cons, List.length_nil]; intro i hi
              match i with
              | 0 => simp [fixedOracle, List.getD]
              | 1 => simp [fixedOracle, List.getD]
              | 2 => simp [fixedOracle, List.getD]
              | 3 => simp [fixedOracle, List.getD]
              | 4 => simp [fixedOracle, List.getD]
              | n + 5 => omega)
          0 stateA _ hdc
        exact ⟨_, stB, fIdx, hbridge ▸ heq, hne, hsm, hdd⟩
      · simp at hv4

end ComboStormOfSteel3Prep_L2
