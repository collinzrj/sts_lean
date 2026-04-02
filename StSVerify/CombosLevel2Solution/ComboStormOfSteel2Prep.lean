/-
  Storm of Steel+ + Tactician+ + Reflex+ + 2×Prepared+ (5 cards) - Level 2 Strict
  Guaranteed infinite combo for ANY shuffle oracle.
-/
import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB
open CardName Action

namespace ComboStormOfSteel2Prep_L2

private def sos : CardInstance := { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }
private def tact : CardInstance := { id := 1, name := TacticianPlus, cost := 0, damage := 0 }
private def reflex : CardInstance := { id := 2, name := ReflexPlus, cost := 0, damage := 0 }
private def prep3 : CardInstance := { id := 3, name := PreparedPlus, cost := 0, damage := 0 }
private def prep4 : CardInstance := { id := 4, name := PreparedPlus, cost := 0, damage := 0 }

def cards : List (CardName × Nat) := [
  (StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1), (PreparedPlus, 2)]
def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0, .draw 1, .draw 3, .draw 4,
  .play 5, .play 6, .play 7, .play 8,
  .play 3, .draw 2, .draw 0, .discard 0,
  .endTurn, .draw 0, .draw 1, .draw 2, .draw 3, .draw 4]

def stateA : GameState := {
  hand := [prep4, prep3, reflex, tact, sos], drawPile := [], discardPile := [],
  exhaustPile := [{id:=8, name:=Shiv, cost:=0, damage:=4},
                  {id:=7, name:=Shiv, cost:=0, damage:=4},
                  {id:=6, name:=Shiv, cost:=0, damage:=4},
                  {id:=5, name:=Shiv, cost:=0, damage:=4}],
  inUse := [], actionQueue := [],
  energy := 3, damage := 16, block := 0,
  stance := .Neutral, orbs := [], orbSlots := 3, focus := 0,
  enemy := enemy, activePowers := [], nextId := 9,
  noDraw := false, corruptionActive := false }

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

private def isPrep (c : CardInstance) : Bool := c.name == PreparedPlus
private def pickPrep (d1 d2 d3 : CardInstance) : CardInstance :=
  if isPrep d1 then d1 else if isPrep d2 then d2 else d3

private def mkTrace (p1 p2 : List CardInstance) : List Action :=
  match p1 with
  | d1 :: d2 :: d3 :: [d4] =>
    let prep := pickPrep d1 d2 d3
    [.play 0, .draw d1.id, .draw d2.id, .draw d3.id,
     .play 9, .play 10, .play 11, .play 12,
     .play prep.id, .draw d4.id, .draw 0, .discard 0,
     .endTurn] ++ (p2.map fun c => .draw c.id)
  | _ => []

private def insertEverywhere (x : CardInstance) : List CardInstance → List (List CardInstance)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertEverywhere x ys).map (y :: ·)

private def permsOf : List CardInstance → List (List CardInstance)
  | [] => [[]]
  | x :: xs => (permsOf xs).flatMap (insertEverywhere x ·)

private theorem insertEverywhere_contains (x : CardInstance) (l₁ l₂ : List CardInstance) :
    (l₁ ++ x :: l₂) ∈ insertEverywhere x (l₁ ++ l₂) := by
  induction l₁ with
  | nil => cases l₂ <;> simp [insertEverywhere]
  | cons y rest ih =>
    simp only [List.cons_append, insertEverywhere]
    right; exact List.mem_map_of_mem (y :: ·) ih

private theorem permsOf_complete (l pile : List CardInstance) (hp : l.Perm pile) :
    l ∈ permsOf pile := by
  induction pile generalizing l with
  | nil => have := hp.eq_nil; subst this; simp [permsOf]
  | cons x xs ih =>
    have hx : x ∈ l := hp.mem_iff.mpr (List.mem_cons_self x xs)
    obtain ⟨s, t, hst⟩ := List.append_of_mem hx
    have hperm_rest : (s ++ t).Perm xs :=
      (List.perm_middle.symm.trans (hst ▸ hp)).cons_inv
    simp [permsOf, List.mem_flatMap]
    exact ⟨s ++ t, ih _ hperm_rest, by rw [hst]; exact insertEverywhere_contains x s t⟩

private def fixOracle (p1 p2 : List CardInstance) : ShuffleOracle :=
  fun idx _pile => if idx == 0 then p1 else if idx == 2 then p2 else _pile

private def verifyOne (p1 p2 : List CardInstance) : Bool :=
  match executeL2 cardDB (fixOracle p1 p2) 0 stateA (mkTrace p1 p2) with
  | some (stB, _) => sameModAccum stateA stB && dealtDamage stateA stB
  | none => false

private def pile0 : List CardInstance := [prep4, prep3, reflex, tact]
private def fiveCards : List CardInstance := [sos, tact, reflex, prep3, prep4]

private def verifyAll : Bool :=
  (permsOf pile0).all fun p1 => (permsOf fiveCards).all fun p2 => verifyOne p1 p2

private theorem verifyAll_ok : verifyAll = true := by native_decide

private theorem verify_from_perms {p1 p2 : List CardInstance}
    (hp1 : p1 ∈ permsOf pile0) (hp2 : p2 ∈ permsOf fiveCards) :
    verifyOne p1 p2 = true := by
  have hva := verifyAll_ok; unfold verifyAll at hva
  exact List.all_eq_true.mp (List.all_eq_true.mp hva p1 hp1) p2 hp2

set_option maxHeartbeats 800000 in
private theorem perm_4_cases {l : List CardInstance} (hp : l.Perm pile0) :
    l = [prep4, prep3, reflex, tact] ∨ l = [prep4, prep3, tact, reflex] ∨
    l = [prep4, reflex, prep3, tact] ∨ l = [prep4, reflex, tact, prep3] ∨
    l = [prep4, tact, prep3, reflex] ∨ l = [prep4, tact, reflex, prep3] ∨
    l = [prep3, prep4, reflex, tact] ∨ l = [prep3, prep4, tact, reflex] ∨
    l = [prep3, reflex, prep4, tact] ∨ l = [prep3, reflex, tact, prep4] ∨
    l = [prep3, tact, prep4, reflex] ∨ l = [prep3, tact, reflex, prep4] ∨
    l = [reflex, prep4, prep3, tact] ∨ l = [reflex, prep4, tact, prep3] ∨
    l = [reflex, prep3, prep4, tact] ∨ l = [reflex, prep3, tact, prep4] ∨
    l = [reflex, tact, prep4, prep3] ∨ l = [reflex, tact, prep3, prep4] ∨
    l = [tact, prep4, prep3, reflex] ∨ l = [tact, prep4, reflex, prep3] ∨
    l = [tact, prep3, prep4, reflex] ∨ l = [tact, prep3, reflex, prep4] ∨
    l = [tact, reflex, prep4, prep3] ∨ l = [tact, reflex, prep3, prep4] := by
  have hlen := hp.length_eq; simp [pile0] at hlen
  have hmem : ∀ x ∈ l, x = prep4 ∨ x = prep3 ∨ x = reflex ∨ x = tact := by
    intro x hx; have hm := hp.subset hx
    simp [pile0, List.mem_cons, List.mem_nil_iff, or_false] at hm; exact hm
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
    simp [prep4, prep3, reflex, tact]

private def getPile2 (p1 : List CardInstance) : List CardInstance :=
  let orc : ShuffleOracle := fun idx _pile => if idx == 0 then p1 else _pile
  match p1 with
  | d1 :: d2 :: d3 :: [d4] =>
    let prep := pickPrep d1 d2 d3
    let tr := [.play 0, .draw d1.id, .draw d2.id, .draw d3.id,
               .play 9, .play 10, .play 11, .play 12,
               .play prep.id, .draw d4.id, .draw 0, .discard 0, .endTurn]
    match executeL2 cardDB orc 0 stateA tr with
    | some (s, _) => s.discardPile
    | none => []
  | _ => []

-- ============================================================
-- DRAW-ONLY ORACLE BRIDGE (drawCondBool approach)
-- ============================================================

/-- At each draw step along the fixed oracle execution where drawPile is empty,
    check that we're at a known shuffle point. Non-draw steps are always OK.
    Shuffle points: si=0 with disc=p0, si=1 with disc=p1, si=2 with disc=p2. -/
private def drawCondBool (fo : ShuffleOracle) (p0 p1 p2 : List CardInstance)
    (si : Nat) (s : GameState) : List Action → Bool
  | [] => true
  | a :: rest =>
    let sc := resolveInUse cardDB (autoDrain cardDB s)
    let dpOk := match a with
      | .draw _ => sc.drawPile.length > 0 ||
                   (decide (si = 0) && decide (sc.discardPile = p0)) ||
                   (decide (si = 1) && decide (sc.discardPile = p1)) ||
                   (decide (si = 2) && decide (sc.discardPile = p2))
      | _ => true
    match stepL2 cardDB fo si sc a with
    | some (s', si') => dpOk && drawCondBool fo p0 p1 p2 si' s' rest
    | none => false

/-- Oracle bridge: if drawCondBool passes and oracle agrees at the 3 shuffle points,
    then executeL2 gives the same result for both oracles. -/
private theorem drawCondBool_bridge (oracle fo : ShuffleOracle)
    (p0 p1 p2 : List CardInstance)
    (h0 : oracle 0 p0 = fo 0 p0)
    (h1 : oracle 1 p1 = fo 1 p1)
    (h2 : oracle 2 p2 = fo 2 p2)
    (si : Nat) (s : GameState) (trace : List Action)
    (hb : drawCondBool fo p0 p1 p2 si s trace = true) :
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
            rcases hdpOk with (⟨hsi, hdisc⟩ | ⟨hsi, hdisc⟩) | ⟨hsi, hdisc⟩
            · rw [hsi, hdisc]; exact h0
            · rw [hsi, hdisc]; exact h1
            · rw [hsi, hdisc]; exact h2
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
-- CONCRETE VERIFICATION (native_decide on fully concrete inputs)
-- ============================================================

-- Oracle 1 on singleton = identity
private theorem oracle_single (oracle : ShuffleOracle) (hv : validOracle oracle) (n : Nat)
    (a : CardInstance) : oracle n [a] = [a] :=
  List.perm_singleton.mp (hv n [a])

private def verifyOneNew (p1 p2 : List CardInstance) : Bool :=
  match executeL2 cardDB (fixOracle p1 p2) 0 stateA (mkTrace p1 p2) with
  | some (stB, _) =>
    sameModAccum stateA stB && dealtDamage stateA stB &&
    drawCondBool (fixOracle p1 p2) pile0 [sos] (getPile2 p1) 0 stateA (mkTrace p1 p2)
  | none => false

private def verifyAllNew : Bool :=
  (permsOf pile0).all fun p1 => (permsOf fiveCards).all fun p2 => verifyOneNew p1 p2

private theorem verifyAllNew_ok : verifyAllNew = true := by native_decide

private theorem verifyNew_from_perms {p1 p2 : List CardInstance}
    (hp1 : p1 ∈ permsOf pile0) (hp2 : p2 ∈ permsOf fiveCards) :
    verifyOneNew p1 p2 = true := by
  have hva := verifyAllNew_ok; unfold verifyAllNew at hva
  exact List.all_eq_true.mp (List.all_eq_true.mp hva p1 hp1) p2 hp2

-- ============================================================
-- CASE HANDLER
-- ============================================================

private theorem case_handler (p1 p2 : List CardInstance)
    (hmem1 : p1 ∈ permsOf pile0) (hmem2 : p2 ∈ permsOf fiveCards)
    (oracle : ShuffleOracle)
    (h0 : oracle 0 pile0 = p1)
    (h1 : oracle 1 [sos] = fo_sos)
    (h2 : oracle 2 (getPile2 p1) = p2)
    (hfo_sos : fo_sos = fixOracle p1 p2 1 [sos]) :
    ∃ (stB : GameState) (fIdx : Nat) (trace : List Action),
      executeL2 cardDB oracle 0 stateA trace = some (stB, fIdx)
      ∧ sameModAccum stateA stB = true
      ∧ dealtDamage stateA stB = true := by
  have hv := verifyNew_from_perms hmem1 hmem2
  unfold verifyOneNew at hv
  have hf0 : oracle 0 pile0 = fixOracle p1 p2 0 pile0 := by
    simp only [fixOracle]; exact h0
  have hf1 : oracle 1 [sos] = fixOracle p1 p2 1 [sos] := by
    rw [h1, hfo_sos]
  have hf2 : oracle 2 (getPile2 p1) = fixOracle p1 p2 2 (getPile2 p1) := by
    simp only [fixOracle]; exact h2
  generalize hres :
    executeL2 cardDB (fixOracle p1 p2) 0 stateA (mkTrace p1 p2) = result at hv
  match result, hv with
  | some (stB, fIdx), hv =>
    simp only [Bool.and_eq_true] at hv
    obtain ⟨⟨hsm, hdd⟩, hdc⟩ := hv
    have hbridge := drawCondBool_bridge oracle (fixOracle p1 p2) pile0 [sos] (getPile2 p1)
      hf0 hf1 hf2 0 stateA (mkTrace p1 p2) hdc
    exact ⟨stB, fIdx, mkTrace p1 p2, hbridge ▸ hres, hsm, hdd⟩
  | none, hv => simp at hv

-- ============================================================
-- MAIN THEOREM
-- ============================================================

set_option maxHeartbeats 8000000 in
private theorem loop_l2 (oracle : ShuffleOracle) (hv : validOracle oracle) :
    ∃ (stB : GameState) (fIdx : Nat) (trace : List Action),
      executeL2 cardDB oracle 0 stateA trace = some (stB, fIdx)
      ∧ sameModAccum stateA stB = true
      ∧ dealtDamage stateA stB = true := by
  have hperm1 : (oracle 0 pile0).Perm pile0 := hv 0 pile0
  have h_cases := perm_4_cases hperm1
  rcases h_cases with h | h | h | h | h | h | h | h |
                       h | h | h | h | h | h | h | h |
                       h | h | h | h | h | h | h | h <;>
  ( have hpile2_perm : (getPile2 (oracle 0 pile0)).Perm fiveCards := by rw [h]; native_decide
    have hp2_perm : (oracle 2 (getPile2 (oracle 0 pile0))).Perm fiveCards :=
      (hv 2 _).trans hpile2_perm
    have hp1_mem := permsOf_complete _ pile0 hperm1
    have hp2_mem := permsOf_complete _ fiveCards hp2_perm
    have h_single := oracle_single oracle hv 1 sos
    exact case_handler (oracle 0 pile0) (oracle 2 (getPile2 (oracle 0 pile0)))
      hp1_mem hp2_mem oracle rfl h_single rfl
      (by simp [fixOracle, h_single]) )

theorem ComboStormOfSteel2Prep_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hvalid
  obtain ⟨stB, fIdx, trace, hexec, hsma, hdmg⟩ := loop_l2 oracle hvalid
  exact ⟨trace, stB, fIdx, hexec, hsma, hdmg⟩

end ComboStormOfSteel2Prep_L2
