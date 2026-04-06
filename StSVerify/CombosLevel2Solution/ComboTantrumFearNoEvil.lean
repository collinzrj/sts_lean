/-
  Watcher - Tantrum+ + 2xFearNoEvil+ + 2xFlurryOfBlows+ (Level 2)

  Single shuffle point: 3-card discard pile [flr7, flr6, fne5].
  6 permutations verified individually via native_decide.
  drawCondBool bridge lifts fixed-oracle results to arbitrary oracles.
-/

import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB

open CardName Action

namespace ComboTantrumFearNoEvil_L2

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
  .endTurn,
  .draw 3, .draw 4, .draw 5, .draw 6, .draw 7,
  .play 4, .play 3,
  .draw 3, .draw 4, .failDraw,
  .play 5, .play 6, .play 7
]

def stateA : GameState := {
  hand := [fne4, tant3], drawPile := []
  discardPile := [flr7, flr6, fne5]
  exhaustPile := exhaustConst, inUse := [], actionQueue := []
  energy := 2, damage := 57, block := 18, stance := .Calm
  orbs := [], orbSlots := 3, focus := 0, enemy := enemyConst
  activePowers := powersConst, nextId := 13, noDraw := false, corruptionActive := false
}

private def stateB : GameState := {
  hand := [tant3, fne4], drawPile := []
  discardPile := [flr7, flr6, fne5]
  exhaustPile := exhaustConst, inUse := [], actionQueue := []
  energy := 2, damage := 127, block := 30, stance := .Calm
  orbs := [], orbSlots := 3, focus := 0, enemy := enemyConst
  activePowers := powersConst, nextId := 13, noDraw := false, corruptionActive := false
}

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

private theorem same_mod : sameModAccum stateA stateB = true := by native_decide
private theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

private def pile1 : List CardInstance := [flr7, flr6, fne5]

private def mkLoopTrace (sh : List CardInstance) : List Action :=
  [.play 3, .draw 3] ++
  (sh.map fun c => Action.draw c.id) ++
  [.play 5, .play 6, .play 7]

private def fixedOracle (sh : List CardInstance) : ShuffleOracle := fun idx _ =>
  if idx == 0 then sh else []

private def drawCondBool (fo : ShuffleOracle)
    (si : Nat) (s : GameState) : List Action → Bool
  | [] => true
  | a :: rest =>
    let sc := autoDrain cardDB s
    let dpOk := match a with
      | .draw _ => sc.drawPile.length > 0 ||
                   (decide (si = 0) && decide (sc.discardPile = pile1))
      | _ => true
    match stepL2 cardDB fo si sc a with
    | some (s', si') => dpOk && drawCondBool fo si' s' rest
    | none => false

private def allPerms3 : List (List CardInstance) :=
  [ [flr7, flr6, fne5], [flr7, fne5, flr6],
    [flr6, flr7, fne5], [flr6, fne5, flr7],
    [fne5, flr7, flr6], [fne5, flr6, flr7] ]

-- ============================================================
-- drawCondBool bridge
-- ============================================================

private theorem drawCondBool_bridge (oracle fo : ShuffleOracle)
    (h0 : oracle 0 pile1 = fo 0 pile1)
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
            obtain ⟨hsi, hdisc⟩ := hdpOk
            rw [hsi, hdisc]; exact h0
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
-- Perm membership
-- ============================================================

set_option maxHeartbeats 800000 in
private theorem perm3_mem (l : List CardInstance) (hp : l.Perm pile1) : l ∈ allPerms3 := by
  have hlen := hp.length_eq; simp [pile1] at hlen
  match l, hlen with
  | [x, y, z], _ =>
    have hx := hp.mem_iff.mp (List.mem_cons_self x _)
    have hy := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_self y _))
    have hz := hp.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self z _)))
    simp only [pile1, flr7, flr6, fne5, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy hz
    have hnd : [x, y, z].Nodup := hp.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or,
               List.not_mem_nil, not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hxy, hxz⟩, hyz, _⟩ := hnd
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      (try exact absurd rfl hxy) <;> rcases hz with rfl | rfl | rfl <;>
      (try exact absurd rfl hxz) <;> (try exact absurd rfl hyz) <;>
      simp [allPerms3, flr7, flr6, fne5]

-- ============================================================
-- Per-permutation verification (individual native_decide)
-- ============================================================

private theorem exec1 : executeL2 cardDB (fixedOracle [flr7, flr6, fne5]) 0 stateA (mkLoopTrace [flr7, flr6, fne5]) = some (stateB, 1) := by native_decide
private theorem exec2 : executeL2 cardDB (fixedOracle [flr7, fne5, flr6]) 0 stateA (mkLoopTrace [flr7, fne5, flr6]) = some (stateB, 1) := by native_decide
private theorem exec3 : executeL2 cardDB (fixedOracle [flr6, flr7, fne5]) 0 stateA (mkLoopTrace [flr6, flr7, fne5]) = some (stateB, 1) := by native_decide
private theorem exec4 : executeL2 cardDB (fixedOracle [flr6, fne5, flr7]) 0 stateA (mkLoopTrace [flr6, fne5, flr7]) = some (stateB, 1) := by native_decide
private theorem exec5 : executeL2 cardDB (fixedOracle [fne5, flr7, flr6]) 0 stateA (mkLoopTrace [fne5, flr7, flr6]) = some (stateB, 1) := by native_decide
private theorem exec6 : executeL2 cardDB (fixedOracle [fne5, flr6, flr7]) 0 stateA (mkLoopTrace [fne5, flr6, flr7]) = some (stateB, 1) := by native_decide

private theorem dc1 : drawCondBool (fixedOracle [flr7, flr6, fne5]) 0 stateA (mkLoopTrace [flr7, flr6, fne5]) = true := by native_decide
private theorem dc2 : drawCondBool (fixedOracle [flr7, fne5, flr6]) 0 stateA (mkLoopTrace [flr7, fne5, flr6]) = true := by native_decide
private theorem dc3 : drawCondBool (fixedOracle [flr6, flr7, fne5]) 0 stateA (mkLoopTrace [flr6, flr7, fne5]) = true := by native_decide
private theorem dc4 : drawCondBool (fixedOracle [flr6, fne5, flr7]) 0 stateA (mkLoopTrace [flr6, fne5, flr7]) = true := by native_decide
private theorem dc5 : drawCondBool (fixedOracle [fne5, flr7, flr6]) 0 stateA (mkLoopTrace [fne5, flr7, flr6]) = true := by native_decide
private theorem dc6 : drawCondBool (fixedOracle [fne5, flr6, flr7]) 0 stateA (mkLoopTrace [fne5, flr6, flr7]) = true := by native_decide

private theorem ne1 : noEndTurn (mkLoopTrace [flr7, flr6, fne5]) = true := by native_decide

private theorem ne_eq (sh : List CardInstance) (hlen : sh.length = 3) :
    noEndTurn (mkLoopTrace sh) = true := by
  match sh, hlen with
  | [_, _, _], _ => exact ne1

-- ============================================================
-- Per-case proof assembly
-- ============================================================

private theorem fo_pile_eq (sh : List CardInstance) :
    (fixedOracle sh) 0 pile1 = sh := by rfl

private theorem mk_case (sh : List CardInstance)
    (hexec : executeL2 cardDB (fixedOracle sh) 0 stateA (mkLoopTrace sh) = some (stateB, 1))
    (hdc : drawCondBool (fixedOracle sh) 0 stateA (mkLoopTrace sh) = true)
    (hlen : sh.length = 3)
    (oracle : ShuffleOracle) (h0 : oracle 0 pile1 = sh) :
    ∃ t sB fi, executeL2 cardDB oracle 0 stateA t = some (sB, fi)
      ∧ noEndTurn t = true ∧ sameModAccum stateA sB = true ∧ dealtDamage stateA sB = true := by
  refine ⟨_, stateB, 1, ?_, ne_eq sh hlen, same_mod, dealt_dmg⟩
  have hf0 : oracle 0 pile1 = (fixedOracle sh) 0 pile1 := by
    rw [fo_pile_eq]; exact h0
  rw [drawCondBool_bridge oracle _ hf0 0 stateA _ hdc]
  exact hexec

-- ============================================================
-- Main theorem
-- ============================================================

theorem ComboTantrumFearNoEvil_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  have hsh_mem := perm3_mem (oracle 0 pile1) (hValid 0 pile1)
  simp only [allPerms3, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hsh_mem
  rcases hsh_mem with h | h | h | h | h | h
  · exact mk_case _ exec1 dc1 rfl oracle h
  · exact mk_case _ exec2 dc2 rfl oracle h
  · exact mk_case _ exec3 dc3 rfl oracle h
  · exact mk_case _ exec4 dc4 rfl oracle h
  · exact mk_case _ exec5 dc5 rfl oracle h
  · exact mk_case _ exec6 dc6 rfl oracle h

end ComboTantrumFearNoEvil_L2
