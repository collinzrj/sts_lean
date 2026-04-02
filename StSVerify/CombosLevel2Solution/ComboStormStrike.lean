/-
  Storm of Steel+ + Tactician+ + Reflex+ + Prepared+ + Strike Silent (5 cards) - Level 2
  16 damage per loop (4 Shivs × 4 damage)

  v2 engine: CardInstance piles, sameModAccum, executeL2 with ShuffleOracle.

  Proof strategy:
  1. Computational verification: all 576 permutation pairs verified via native_decide
  2. Oracle bridge: bridgeCheck (boolean) + soundness lemma
  3. Main theorem: combine bridge + verification
-/

import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB

open CardName Action

namespace ComboStormStrike_L2_Strict

-- ============================================================
-- CARD INSTANCES
-- ============================================================

private def storm : CardInstance := { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }
private def tact  : CardInstance := { id := 1, name := TacticianPlus, cost := 0, damage := 0 }
private def refx  : CardInstance := { id := 2, name := ReflexPlus, cost := 0, damage := 0 }
private def prep  : CardInstance := { id := 3, name := PreparedPlus, cost := 0, damage := 0 }
private def strk  : CardInstance := { id := 4, name := StrikeSilent, cost := 1, damage := 6 }

def cards : List (CardName × Nat) := [
  (StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1),
  (PreparedPlus, 1), (StrikeSilent, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }
def pile1 : List CardInstance := [strk, prep, refx, tact]

-- ============================================================
-- SETUP
-- ============================================================

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0,
  .draw 3, .draw 4, .draw 1,
  .play 5, .play 6, .play 7, .play 8,
  .play 4, .play 3,
  .draw 2, .draw 0, .discard 2,
  .draw 4, .draw 2, .failDraw,
  .endTurn,
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4
]

def stateA : GameState := {
  hand := [strk, prep, refx, tact, storm]
  drawPile := []
  discardPile := []
  exhaustPile := [{ id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 },
                  { id := 5, name := Shiv, cost := 0, damage := 4 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 22
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

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- ============================================================
-- LOOP TRACE
-- ============================================================

def mkLoopTrace (sh1 sh2 : List CardInstance) : List Action :=
  [.play 0] ++
  (sh1.take 3).map (fun c => Action.draw c.id) ++
  [.play 9, .play 10, .play 11, .play 12, .endTurn] ++
  (match sh1.get? 3 with | some c => [Action.draw c.id] | none => []) ++
  (sh2.take 4).map (fun c => Action.draw c.id)

def mkPile2 (sh1 : List CardInstance) : List CardInstance :=
  (sh1.take 3).reverse ++ [storm]

def fixedOracle (sh1 sh2 : List CardInstance) : ShuffleOracle := fun idx _ =>
  if idx == 0 then sh1 else sh2

-- ============================================================
-- COMPUTATIONAL VERIFICATION
-- ============================================================

private def insertEverywhere' (x : CardInstance) : List CardInstance → List (List CardInstance)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertEverywhere' x ys).map (y :: ·)

private def permsOf' : List CardInstance → List (List CardInstance)
  | [] => [[]]
  | x :: xs => (permsOf' xs).flatMap (insertEverywhere' x ·)

private def verifyPair (s1 s2 : List CardInstance) : Bool :=
  match executeL2 cardDB (fixedOracle s1 s2) 0 stateA (mkLoopTrace s1 s2) with
  | some (stateB, _) => sameModAccum stateA stateB && dealtDamage stateA stateB
  | none => false

private def checkAll : Bool :=
  (permsOf' pile1).all fun p1 =>
    (permsOf' (mkPile2 p1)).all fun p2 => verifyPair p1 p2

theorem all_perms_check : checkAll = true := by native_decide

-- ============================================================
-- permsOf' completeness
-- ============================================================

private theorem insertEverywhere'_head (x : CardInstance) (l : List CardInstance) :
    (x :: l) ∈ insertEverywhere' x l := by
  cases l with | nil => simp [insertEverywhere'] | cons _ _ => simp [insertEverywhere']

private theorem insertEverywhere'_contains (x : CardInstance) (l₁ l₂ : List CardInstance) :
    (l₁ ++ x :: l₂) ∈ insertEverywhere' x (l₁ ++ l₂) := by
  induction l₁ with
  | nil => simp [List.nil_append]; exact insertEverywhere'_head x l₂
  | cons y rest ih =>
    simp only [List.cons_append, insertEverywhere']
    right; exact List.mem_map_of_mem (y :: ·) ih

private theorem perm_split (x : CardInstance) (xs s t : List CardInstance)
    (h : (s ++ x :: t).Perm (x :: xs)) : (s ++ t).Perm xs :=
  (List.perm_middle.symm.trans h).cons_inv

private theorem permsOf'_complete (l pile : List CardInstance) (hp : l.Perm pile) :
    l ∈ permsOf' pile := by
  induction pile generalizing l with
  | nil => have := hp.eq_nil; subst this; simp [permsOf']
  | cons x xs ih =>
    have hx : x ∈ l := hp.mem_iff.mpr (List.mem_cons_self x xs)
    obtain ⟨s, t, hst⟩ := List.append_of_mem hx
    simp [permsOf', List.mem_flatMap]
    exact ⟨s ++ t, ih _ (perm_split x xs s t (hst ▸ hp)),
           by rw [hst]; exact insertEverywhere'_contains x s t⟩

private theorem verify_from_perm (sh1 sh2 : List CardInstance)
    (hp1 : sh1.Perm pile1) (hp2 : sh2.Perm (mkPile2 sh1)) :
    verifyPair sh1 sh2 = true := by
  have h1 := permsOf'_complete sh1 pile1 hp1
  have h2 := permsOf'_complete sh2 (mkPile2 sh1) hp2
  have := all_perms_check; unfold checkAll at this
  exact ((List.all_eq_true.mp this sh1 h1 |> List.all_eq_true.mp) sh2 h2)

-- ============================================================
-- ORACLE BRIDGE
-- ============================================================

-- Boolean bridge check: at each draw step, verify drawPile non-empty or oracle agreement
private def bridgeGo (sh1 : List CardInstance) (fo : ShuffleOracle)
    (si : Nat) (s : GameState) : List Action → Bool
  | [] => true
  | a :: rest =>
    let s_c := resolveInUse cardDB (autoDrain cardDB s)
    let cond := match a with
      | .draw _ => decide (s_c.drawPile ≠ []) ||
        (decide (si = 0) && decide (s_c.discardPile = pile1)) ||
        (decide (si = 1) && decide (s_c.discardPile = mkPile2 sh1))
      | _ => true
    if cond then
      match stepL2 cardDB fo si s_c a with
      | some (s', si') => bridgeGo sh1 fo si' s' rest
      | none => false
    else false

-- Verify for all permutation pairs
private def checkAllBridge : Bool :=
  (permsOf' pile1).all fun p1 =>
    (permsOf' (mkPile2 p1)).all fun p2 =>
      bridgeGo p1 (fixedOracle p1 p2) 0 stateA (mkLoopTrace p1 p2)

theorem all_bridge_ok : checkAllBridge = true := by native_decide

private theorem bridge_check_ok (sh1 sh2 : List CardInstance)
    (hp1 : sh1.Perm pile1) (hp2 : sh2.Perm (mkPile2 sh1)) :
    bridgeGo sh1 (fixedOracle sh1 sh2) 0 stateA (mkLoopTrace sh1 sh2) = true := by
  have h1 := permsOf'_complete sh1 pile1 hp1
  have h2 := permsOf'_complete sh2 (mkPile2 sh1) hp2
  have := all_bridge_ok; unfold checkAllBridge at this
  exact ((List.all_eq_true.mp this sh1 h1 |> List.all_eq_true.mp) sh2 h2)

-- Soundness: bridgeGo = true → executeL2 oracle = executeL2 fo
private theorem bridge_sound (oracle fo : ShuffleOracle) (sh1 : List CardInstance)
    (h_agree_0 : oracle 0 pile1 = fo 0 pile1)
    (h_agree_1 : oracle 1 (mkPile2 sh1) = fo 1 (mkPile2 sh1)) :
    ∀ (trace : List Action) (si : Nat) (s : GameState),
    bridgeGo sh1 fo si s trace = true →
    executeL2 cardDB oracle si s trace = executeL2 cardDB fo si s trace := by
  intro trace; induction trace with
  | nil => intros; rfl
  | cons a rest ih =>
    intro si s hbc
    -- Step agreement
    have h_step : stepL2 cardDB oracle si (resolveInUse cardDB (autoDrain cardDB s)) a =
                  stepL2 cardDB fo si (resolveInUse cardDB (autoDrain cardDB s)) a := by
      cases a with
      | draw c =>
        apply stepL2_oracle_cond
        -- Need: drawPile ≠ [] ∨ oracle si disc = fo si disc
        -- Extract from bridgeGo: the cond was true
        simp only [bridgeGo] at hbc
        -- hbc has if-then-else structure. Extract the condition.
        -- The condition for draw: decide(drawPile≠[]) || (si==0 && decide(disc=pile1)) || ...
        -- If condition false → if false then ... else false = true → false = true → contradiction
        -- So condition must be true.
        -- Get the condition value
        generalize hcv : (decide ((resolveInUse cardDB (autoDrain cardDB s)).drawPile ≠ []) ||
          decide (si = 0) && decide ((resolveInUse cardDB (autoDrain cardDB s)).discardPile = pile1) ||
          decide (si = 1) && decide ((resolveInUse cardDB (autoDrain cardDB s)).discardPile = mkPile2 sh1)) = cv at hbc
        cases cv with
        | false => simp at hbc
        | true =>
          simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hcv
          -- hcv : (drawPile ≠ [] ∨ si=0 ∧ disc=pile1) ∨ si=1 ∧ disc=mkPile2
          rcases hcv with (hne | ⟨rfl, hdisc⟩) | ⟨rfl, hdisc⟩
          · exact Or.inl hne
          · exact Or.inr (by rw [hdisc]; exact h_agree_0)
          · exact Or.inr (by rw [hdisc]; exact h_agree_1)
      | _ => simp [stepL2]
    -- Rewrite executeL2
    show executeL2 cardDB oracle si s (a :: rest) = executeL2 cardDB fo si s (a :: rest)
    simp only [executeL2, h_step]
    cases hfo : stepL2 cardDB fo si (resolveInUse cardDB (autoDrain cardDB s)) a with
    | none => rfl
    | some p =>
      apply ih
      -- Extract continuation from hbc
      -- bridgeGo checks condition, then matches step result
      -- For draw: condition + match step → bridgeGo rest
      -- For non-draw: true (condition) + match step → bridgeGo rest
      -- In either case: we need hbc simplified with condition=true and step=some p
      simp only [bridgeGo] at hbc
      -- hbc has structure: (if condVal = true then match stepResult with ... else false) = true
      -- Split on action type in hbc to determine condVal
      -- Then use hfo to simplify the match
      split at hbc
      · -- draw case: condVal was some condition
        generalize hcv2 : (_ || _ || _) = cv2 at hbc
        cases cv2 with
        | false => simp at hbc
        | true => simp only [ite_true, hfo] at hbc; exact hbc
      · -- non-draw case: condVal = true
        simp only [ite_true, hfo] at hbc; exact hbc

-- The oracle bridge theorem
private theorem oracle_bridge (oracle : ShuffleOracle)
    (sh1 sh2 : List CardInstance)
    (hsh1 : oracle 0 pile1 = sh1) (hsh2 : oracle 1 (mkPile2 sh1) = sh2)
    (hp1 : sh1.Perm pile1) (hp2 : sh2.Perm (mkPile2 sh1)) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace sh1 sh2) =
    executeL2 cardDB (fixedOracle sh1 sh2) 0 stateA (mkLoopTrace sh1 sh2) := by
  apply bridge_sound oracle (fixedOracle sh1 sh2) sh1
  · simp [fixedOracle, hsh1]
  · simp [fixedOracle, hsh2]
  · exact bridge_check_ok sh1 sh2 hp1 hp2

-- ============================================================
-- MAIN THEOREM
-- ============================================================

theorem is_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  let sh1 := oracle 0 pile1
  let sh2 := oracle 1 (mkPile2 sh1)
  have hPerm1 : sh1.Perm pile1 := hValid 0 pile1
  have hPerm2 : sh2.Perm (mkPile2 sh1) := hValid 1 (mkPile2 sh1)
  have hBridge := oracle_bridge oracle sh1 sh2 rfl rfl hPerm1 hPerm2
  have hVerify := verify_from_perm sh1 sh2 hPerm1 hPerm2
  unfold verifyPair at hVerify
  generalize hres : executeL2 cardDB (fixedOracle sh1 sh2) 0 stateA (mkLoopTrace sh1 sh2) = result
  rw [hres] at hVerify
  match result, hVerify, hres with
  | some (stateB, finalIdx), hVerify, hres =>
    simp [Bool.and_eq_true] at hVerify
    refine ⟨mkLoopTrace sh1 sh2, stateB, finalIdx, ?_, hVerify.1, hVerify.2⟩
    rw [hBridge, hres]
  | none, hVerify, _ => simp at hVerify

end ComboStormStrike_L2_Strict
