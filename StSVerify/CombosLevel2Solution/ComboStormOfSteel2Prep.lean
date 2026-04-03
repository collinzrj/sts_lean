/-
  Storm of Steel+ + Tactician+ + Reflex+ + 2x Prepared+ (5 cards) - Level 2

  RESULT: Guaranteed infinite at Level 2.

  Key insight: use a stateA where SoS is in hand (not in discard).
  The loop plays SoS first, creating 3 Shivs. The adversarial oracle can
  strand any 1 of 4 cards after the Reflex trigger's 3 draws. Prepared+
  rescues the stranded card from drawPile, plus SoS from a singleton
  shuffle. Discarding Tactician+ and Reflex+ fires their triggers,
  recovering all cards. sameModAccum holds because the two Prepared+
  copies are interchangeable.

  Shuffle points in loop:
    0: [Reflex, Tact, P4, P3] (4 cards) -- 4! = 24 perms
    1: [SoS] (singleton) -- deterministic
    2: [Reflex, Tact] (2 cards) -- 2! = 2 perms

  Uses drawCondBool bridge pattern for oracle agreement.
-/

import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB

open CardName Action

namespace ComboStormOfSteel2Prep_L2

-- ============================================================
-- CARD INSTANCES
-- ============================================================

private def ci0 : CardInstance := { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }
private def ci1 : CardInstance := { id := 1, name := TacticianPlus, cost := 0, damage := 0 }
private def ci2 : CardInstance := { id := 2, name := ReflexPlus, cost := 0, damage := 0 }
private def ci3 : CardInstance := { id := 3, name := PreparedPlus, cost := 0, damage := 0 }
private def ci4 : CardInstance := { id := 4, name := PreparedPlus, cost := 0, damage := 0 }

-- ============================================================
-- FRAMEWORK
-- ============================================================

def cards : List (CardName × Nat) := [
  (StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1), (PreparedPlus, 2)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

private def exhaustBase : List CardInstance :=
  [{ id := 8, name := Shiv, cost := 0, damage := 4 },
   { id := 7, name := Shiv, cost := 0, damage := 4 },
   { id := 6, name := Shiv, cost := 0, damage := 4 },
   { id := 5, name := Shiv, cost := 0, damage := 4 }]

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0,
  .draw 1, .draw 2, .draw 3,
  .play 5, .play 6, .play 7, .play 8,
  .play 3,
  .draw 4, .draw 0,
  .discard 2, .discard 1,
  .draw 1, .draw 2, .failDraw
]

def stateA : GameState := {
  hand := [ci2, ci1, ci0, ci4]
  drawPile := []
  discardPile := [ci3]
  exhaustPile := exhaustBase
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
  nextId := 9
  noDraw := false
  corruptionActive := false
}

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- ============================================================
-- LOOP TRACE (adaptive, depends on oracle output)
-- ============================================================

private def pile0 : List CardInstance := [ci2, ci1, ci4, ci3]

/-- Construct the adaptive loop trace from oracle outputs at shuffle points 0 and 2.
    sh0 = oracle's permutation of pile0 (4 cards from SoS discard)
    sh2 = oracle's permutation of [ci2, ci1] (2 cards from Reflex trigger) -/
def mkLoopTrace (sh0 sh2 : List CardInstance) : List Action :=
  match sh0 with
  | a :: b :: c :: [d] =>
    let prepId := if d.id == 4 then 3 else 4
    [.play 0,
     .draw a.id, .draw b.id, .draw c.id,
     .play 9, .play 10, .play 11,
     .play prepId,
     .draw d.id, .draw 0,
     .discard 1, .discard 2] ++
    (sh2.map fun x => Action.draw x.id) ++
    [.failDraw]
  | _ => []

/-- The pile at shuffle point 2 is always [ci2, ci1] (Reflex then Tact discarded). -/
private def pile2 : List CardInstance := [ci2, ci1]

/-- Fixed oracle for computational verification.
    At idx 0: return sh0 (4-card permutation).
    At idx 1: return the pile unchanged (singleton, always [ci0]).
    At idx 2: return sh2 (2-card permutation). -/
def fixedOracle (sh0 sh2 : List CardInstance) : ShuffleOracle := fun idx pile =>
  if idx == 0 then sh0 else if idx == 2 then sh2 else pile

-- ============================================================
-- PERMUTATION HELPERS
-- ============================================================

set_option maxHeartbeats 800000 in
private theorem perm_4_cases (l : List CardInstance)
    (hp : l.Perm [ci2, ci1, ci4, ci3]) :
    l = [ci2, ci1, ci4, ci3] ∨ l = [ci2, ci1, ci3, ci4] ∨
    l = [ci2, ci4, ci1, ci3] ∨ l = [ci2, ci4, ci3, ci1] ∨
    l = [ci2, ci3, ci1, ci4] ∨ l = [ci2, ci3, ci4, ci1] ∨
    l = [ci1, ci2, ci4, ci3] ∨ l = [ci1, ci2, ci3, ci4] ∨
    l = [ci1, ci4, ci2, ci3] ∨ l = [ci1, ci4, ci3, ci2] ∨
    l = [ci1, ci3, ci2, ci4] ∨ l = [ci1, ci3, ci4, ci2] ∨
    l = [ci4, ci2, ci1, ci3] ∨ l = [ci4, ci2, ci3, ci1] ∨
    l = [ci4, ci1, ci2, ci3] ∨ l = [ci4, ci1, ci3, ci2] ∨
    l = [ci4, ci3, ci2, ci1] ∨ l = [ci4, ci3, ci1, ci2] ∨
    l = [ci3, ci2, ci1, ci4] ∨ l = [ci3, ci2, ci4, ci1] ∨
    l = [ci3, ci1, ci2, ci4] ∨ l = [ci3, ci1, ci4, ci2] ∨
    l = [ci3, ci4, ci2, ci1] ∨ l = [ci3, ci4, ci1, ci2] := by
  have hlen := hp.length_eq; simp at hlen
  have hmem : ∀ x ∈ l, x = ci2 ∨ x = ci1 ∨ x = ci4 ∨ x = ci3 := by
    intro x hx; have hm := hp.subset hx
    simp [List.mem_cons, List.mem_nil_iff, or_false] at hm; exact hm
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
    simp [ci1, ci2, ci3, ci4]

private theorem perm_2_cases (l : List CardInstance)
    (hp : l.Perm [ci2, ci1]) : l = [ci2, ci1] ∨ l = [ci1, ci2] := by
  have hlen := hp.length_eq; simp at hlen
  match l, hlen with
  | [x, y], _ =>
    have hx : x ∈ [ci2, ci1] := hp.mem_iff.mp (by simp)
    have hy : y ∈ [ci2, ci1] := hp.mem_iff.mp (by simp)
    simp [List.mem_cons, List.mem_nil_iff] at hx hy
    have hnd : [x, y].Nodup := hp.nodup_iff.mpr (by decide)
    rw [List.nodup_cons] at hnd; simp [List.mem_cons, List.mem_nil_iff] at hnd
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> (first | simp_all | omega)

-- ============================================================
-- DRAW-ONLY ORACLE BRIDGE
-- ============================================================

/-- At each draw step along the fixed oracle execution where drawPile is empty,
    check that we're at a known shuffle point (idx 0 with pile0, or idx 2 with pile2).
    The singleton shuffle at idx 1 has drawPile = [ci0] after the oracle places it,
    so drawPile is actually non-empty there -- no special handling needed. -/
private def drawCondBool (fo : ShuffleOracle) (p0 p2 : List CardInstance)
    (si : Nat) (s : GameState) : List Action → Bool
  | [] => true
  | a :: rest =>
    let sc := resolveInUse cardDB (autoDrain cardDB s)
    let dpOk := match a with
      | .draw _ => sc.drawPile.length > 0 ||
                   (decide (si = 0) && decide (sc.discardPile = p0)) ||
                   (decide (si = 1) && decide (sc.discardPile = [ci0])) ||
                   (decide (si = 2) && decide (sc.discardPile = p2))
      | _ => true
    match stepL2 cardDB fo si sc a with
    | some (s', si') => dpOk && drawCondBool fo p0 p2 si' s' rest
    | none => false

/-- Oracle bridge: if drawCondBool passes and oracle agrees at shuffle points,
    then executeL2 gives the same result for both oracles. -/
private theorem drawCondBool_bridge (oracle fo : ShuffleOracle) (p0 p2 : List CardInstance)
    (h0 : oracle 0 p0 = fo 0 p0)
    (h1 : oracle 1 [ci0] = fo 1 [ci0])
    (h2 : oracle 2 p2 = fo 2 p2)
    (si : Nat) (s : GameState) (trace : List Action)
    (hb : drawCondBool fo p0 p2 si s trace = true) :
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
            -- 3 possible shuffle points: si = 0/1/2 with corresponding disc pile
            rcases hdpOk with ⟨hsi, hdisc⟩ | ⟨hsi, hdisc⟩ | ⟨hsi, hdisc⟩ <;> simp_all
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

private def verifyOne (sh0 sh2 : List CardInstance) : Bool :=
  match executeL2 cardDB (fixedOracle sh0 sh2) 0 stateA (mkLoopTrace sh0 sh2) with
  | some (stateB, _) =>
    sameModAccum stateA stateB && dealtDamage stateA stateB &&
    drawCondBool (fixedOracle sh0 sh2) pile0 pile2 0 stateA (mkLoopTrace sh0 sh2) &&
    noEndTurn (mkLoopTrace sh0 sh2)
  | none => false

private def allPerms4 : List (List CardInstance) :=
  [ [ci2, ci1, ci4, ci3], [ci2, ci1, ci3, ci4],
    [ci2, ci4, ci1, ci3], [ci2, ci4, ci3, ci1],
    [ci2, ci3, ci1, ci4], [ci2, ci3, ci4, ci1],
    [ci1, ci2, ci4, ci3], [ci1, ci2, ci3, ci4],
    [ci1, ci4, ci2, ci3], [ci1, ci4, ci3, ci2],
    [ci1, ci3, ci2, ci4], [ci1, ci3, ci4, ci2],
    [ci4, ci2, ci1, ci3], [ci4, ci2, ci3, ci1],
    [ci4, ci1, ci2, ci3], [ci4, ci1, ci3, ci2],
    [ci4, ci3, ci2, ci1], [ci4, ci3, ci1, ci2],
    [ci3, ci2, ci1, ci4], [ci3, ci2, ci4, ci1],
    [ci3, ci1, ci2, ci4], [ci3, ci1, ci4, ci2],
    [ci3, ci4, ci2, ci1], [ci3, ci4, ci1, ci2] ]

private def allPerms2 : List (List CardInstance) := [[ci2, ci1], [ci1, ci2]]

private def verifyAll : Bool :=
  allPerms4.all fun sh0 => allPerms2.all fun sh2 => verifyOne sh0 sh2

-- Single native_decide for all 48 cases
theorem all_verified : verifyAll = true := by native_decide

private theorem verifyOne_of_mem (sh0 sh2 : List CardInstance)
    (h0 : sh0 ∈ allPerms4) (h2 : sh2 ∈ allPerms2) :
    verifyOne sh0 sh2 = true := by
  have hva := all_verified
  unfold verifyAll at hva
  rw [List.all_eq_true] at hva
  have h0' := hva sh0 h0
  rw [List.all_eq_true] at h0'
  exact h0' sh2 h2

-- ============================================================
-- CASE HANDLER
-- ============================================================

private theorem case_handler (sh0 sh2 : List CardInstance)
    (hmem0 : sh0 ∈ allPerms4) (hmem2 : sh2 ∈ allPerms2)
    (oracle : ShuffleOracle)
    (hValid : validOracle oracle)
    (ho0 : oracle 0 pile0 = sh0)
    (ho2 : oracle 2 pile2 = sh2) :
    ∃ (loopTrace : List Action) (stateB : GameState) (finalIdx : Nat),
      executeL2 cardDB oracle 0 stateA loopTrace = some (stateB, finalIdx)
      ∧ noEndTurn loopTrace = true
      ∧ sameModAccum stateA stateB = true
      ∧ dealtDamage stateA stateB = true := by
  have hv := verifyOne_of_mem sh0 sh2 hmem0 hmem2
  unfold verifyOne at hv
  have hf0 : oracle 0 pile0 = fixedOracle sh0 sh2 0 pile0 := by
    simp only [fixedOracle]; exact ho0
  -- At idx 1, fixedOracle returns pile unchanged. A valid oracle on a singleton
  -- also returns the singleton. More generally, we need oracle 1 pile = pile for
  -- any pile encountered. The drawCondBool only checks idx 1 when disc = [ci0],
  -- so we only need agreement there. But the bridge requires ∀ pile agreement.
  -- Actually: the fixedOracle at idx 1 returns pile (identity). For the real oracle,
  -- the only pile passed to oracle at idx 1 during execution is [ci0] (singleton).
  -- But the bridge requires agreement for ALL piles at idx 1 (since it's a ∀ pile).
  -- This is too strong. Let me weaken the bridge to only require agreement when
  -- drawCondBool actually checks (i.e., when disc matches the known pattern).
  -- Actually the bridge just needs oracle and fo to agree at the specific (si, pile)
  -- pairs that drawCondBool flags. Since drawCondBool checks si=1 with disc=[ci0],
  -- we need oracle 1 [ci0] = fo 1 [ci0] = [ci0]. This is true for valid oracles
  -- (singleton perm) and for fixedOracle (returns pile).
  have hf1 : oracle 1 [ci0] = fixedOracle sh0 sh2 1 [ci0] := by
    simp only [fixedOracle, ci0]
    exact List.perm_singleton.mp (hValid 1 [ci0])
  have hf2 : oracle 2 pile2 = fixedOracle sh0 sh2 2 pile2 := by
    simp only [fixedOracle]; exact ho2
  generalize hres : executeL2 cardDB (fixedOracle sh0 sh2) 0 stateA (mkLoopTrace sh0 sh2) = result at hv
  match result, hv with
  | some (stB, fIdx), hv =>
    simp only [Bool.and_eq_true] at hv
    obtain ⟨⟨⟨hsm, hdd⟩, hdc⟩, hne⟩ := hv
    have hbridge := drawCondBool_bridge oracle (fixedOracle sh0 sh2) pile0 pile2 hf0 hf1 hf2 0 stateA
      (mkLoopTrace sh0 sh2) hdc
    exact ⟨mkLoopTrace sh0 sh2, stB, fIdx, hbridge ▸ hres, hne, hsm, hdd⟩
  | none, hv => simp at hv

-- ============================================================
-- MAIN THEOREM
-- ============================================================

set_option maxHeartbeats 8000000 in
theorem ComboStormOfSteel2Prep_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  have hPerm0 : List.Perm (oracle 0 pile0) pile0 := hValid 0 pile0
  have h4 := perm_4_cases (oracle 0 pile0) hPerm0
  rcases h4 with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 |
                 h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 |
                 h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 <;> (
    have hPerm2 : (oracle 2 pile2).Perm pile2 := hValid 2 pile2
    have h2cases := perm_2_cases (oracle 2 pile2) hPerm2
    rcases h2cases with h2 | h2 <;>
      exact case_handler _ _ (by simp [allPerms4]) (by simp [allPerms2]) oracle hValid h0 h2
  )

end ComboStormOfSteel2Prep_L2
