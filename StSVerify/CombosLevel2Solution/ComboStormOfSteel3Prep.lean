/-
  Storm of Steel+ + Tactician+ + Reflex+ + 3×Prepared+ (6 cards) - Level 2 Strict
  12 damage per loop (3 Shivs × 4 damage)

  Key insight: stateA has hand = {sos, tact, reflex, prep}, drawPile = {}, discard = {prep, prep}.
  Loop: play SoS (3 shivs), Prep draw 2 + discard tact, endTurn, 5 draws, Prep fixup (failDraw).
  The fixup always draws the 6th card from drawPile, failDraws, and discards a prep.
  This guarantees hand = {sos, tact, reflex, prep} regardless of oracle output.

  Proof strategy:
  1. Computational verification: all 120 × 720 = 86400 permutation pairs verified via native_decide
  2. Oracle bridge: drawCondBool (boolean) + soundness lemma
  3. Main theorem: combine bridge + verification
-/

import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB

open CardName Action

namespace ComboStormOfSteel3Prep_L2_Strict

-- ============================================================
-- CARD INSTANCES
-- ============================================================

private def sos : CardInstance := { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }
private def tact : CardInstance := { id := 1, name := TacticianPlus, cost := 0, damage := 0 }
private def reflex : CardInstance := { id := 2, name := ReflexPlus, cost := 0, damage := 0 }
private def prep3 : CardInstance := { id := 3, name := PreparedPlus, cost := 0, damage := 0 }
private def prep4 : CardInstance := { id := 4, name := PreparedPlus, cost := 0, damage := 0 }
private def prep5 : CardInstance := { id := 5, name := PreparedPlus, cost := 0, damage := 0 }

def cards : List (CardName × Nat) := [
  (StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1), (PreparedPlus, 3)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- ============================================================
-- SETUP
-- ============================================================

def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0,
  .draw 5, .draw 1, .draw 2,
  .play 6, .play 7, .play 8, .play 9,
  .play 5, .draw 3, .draw 4, .discard 1,
  .endTurn,
  .draw 4, .draw 3, .draw 2, .draw 1, .draw 5,
  .play 5, .draw 0, .failDraw, .discard 4]

def stateA : GameState := {
  hand := [sos, tact, reflex, prep3],
  drawPile := [],
  discardPile := [prep5, prep4],
  exhaustPile := [{ id := 9, name := Shiv, cost := 0, damage := 4 },
                  { id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 }],
  inUse := [], actionQueue := [],
  energy := 3, damage := 16, block := 0,
  stance := .Neutral, orbs := [], orbSlots := 3, focus := 0,
  enemy := enemy, activePowers := [], nextId := 10,
  noDraw := false, corruptionActive := false }

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- ============================================================
-- LOOP TRACE (parameterized by oracle outputs)
-- ============================================================

-- pile0: discard pile at first shuffle (after SoS discards hand)
-- SoS discards [prep3, reflex, tact] from hand, plus existing discard [prep5, prep4]
-- Order: tact, reflex, prep3 (discarded R-to-L), then prep5, prep4 (existing)
-- After autoDrain: [prep3, reflex, tact, prep5, prep4]
private def pile0 : List CardInstance := [tact, reflex, prep3, prep5, prep4]

private def isPrep (c : CardInstance) : Bool := c.name == PreparedPlus

private def pickPrep3 (d1 d2 d3 : CardInstance) : CardInstance :=
  if isPrep d3 then d3 else if isPrep d2 then d2 else d1

private def pickPrepFromHand5 (drawn5 : List CardInstance) : CardInstance :=
  match drawn5.find? isPrep with
  | some c => c
  | none => drawn5[0]!

-- Pick a prep from the 5-card hand (after fixup draw) to discard.
-- The hand has 5 cards: (drawn5 minus playedPrep) ++ [drawnFromDrawPile].
-- We want to discard any prep from this 5-card hand.
private def pickDiscardPrep (drawn5 : List CardInstance) (playedPrep drawnCard : CardInstance) : CardInstance :=
  let hand := drawnCard :: (drawn5.filter (· != playedPrep))
  match hand.find? (fun c => isPrep c && c.id != playedPrep.id) with
  | some c => c
  | none => hand[0]!

def mkLoopTrace (p1 p2 : List CardInstance) : List Action :=
  match p1 with
  | d1 :: d2 :: d3 :: d4 :: [d5] =>
    let prep := pickPrep3 d1 d2 d3
    let drawn5 := p2.take 5
    let leftover := p2[5]!
    let fixupPrep := pickPrepFromHand5 drawn5
    let discardTarget := pickDiscardPrep drawn5 fixupPrep leftover
    [.play 0,  -- play SoS: 3 discards, 3 shivs, Tact+2E, Reflex 3 draws
     .draw d1.id, .draw d2.id, .draw d3.id,  -- 3 Reflex draws from oracle 0
     .play 10, .play 11, .play 12,  -- play 3 shivs
     .play prep.id, .draw d4.id, .draw d5.id, .discard 1,  -- Prep: draw 2, discard tact
     .endTurn] ++
    drawn5.map (fun c => Action.draw c.id) ++  -- 5 draws from oracle 1
    [.play fixupPrep.id,  -- play fixup Prep
     .draw leftover.id,   -- draw the 6th card from drawPile
     .failDraw,           -- 2nd draw fails (piles empty)
     .discard discardTarget.id]  -- discard a prep
  | _ => []

private def fixOracle (p1 p2 : List CardInstance) : ShuffleOracle :=
  fun idx _pile => if idx == 0 then p1 else if idx == 1 then p2 else _pile

-- ============================================================
-- PERMUTATION HELPERS
-- ============================================================

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

-- ============================================================
-- DRAW-ONLY ORACLE BRIDGE (drawCondBool approach)
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
            rcases hdpOk with ⟨hsi, hdisc⟩ | ⟨hsi, hdisc⟩
            · rw [hsi, hdisc]; exact h0
            · rw [hsi, hdisc]; exact h1
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

private def sixCards : List CardInstance := [sos, tact, reflex, prep3, prep4, prep5]

-- Compute the discard pile at oracle 1 shuffle time for a given p1
-- (run the trace up to endTurn to get the state, then return discardPile)
private def getPile1 (p1 : List CardInstance) : List CardInstance :=
  match p1 with
  | d1 :: d2 :: d3 :: d4 :: [d5] =>
    let prep := pickPrep3 d1 d2 d3
    let orc : ShuffleOracle := fun idx _pile => if idx == 0 then p1 else _pile
    let tr := [.play 0, .draw d1.id, .draw d2.id, .draw d3.id,
               .play 10, .play 11, .play 12,
               .play prep.id, .draw d4.id, .draw d5.id, .discard 1,
               .endTurn]
    match executeL2 cardDB orc 0 stateA tr with
    | some (s, _) => s.discardPile
    | none => []
  | _ => []

private def verifyOne (p1 p2 : List CardInstance) : Bool :=
  match executeL2 cardDB (fixOracle p1 p2) 0 stateA (mkLoopTrace p1 p2) with
  | some (stB, _) =>
    sameModAccum stateA stB && dealtDamage stateA stB &&
    drawCondBool (fixOracle p1 p2) pile0 (getPile1 p1) 0 stateA (mkLoopTrace p1 p2)
  | none => false

private def verifyAll : Bool :=
  (permsOf pile0).all fun p1 => (permsOf sixCards).all fun p2 => verifyOne p1 p2

private theorem verifyAll_ok : verifyAll = true := by native_decide

private theorem verify_from_perms {p1 p2 : List CardInstance}
    (hp1 : p1 ∈ permsOf pile0) (hp2 : p2 ∈ permsOf sixCards) :
    verifyOne p1 p2 = true := by
  have hva := verifyAll_ok; unfold verifyAll at hva
  exact List.all_eq_true.mp (List.all_eq_true.mp hva p1 hp1) p2 hp2

-- ============================================================
-- ORACLE SINGLETON LEMMA
-- ============================================================

private theorem oracle_single (oracle : ShuffleOracle) (hv : validOracle oracle) (n : Nat)
    (a : CardInstance) : oracle n [a] = [a] :=
  List.perm_singleton.mp (hv n [a])

-- ============================================================
-- CASE HANDLER
-- ============================================================

private theorem case_handler (p1 p2 : List CardInstance)
    (hmem1 : p1 ∈ permsOf pile0) (hmem2 : p2 ∈ permsOf sixCards)
    (oracle : ShuffleOracle)
    (h0 : oracle 0 pile0 = p1)
    (h1 : oracle 1 (getPile1 p1) = p2) :
    ∃ (stB : GameState) (fIdx : Nat) (trace : List Action),
      executeL2 cardDB oracle 0 stateA trace = some (stB, fIdx)
      ∧ sameModAccum stateA stB = true
      ∧ dealtDamage stateA stB = true := by
  have hv := verify_from_perms hmem1 hmem2
  unfold verifyOne at hv
  have hf0 : oracle 0 pile0 = fixOracle p1 p2 0 pile0 := by
    simp only [fixOracle]; exact h0
  have hf1 : oracle 1 (getPile1 p1) = fixOracle p1 p2 1 (getPile1 p1) := by
    simp only [fixOracle]; exact h1
  generalize hres :
    executeL2 cardDB (fixOracle p1 p2) 0 stateA (mkLoopTrace p1 p2) = result at hv
  match result, hv with
  | some (stB, fIdx), hv =>
    simp only [Bool.and_eq_true] at hv
    obtain ⟨⟨hsm, hdd⟩, hdc⟩ := hv
    have hbridge := drawCondBool_bridge oracle (fixOracle p1 p2) pile0 (getPile1 p1)
      hf0 hf1 0 stateA (mkLoopTrace p1 p2) hdc
    exact ⟨stB, fIdx, mkLoopTrace p1 p2, hbridge ▸ hres, hsm, hdd⟩
  | none, hv => simp at hv

-- ============================================================
-- PILE1 MEMBERSHIP (computationally verified)
-- ============================================================

-- For each p1 ∈ permsOf pile0, getPile1 p1 ∈ permsOf sixCards
private def checkPile1Mem : Bool :=
  (permsOf pile0).all fun p1 =>
    (permsOf sixCards).any fun p2 => decide (getPile1 p1 = p2)

private theorem checkPile1Mem_ok : checkPile1Mem = true := by native_decide

private theorem getPile1_mem_sixCards {p1 : List CardInstance}
    (hp1 : p1 ∈ permsOf pile0) : getPile1 p1 ∈ permsOf sixCards := by
  have := checkPile1Mem_ok; unfold checkPile1Mem at this
  have h := List.all_eq_true.mp this p1 hp1
  rw [List.any_eq_true] at h
  obtain ⟨p2, hp2, heq⟩ := h
  simp [decide_eq_true_eq] at heq
  rw [heq]; exact hp2

-- permsOf soundness: membership implies Perm
private theorem insertEverywhere_perm (x : CardInstance) (l : List CardInstance) :
    ∀ m, m ∈ insertEverywhere x l → m.Perm (x :: l) := by
  induction l with
  | nil => intro m hm; simp [insertEverywhere] at hm; rw [hm]
  | cons y ys ih =>
    intro m hm
    simp [insertEverywhere] at hm
    rcases hm with rfl | ⟨m', hm', rfl⟩
    · exact List.Perm.refl _
    · exact (List.Perm.cons y (ih m' hm')).trans (List.Perm.swap x y ys)

private theorem permsOf_sound (l pile : List CardInstance) (hm : l ∈ permsOf pile) :
    l.Perm pile := by
  induction pile generalizing l with
  | nil => simp [permsOf] at hm; rw [hm]
  | cons x xs ih =>
    simp [permsOf, List.mem_flatMap] at hm
    obtain ⟨rest, hrest, hl⟩ := hm
    exact (insertEverywhere_perm x rest l hl).trans (List.Perm.cons x (ih rest hrest))

-- ============================================================
-- MAIN THEOREM
-- ============================================================

set_option maxHeartbeats 8000000 in
private theorem loop_l2 (oracle : ShuffleOracle) (hv : validOracle oracle) :
    ∃ (stB : GameState) (fIdx : Nat) (trace : List Action),
      executeL2 cardDB oracle 0 stateA trace = some (stB, fIdx)
      ∧ sameModAccum stateA stB = true
      ∧ dealtDamage stateA stB = true := by
  have hp0 : (oracle 0 pile0).Perm pile0 := hv 0 pile0
  have hp0_mem := permsOf_complete _ pile0 hp0
  let p1 := oracle 0 pile0
  have pile1_perm : (oracle 1 (getPile1 p1)).Perm (getPile1 p1) := hv 1 (getPile1 p1)
  have hgp1_mem := getPile1_mem_sixCards hp0_mem
  have hgp1_perm : (getPile1 p1).Perm sixCards := permsOf_sound _ _ hgp1_mem
  have hp1_mem := permsOf_complete _ sixCards (pile1_perm.trans hgp1_perm)
  exact case_handler p1 (oracle 1 (getPile1 p1)) hp0_mem hp1_mem oracle rfl rfl

theorem ComboStormOfSteel3Prep_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hvalid
  obtain ⟨stB, fIdx, trace, hexec, hsma, hdmg⟩ := loop_l2 oracle hvalid
  exact ⟨trace, stB, fIdx, hexec, hsma, hdmg⟩

end ComboStormOfSteel3Prep_L2_Strict
