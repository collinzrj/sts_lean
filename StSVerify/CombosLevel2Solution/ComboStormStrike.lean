/-
  Storm of Steel+ + Tactician+ + Reflex+ + Prepared+ + Strike Silent (5 cards) - Level 2
  v3 engine: resolveCard via autoDrain.
  stateA: all 5 in hand. Single loop variant for all oracles.

  Key insight: the loop does NOT play SoS at all.
  Loop: play Strike (6 dmg) → play Prep → draw Strike from 1-card shuffle →
  failDraw → discard Reflex (draw 3) → discard Tact (+2E) →
  draw all 3 from [Prep, Tact, Reflex] shuffle → back to stateA.

  Shuffle 0: [Strike] (1 card, trivial).
  Shuffle 1: [Prep, Tact, Reflex] (3 cards, draw all 3, 6 permutations).
  Oracle only affects draw order in the 3-card shuffle, not the outcome.
-/

import StSVerify.CombosSpecL2.ComboStormStrike
import StSVerify.EngineHelperLemmas

open CardName Action

namespace ComboStormStrike_L2

private def ci0 : CardInstance := { id := 0, name := StormOfSteelPlus, cost := 1, damage := 0 }
private def ci1 : CardInstance := { id := 1, name := TacticianPlus, cost := 0, damage := 0 }
private def ci2 : CardInstance := { id := 2, name := ReflexPlus, cost := 0, damage := 0 }
private def ci3 : CardInstance := { id := 3, name := PreparedPlus, cost := 0, damage := 0 }
private def ci4 : CardInstance := { id := 4, name := StrikeSilent, cost := 1, damage := 6 }



-- Setup: draw 5, play SoS, draw 3, play 4 shivs, play Prep, draw 2, discard 2, draw 3
def setupTrace : List Action := [
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 0,
  .draw 1, .draw 2, .draw 3,
  .play 5, .play 6, .play 7, .play 8,
  .play 3,
  .draw 4, .draw 0,
  .discard 2, .discard 1,
  .draw 3, .draw 1, .draw 2
]

def stateA : GameState := {
  hand := [ci2, ci1, ci3, ci0, ci4], drawPile := [], discardPile := []
  exhaustPile := [{ id := 8, name := Shiv, cost := 0, damage := 4 },
                  { id := 7, name := Shiv, cost := 0, damage := 4 },
                  { id := 6, name := Shiv, cost := 0, damage := 4 },
                  { id := 5, name := Shiv, cost := 0, damage := 4 }]
  inUse := [], actionQueue := []
  energy := 6, damage := 16, block := 0, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [], nextId := 9, noDraw := false, corruptionActive := false
}

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- Piles (what gets shuffled at each index)
-- pile0: after Strike played + Prep played, discard = [Strike(4)]
-- pile1: after Reflex+Tact discarded + Prep resolved, discard = [Prep(3), Tact(1), Reflex(2)]
private def pile0 : List CardInstance := [ci4]
private def pile1 : List CardInstance := [ci3, ci1, ci2]

-- Loop trace: the only oracle-varying part is the draw IDs for shuffle 1
def mkLoopTrace (sh1 : List CardInstance) : List Action :=
  match sh1 with
  | [a, b, c] =>
    [.play 4,                        -- Play Strike (6 dmg, 1E)
     .play 3,                        -- Play Prep (draw 2, discard 2)
     .draw 4,                        -- Draw Strike from shuffle of [Strike]
     .failDraw,                      -- Can't draw 2nd (both piles empty)
     .discard 2,                     -- Discard Reflex (draw 3 trigger)
     .discard 1,                     -- Discard Tact (+2E trigger)
     .draw a.id, .draw b.id, .draw c.id  -- Draw all 3 from shuffle of [Prep, Tact, Reflex]
    ]
  | _ => []

-- Fixed oracle for verification
def fixedOracle (sh1 : List CardInstance) : ShuffleOracle := fun idx _ =>
  if idx == 0 then [ci4] else if idx == 1 then sh1 else []

-- drawCondBool: at each draw step, either drawPile is non-empty or
-- the oracle agrees on the specific (shIdx, discardPile) pair
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

-- All 6 permutations of pile1 = [Prep, Tact, Reflex]
private def allPerms3 : List (List CardInstance) :=
  [ [ci3, ci1, ci2], [ci3, ci2, ci1], [ci1, ci3, ci2], [ci1, ci2, ci3], [ci2, ci3, ci1], [ci2, ci1, ci3] ]

-- Verify each permutation
private def verifyOne (sh1 : List CardInstance) : Bool :=
  let fo := fixedOracle sh1
  let trace := mkLoopTrace sh1
  match executeL2 cardDB fo 0 stateA trace with
  | some (stateB, _) =>
    sameModAccum stateA stateB && dealtDamage stateA stateB &&
    drawCondBool fo 0 stateA trace && noEndTurn trace
  | none => false

private def verifyAll : Bool :=
  allPerms3.all fun sh1 => verifyOne sh1

set_option maxHeartbeats 8000000 in
theorem all_verified : verifyAll = true := by native_decide

-- Perm membership: any permutation of pile1 is in allPerms3
set_option maxHeartbeats 800000 in
private theorem perm3_mem (l : List CardInstance) (hp : l.Perm pile1) : l ∈ allPerms3 := by
  have hlen := hp.length_eq; simp [pile1] at hlen
  match l, hlen with
  | [x, y, z], _ =>
    have hx : x ∈ pile1 := hp.mem_iff.mp (by simp)
    have hy : y ∈ pile1 := hp.mem_iff.mp (by simp)
    have hz : z ∈ pile1 := hp.mem_iff.mp (by simp)
    simp only [pile1, ci1, ci2, ci3, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy hz
    have hnd : [x, y, z].Nodup := hp.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or, List.not_mem_nil,
               not_false_eq_true, and_true, and_self] at hnd
    obtain ⟨⟨hxy, hxz⟩, hyz, _⟩ := hnd
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      (try exact absurd rfl hxy) <;> rcases hz with rfl | rfl | rfl <;>
      (try exact absurd rfl hxz) <;> (try exact absurd rfl hyz) <;>
      simp [allPerms3, ci1, ci2, ci3]

-- Singleton perm: any permutation of [ci4] is [ci4]
private theorem perm1_eq (l : List CardInstance) (hp : l.Perm [ci4]) : l = [ci4] := by
  have hlen := hp.length_eq; simp at hlen
  match l, hlen with
  | [x], _ =>
    have hx : x ∈ [ci4] := hp.mem_iff.mp (by simp)
    simp at hx; exact congrArg (·::List.nil) hx

-- Main handler: for any sh1 permutation, the loop works
private theorem handle_loop (sh1 : List CardInstance)
    (hmem1 : sh1 ∈ allPerms3)
    (oracle : ShuffleOracle)
    (h0 : oracle 0 pile0 = [ci4]) (h1 : oracle 1 pile1 = sh1) :
    ∃ t sB fi, executeL2 cardDB oracle 0 stateA t = some (sB, fi)
      ∧ noEndTurn t = true ∧ sameModAccum stateA sB = true ∧ dealtDamage stateA sB = true := by
  have hva := all_verified; unfold verifyAll at hva; rw [List.all_eq_true] at hva
  have hv := hva sh1 hmem1
  simp only [verifyOne] at hv
  split at hv
  · next stB fIdx heq =>
    simp only [Bool.and_eq_true] at hv; obtain ⟨⟨⟨hsm, hdd⟩, hdc⟩, hne⟩ := hv
    have hf0 : oracle 0 pile0 = fixedOracle sh1 0 pile0 := by simp [fixedOracle]; exact h0
    have hf1 : oracle 1 pile1 = fixedOracle sh1 1 pile1 := by simp [fixedOracle]; exact h1
    exact ⟨_, stB, fIdx, (drawCondBool_bridge oracle _ hf0 hf1 0 stateA _ hdc) ▸ heq, hne, hsm, hdd⟩
  · simp at hv

-- Main theorem
theorem ComboStormStrike_L2_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  -- The oracle controls shuffles. Shuffle 0 is of [ci4] (1 card), shuffle 1 is of pile1 (3 cards).
  -- Singleton shuffle: oracle must return [ci4]
  have hsh0 : oracle 0 pile0 = [ci4] := by
    have hp := hValid 0 pile0
    exact perm1_eq (oracle 0 pile0) hp
  -- 3-element shuffle: oracle returns a permutation of pile1
  have hsh1_mem := perm3_mem (oracle 1 pile1) (hValid 1 pile1)
  exact handle_loop _ hsh1_mem oracle hsh0 rfl

theorem proof : GuaranteedInfiniteCombo cardDB cards enemy := ComboStormStrike_L2_guaranteed_infinite

end ComboStormStrike_L2
