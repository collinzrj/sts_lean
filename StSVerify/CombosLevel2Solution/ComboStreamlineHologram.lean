/-
  故障機器人 - 流線型+全息影像+精簡 (Level 2)
  Cards: 11
  v2 engine rewrite

  Engine v3 change: hologramChoose is now queue-gated.
  New loop strategy uses Turbo+Skim+CoolheadedPlus+Recycle chain.

  Loop: play CH first (so shuffle 0 is only [H2, H1] = 2 cards),
  then Turbo, SL, Holograms, Skim (shuffle 1 = 4 cards), Recycle, Holograms.

  Shuffle 0: disc=[H2, H1] -> 2! = 2 perms
  Shuffle 1: disc=[H2, SL, Turbo, Void] -> 4! = 24 perms
  Total: 48 cases, all verified by native_decide in batches.
-/

import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB

open CardName Action

namespace ComboStreamlineHologram_L2

-- ============================================================
-- CARD INSTANCES
-- ============================================================

private def ci0  : CardInstance := { id := 0,  name := StreamlinePlus,  cost := 0, damage := 20 }
private def ci1  : CardInstance := { id := 1,  name := HologramPlus,    cost := 0, damage := 0 }
private def ci2  : CardInstance := { id := 2,  name := HologramPlus,    cost := 0, damage := 0 }
private def ci9  : CardInstance := { id := 9,  name := TurboPlus,       cost := 0, damage := 0 }
private def ci12 : CardInstance := { id := 12, name := Void,            cost := 0, damage := 0 }

-- ============================================================
-- Deck definition (v2: CardName × count)
-- ============================================================

def cards : List (CardName × Nat) :=
  [ (StreamlinePlus, 1)      -- id 0
  , (HologramPlus, 2)        -- ids 1,2
  , (CoolheadedPlus, 1)      -- id 3
  , (DefragmentPlus, 1)      -- id 4
  , (BiasedCognitionPlus, 1) -- id 5
  , (CapacitorPlus, 1)       -- id 6
  , (RecyclePlus, 1)         -- id 7
  , (SkimPlus, 1)            -- id 8
  , (TurboPlus, 1)           -- id 9
  , (RebootPlus, 1)          -- id 10
  ]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- ============================================================
-- SETUP AND LOOP
-- ============================================================

def setupTrace : List Action :=
  [ -- Turn 1: Draw powers + Reboot. Play 3 powers + Reboot.
    .draw 4, .draw 5, .draw 6, .draw 0, .draw 10,
    .play 4,   -- Defrag (power, 1E)
    .play 5,   -- Biased Cognition (power, 1E)
    .play 6,   -- Capacitor (power, 1E). E=0. OrbSlots=6. Focus=5.
    .play 10,  -- Reboot (0E): shuffle hand into draw, draw 5, exhaust self
    .draw 0, .draw 1, .draw 2, .draw 3, .draw 7,
    .endTurn,
    -- Turn 2: SL(2->1), CH(Frost#1)
    .draw 8, .draw 9,
    .draw 3, .draw 0, .draw 1,
    .play 0,   -- SL (2E): 20dmg, cost 2->1
    .play 3,   -- CH (1E): Frost#1, draw 2
    .draw 2, .draw 7,
    .endTurn,
    -- Turn 3: SL(1->0), CH(Frost#2)
    .draw 0, .draw 3, .draw 9, .draw 8, .draw 7,
    .play 0,   -- SL (1E): 20dmg, cost 1->0
    .play 3,   -- CH (1E): Frost#2, draw 2
    .draw 1, .draw 2,
    .endTurn,
    -- Turns 4-7: CH for Frost #3-#6
    .draw 3, .draw 0, .draw 9, .draw 8, .draw 7,
    .play 3, .draw 1, .draw 2,
    .endTurn,
    .draw 3, .draw 0, .draw 9, .draw 8, .draw 7,
    .play 3, .draw 1, .draw 2,
    .endTurn,
    .draw 3, .draw 0, .draw 9, .draw 8, .draw 7,
    .play 3, .draw 1, .draw 2,
    .endTurn,
    .draw 3, .draw 0, .draw 9, .draw 8, .draw 7,
    .play 3, .draw 1, .draw 2,
    .endTurn,
    -- Turn 8: Final arrangement
    .draw 3, .draw 0, .draw 9, .draw 8, .draw 7,
    .play 3,           -- CH (1E): Frost (stable at 6), draw 2
    .draw 1, .draw 2,
    .play 9,           -- Turbo (0E): +2E, Void(11) to disc
    .play 8,           -- Skim (1E): draw 4
    .draw 9, .draw 11, .draw 3, .failDraw,
    .play 7,           -- Recycle: exhaust Void(11)
    .recycleChoose 11,
    .play 1,           -- H1: retrieve Rec
    .hologramChoose 7,
    .play 2,           -- H2: retrieve Skim
    .hologramChoose 8
  ]

-- Loop trace parameterized by shuffle outputs
-- sh0: permutation of [H2, H1] (2 cards, shuffle 0 at CH draw)
-- sh1: permutation of [H2, SL, Turbo, Void] (4 cards, shuffle 1 at Skim draw)
def mkLoopTrace (sh0 sh1 : List CardInstance) : List Action :=
  match sh0 with
  | [a, b] =>
    match sh1 with
    | [p, q, r, s] =>
      [ .play 3,           -- CH (1E): Frost, draw 2
        .draw a.id, .draw b.id,  -- draw from shuffle 0
        .play 9,           -- Turbo (0E): +2E, Void(12) to disc
        .play 0,           -- SL (0E): 20dmg
        .play 1,           -- H1: retrieve CH
        .hologramChoose 3,
        .play 2,           -- H2: retrieve H1
        .hologramChoose 1,
        .play 8,           -- Skim (1E): draw 4
        .draw p.id, .draw q.id, .draw r.id, .draw s.id,  -- draw from shuffle 1
        .play 7,           -- Recycle: exhaust Void(12)
        .recycleChoose 12,
        .play 1,           -- H1: retrieve Rec
        .hologramChoose 7,
        .play 2,           -- H2: retrieve Skim
        .hologramChoose 8
      ]
    | _ => []
  | _ => []

def stateA : GameState := {
  hand := [{ id := 8, name := SkimPlus, cost := 1, damage := 0 },
           { id := 7, name := RecyclePlus, cost := 0, damage := 0 },
           { id := 3, name := CoolheadedPlus, cost := 1, damage := 0 },
           { id := 9, name := TurboPlus, cost := 0, damage := 0 },
           { id := 0, name := StreamlinePlus, cost := 0, damage := 20 }]
  drawPile := []
  discardPile := [{ id := 2, name := HologramPlus, cost := 0, damage := 0 },
                  { id := 1, name := HologramPlus, cost := 0, damage := 0 }]
  exhaustPile := [{ id := 11, name := Void, cost := 0, damage := 0 },
                  { id := 10, name := RebootPlus, cost := 0, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 40
  block := 10
  stance := .Neutral
  orbs := [.Frost, .Frost, .Frost, .Frost, .Frost, .Frost]
  orbSlots := 6
  focus := 5
  enemy := { vulnerable := 0, weak := 0, intending := false }
  activePowers := [CapacitorPlus, BiasedCognitionPlus, DefragmentPlus]
  nextId := 12
  noDraw := false
  corruptionActive := false
}

-- ============================================================
-- BASIC VERIFICATION
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

-- ============================================================
-- SHUFFLE PILES AND ORACLE
-- ============================================================

-- Pile 0: discard at time of CH's draw effect (only H2, H1)
private def pile0 : List CardInstance := [ci2, ci1]

-- Pile 1: discard at time of Skim's draw effect (H2, SL, Turbo, Void)
private def pile1 : List CardInstance := [ci2, ci0, ci9, ci12]

private def fixedOracle (p0 : List CardInstance) (p1 : List CardInstance) : ShuffleOracle :=
  fun idx _ => if idx == 0 then p0 else if idx == 1 then p1 else []

-- ============================================================
-- drawCondBool BRIDGE
-- ============================================================

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

-- ============================================================
-- PERMUTATION ENUMERATION AND VERIFICATION
-- ============================================================

-- All permutations of pile0 = [H2, H1] (2 elements)
private def allPerms2 : List (List CardInstance) :=
  [ [ci2, ci1], [ci1, ci2] ]

-- All permutations of pile1 = [H2, SL, Turbo, Void] (4 elements)
private def allPerms4 : List (List CardInstance) :=
  [ [ci2, ci0, ci9, ci12], [ci2, ci0, ci12, ci9], [ci2, ci9, ci0, ci12], [ci2, ci9, ci12, ci0],
    [ci2, ci12, ci0, ci9], [ci2, ci12, ci9, ci0],
    [ci0, ci2, ci9, ci12], [ci0, ci2, ci12, ci9], [ci0, ci9, ci2, ci12], [ci0, ci9, ci12, ci2],
    [ci0, ci12, ci2, ci9], [ci0, ci12, ci9, ci2],
    [ci9, ci2, ci0, ci12], [ci9, ci2, ci12, ci0], [ci9, ci0, ci2, ci12], [ci9, ci0, ci12, ci2],
    [ci9, ci12, ci2, ci0], [ci9, ci12, ci0, ci2],
    [ci12, ci2, ci0, ci9], [ci12, ci2, ci9, ci0], [ci12, ci0, ci2, ci9], [ci12, ci0, ci9, ci2],
    [ci12, ci9, ci2, ci0], [ci12, ci9, ci0, ci2] ]

private def verifyOne (p0 : List CardInstance) (p1 : List CardInstance) : Bool :=
  let fo := fixedOracle p0 p1
  let trace := mkLoopTrace p0 p1
  match executeL2 cardDB fo 0 stateA trace with
  | some (stB, _) =>
    sameModAccum stateA stB && dealtDamage stateA stB &&
    drawCondBool fo 0 stateA trace && noEndTurn trace
  | none => false

-- Verify one pile0 permutation against all pile1 permutations
private def verifyP0 (p0 : List CardInstance) : Bool :=
  allPerms4.all fun p1 => verifyOne p0 p1

-- Batch: verify for p0 = [ci2, ci1]
set_option maxHeartbeats 16000000 in
private theorem verify_p0a : verifyP0 [ci2, ci1] = true := by native_decide

-- Batch: verify for p0 = [ci1, ci2]
set_option maxHeartbeats 16000000 in
private theorem verify_p0b : verifyP0 [ci1, ci2] = true := by native_decide

-- ============================================================
-- PERMUTATION MEMBERSHIP LEMMAS
-- ============================================================

-- Singleton perm helper
private theorem perm_singleton_eq (a : CardInstance) (l : List CardInstance)
    (h : List.Perm l [a]) : l = [a] :=
  List.perm_singleton.mp h

-- 2-element perm membership
set_option maxHeartbeats 800000 in
private theorem perm2_mem (l : List CardInstance) (hp : l.Perm pile0) : l ∈ allPerms2 := by
  have hlen := hp.length_eq; simp [pile0] at hlen
  match l, hlen with
  | [a, b], _ =>
    have ha : a ∈ pile0 := hp.mem_iff.mp (by simp)
    have hb : b ∈ pile0 := hp.mem_iff.mp (by simp)
    simp only [pile0, ci2, ci1, List.mem_cons, List.mem_singleton, List.mem_nil_iff,
               or_false] at ha hb
    have hnd : [a, b].Nodup := hp.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff,
               not_or, List.not_mem_nil, not_false_eq_true, and_true] at hnd
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      (try exact absurd rfl hnd.1) <;>
      simp [allPerms2, ci1, ci2]

-- 4-element perm membership
set_option maxHeartbeats 6400000 in
private theorem perm4_mem (l : List CardInstance) (hp : l.Perm pile1) : l ∈ allPerms4 := by
  have hlen := hp.length_eq; simp [pile1] at hlen
  match l, hlen with
  | [a, b, c, d], _ =>
    have ha : a ∈ pile1 := hp.mem_iff.mp (by simp)
    have hb : b ∈ pile1 := hp.mem_iff.mp (by simp)
    have hc : c ∈ pile1 := hp.mem_iff.mp (by simp)
    have hd : d ∈ pile1 := hp.mem_iff.mp (by simp)
    simp only [pile1, ci2, ci0, ci9, ci12, List.mem_cons, List.mem_singleton, List.mem_nil_iff,
               or_false] at ha hb hc hd
    have hnd : [a, b, c, d].Nodup := hp.nodup_iff.mpr (by decide)
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl <;>
      simp (config := { decide := false }) only [allPerms4, ci2, ci0, ci9, ci12,
        List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false, or_true, true_or] <;>
      (revert hnd; native_decide)

-- ============================================================
-- MAIN HANDLER
-- ============================================================

private theorem handle_loop (p0 : List CardInstance) (p1 : List CardInstance)
    (hmem0 : p0 ∈ allPerms2) (hmem1 : p1 ∈ allPerms4)
    (oracle : ShuffleOracle)
    (h0 : oracle 0 pile0 = p0) (h1 : oracle 1 pile1 = p1) :
    ∃ t sB fi, executeL2 cardDB oracle 0 stateA t = some (sB, fi)
      ∧ noEndTurn t = true ∧ sameModAccum stateA sB = true ∧ dealtDamage stateA sB = true := by
  -- Extract verifyOne from the batch theorems
  have hv : verifyOne p0 p1 = true := by
    simp only [allPerms2, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hmem0
    rcases hmem0 with rfl | rfl
    · have h := verify_p0a; unfold verifyP0 at h; rw [List.all_eq_true] at h
      exact h p1 hmem1
    · have h := verify_p0b; unfold verifyP0 at h; rw [List.all_eq_true] at h
      exact h p1 hmem1
  simp only [verifyOne] at hv
  split at hv
  · next stB fIdx heq =>
    simp only [Bool.and_eq_true] at hv; obtain ⟨⟨⟨hsm, hdd⟩, hdc⟩, hne⟩ := hv
    have hf0 : oracle 0 pile0 = fixedOracle p0 p1 0 pile0 := by simp [fixedOracle]; exact h0
    have hf1 : oracle 1 pile1 = fixedOracle p0 p1 1 pile1 := by simp [fixedOracle]; exact h1
    exact ⟨_, stB, fIdx, (drawCondBool_bridge oracle _ hf0 hf1 0 stateA _ hdc) ▸ heq, hne, hsm, hdd⟩
  · simp at hv

-- ============================================================
-- MAIN THEOREM
-- ============================================================

theorem ComboStreamlineHologram_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  have hp0 := perm2_mem (oracle 0 pile0) (hValid 0 pile0)
  have hp1 := perm4_mem (oracle 1 pile1) (hValid 1 pile1)
  exact handle_loop _ _ hp0 hp1 oracle rfl rfl

end ComboStreamlineHologram_L2
