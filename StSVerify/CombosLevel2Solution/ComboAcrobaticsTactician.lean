/-
  Level 2: Acrobatics + Tactician combo (v3 engine)

  Shuffle points in the loop (v3: resolveCard in queue, no resolveInUse):
    oracle 0: [ci6]       (singleton, forced)
    oracle 1: [ci10]      (singleton, forced)
    oracle 2: [ci0, ci2]  (2 permutations)
    oracle 3: [ci1, ci3]  (2 permutations)
  Total: 2 x 2 = 4 oracle cases → 4 distinct final hand orders.
  All 4 satisfy sameModAccum and dealtDamage.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboAcrobaticsTactician_L2

-- ============================================================
-- CARD INSTANCES
-- ============================================================

private def ci0  : CardInstance := { id := 0,  name := AcrobaticsPlus,  cost := 1, damage := 0 }
private def ci1  : CardInstance := { id := 1,  name := AcrobaticsPlus,  cost := 1, damage := 0 }
private def ci2  : CardInstance := { id := 2,  name := TacticianPlus,   cost := 0, damage := 0 }
private def ci3  : CardInstance := { id := 3,  name := ReflexPlus,      cost := 0, damage := 0 }
private def ci4  : CardInstance := { id := 4,  name := BackflipPlus,    cost := 1, damage := 0 }
private def ci5  : CardInstance := { id := 5,  name := BackflipPlus,    cost := 1, damage := 0 }
private def ci6  : CardInstance := { id := 6,  name := NeutralizePlus,  cost := 0, damage := 4 }
private def ci10 : CardInstance := { id := 10, name := EscapePlanPlus,  cost := 0, damage := 0 }

-- ============================================================
-- FRAMEWORK-GENERATED
-- ============================================================

def cards : List (CardName × Nat) := [
  (AcrobaticsPlus, 2), (TacticianPlus, 1), (ReflexPlus, 1),
  (BackflipPlus, 2), (NeutralizePlus, 1), (AfterImage, 1),
  (AdrenalinePlus, 1), (CaltropPlus, 1), (EscapePlanPlus, 1),
  (GrandFinalePlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

-- ============================================================
-- SETUP
-- ============================================================

def setupTrace : List Action := [
  .draw 8, .draw 7, .draw 9, .draw 6, .draw 0,
  .play 8, .draw 11, .draw 1,
  .play 7, .play 9, .play 6,
  .play 0, .draw 2, .draw 3, .draw 4, .draw 5,
  .discard 2,
  .play 1, .draw 10, .draw 6, .draw 0, .draw 2,
  .discard 3,
  .draw 3, .draw 1,
  .failDraw,
  .play 11
]

-- ============================================================
-- STATES
-- ============================================================

private def exhaustConst : List CardInstance :=
  [ { id := 11, name := GrandFinalePlus, cost := 0, damage := 60 },
    { id := 8, name := AdrenalinePlus, cost := 0, damage := 0 } ]

def stateA : GameState := {
  hand := [ci1, ci3, ci2, ci0, ci6, ci10, ci5, ci4]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustConst
  inUse := []
  actionQueue := []
  energy := 3
  damage := 64
  block := 6
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12
  noDraw := false
  corruptionActive := false
}

-- Four possible final states depending on oracle 2 × oracle 3
def stateBxx : GameState := {
  hand := [ci3, ci1, ci2, ci0, ci10, ci6, ci5, ci4]
  drawPile := [], discardPile := [], exhaustPile := exhaustConst
  inUse := [], actionQueue := []
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

def stateBxy : GameState := {
  hand := [ci1, ci3, ci2, ci0, ci10, ci6, ci5, ci4]
  drawPile := [], discardPile := [], exhaustPile := exhaustConst
  inUse := [], actionQueue := []
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

def stateByx : GameState := {
  hand := [ci3, ci1, ci0, ci2, ci10, ci6, ci5, ci4]
  drawPile := [], discardPile := [], exhaustPile := exhaustConst
  inUse := [], actionQueue := []
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

def stateByy : GameState := {
  hand := [ci1, ci3, ci0, ci2, ci10, ci6, ci5, ci4]
  drawPile := [], discardPile := [], exhaustPile := exhaustConst
  inUse := [], actionQueue := []
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- ============================================================
-- BASIC VERIFICATION
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

theorem same_mod_xx : sameModAccum stateA stateBxx = true := by native_decide
theorem same_mod_xy : sameModAccum stateA stateBxy = true := by native_decide
theorem same_mod_yx : sameModAccum stateA stateByx = true := by native_decide
theorem same_mod_yy : sameModAccum stateA stateByy = true := by native_decide
theorem dealt_dmg_xx : dealtDamage stateA stateBxx = true := by native_decide
theorem dealt_dmg_xy : dealtDamage stateA stateBxy = true := by native_decide
theorem dealt_dmg_yx : dealtDamage stateA stateByx = true := by native_decide
theorem dealt_dmg_yy : dealtDamage stateA stateByy = true := by native_decide

-- ============================================================
-- ORACLE-ADAPTIVE LOOP TRACE
-- ============================================================

def mkLoopTrace (oracle : ShuffleOracle) : List Action :=
  let shuf2 := oracle 2 [ci0, ci2]
  let shuf3 := oracle 3 [ci1, ci3]
  match shuf2, shuf3 with
  | d2a :: d2b :: _, d3a :: d3b :: _ =>
    [ .play 6, .play 10, .draw 6,
      .play 0, .draw 10, .failDraw, .discard 2,
      .play 1,
      .draw d2a.id, .draw d2b.id, .failDraw,
      .discard 3,
      .draw d3a.id, .draw d3b.id, .failDraw ]
  | _, _ => []

private theorem noEndTurn_xx (oracle : ShuffleOracle)
    (h2 : oracle 2 [ci0, ci2] = [ci0, ci2]) (h3 : oracle 3 [ci1, ci3] = [ci1, ci3]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h2, h3]; native_decide
private theorem noEndTurn_xy (oracle : ShuffleOracle)
    (h2 : oracle 2 [ci0, ci2] = [ci0, ci2]) (h3 : oracle 3 [ci1, ci3] = [ci3, ci1]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h2, h3]; native_decide
private theorem noEndTurn_yx (oracle : ShuffleOracle)
    (h2 : oracle 2 [ci0, ci2] = [ci2, ci0]) (h3 : oracle 3 [ci1, ci3] = [ci1, ci3]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h2, h3]; native_decide
private theorem noEndTurn_yy (oracle : ShuffleOracle)
    (h2 : oracle 2 [ci0, ci2] = [ci2, ci0]) (h3 : oracle 3 [ci1, ci3] = [ci3, ci1]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h2, h3]; native_decide

-- ============================================================
-- PERMUTATION LEMMAS
-- ============================================================

private theorem perm_2_ci (l : List CardInstance) (x y : CardInstance) (hne : x ≠ y)
    (hp : List.Perm l [x, y]) :
    l = [x, y] ∨ l = [y, x] := by
  have hlen := hp.length_eq; simp at hlen
  match l, hlen with
  | [a, b], _ =>
    have hx : x ∈ [a, b] := hp.mem_iff.mpr (by simp)
    have hy : y ∈ [a, b] := hp.mem_iff.mpr (by simp)
    simp [List.mem_cons, List.mem_nil_iff] at hx hy
    have hnd : [a, b].Nodup := hp.nodup_iff.mpr (by simp [hne])
    rw [List.nodup_cons] at hnd
    simp [List.mem_cons, List.mem_nil_iff] at hnd
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> (first | simp_all | omega)

private theorem perm_one_ci (a : CardInstance) (l : List CardInstance) (hp : List.Perm l [a]) :
    l = [a] := by
  have hlen := hp.length_eq; simp at hlen
  match l, hlen with
  | [x], _ =>
    have : x ∈ [a] := hp.subset (List.mem_cons_self x [])
    simp [List.mem_cons, List.mem_nil_iff] at this; subst this; rfl

-- ============================================================
-- GENERIC STEP HELPERS
-- ============================================================

private theorem exL2_cons {oracle : ShuffleOracle} {si si' : Nat} {s s0 s' : GameState}
    {a : Action} {rest : List Action}
    (hc : autoDrain cardDB s = s0)
    (hs : stepL2 cardDB oracle si s0 a = some (s', si')) :
    executeL2 cardDB oracle si s (a :: rest) =
    executeL2 cardDB oracle si' s' rest := by
  simp only [executeL2, hc, hs]

private theorem sL2_step {oracle : ShuffleOracle} {si : Nat} {s s' : GameState} {a : Action}
    (hn1 : ∀ c, a ≠ .draw c)
    (hs : step cardDB s a = some s') :
    stepL2 cardDB oracle si s a = some (s', si) := by
  cases a with
  | draw c => exact absurd rfl (hn1 c)
  | _ => simp only [stepL2, hs]

private theorem sL2_draw {oracle : ShuffleOracle} {si si' : Nat} {s s' : GameState} {c : CId}
    (hd : drawCardL2 oracle si s c = some (s', si')) :
    stepL2 cardDB oracle si s (.draw c) = some (s', si') := by
  simp only [stepL2, hd]

-- ============================================================
-- INTERMEDIATE STATES
-- ============================================================
-- Convention: sN = autoDrained state that step N+1 sees
-- sN_raw = raw output of step N (when autoDrain is nontrivial)

-- s1_raw: raw output of play 6 on stateA
-- inUse=[ci6], aq=[.resolveCard 6]
private def s1_raw : GameState := {
  hand := [ci1, ci3, ci2, ci0, ci10, ci5, ci4]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustConst
  inUse := [ci6]
  actionQueue := [.resolveCard 6]
  energy := 3, damage := 68, block := 7, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s1: autoDrain of s1_raw (resolveCard 6 → ci6 to discard)
private def s1 : GameState := {
  hand := [ci1, ci3, ci2, ci0, ci10, ci5, ci4]
  drawPile := []
  discardPile := [ci6]
  exhaustPile := exhaustConst
  inUse := []
  actionQueue := []
  energy := 3, damage := 68, block := 7, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s2: raw output of play 10 on s1 (autoDrain = identity, .draw at front)
private def s2 : GameState := {
  hand := [ci1, ci3, ci2, ci0, ci5, ci4]
  drawPile := []
  discardPile := [ci6]
  exhaustPile := exhaustConst
  inUse := [ci10]
  actionQueue := [.draw, .resolveCard 10]
  energy := 3, damage := 68, block := 8, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s3_raw: raw output of draw 6 on s2 (shuffle [ci6] singleton)
-- draws ci6, aq=[.resolveCard 10]
private def s3_raw : GameState := {
  hand := [ci6, ci1, ci3, ci2, ci0, ci5, ci4]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustConst
  inUse := [ci10]
  actionQueue := [.resolveCard 10]
  energy := 3, damage := 68, block := 8, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s3: autoDrain of s3_raw (resolveCard 10 → ci10 to discard)
private def s3 : GameState := {
  hand := [ci6, ci1, ci3, ci2, ci0, ci5, ci4]
  drawPile := []
  discardPile := [ci10]
  exhaustPile := exhaustConst
  inUse := []
  actionQueue := []
  energy := 3, damage := 68, block := 8, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s4: raw output of play 0 on s3 (autoDrain = identity, .draw at front)
private def s4 : GameState := {
  hand := [ci6, ci1, ci3, ci2, ci5, ci4]
  drawPile := []
  discardPile := [ci10]
  exhaustPile := exhaustConst
  inUse := [ci0]
  actionQueue := [.draw, .draw, .draw, .draw, .discardChoice, .resolveCard 0]
  energy := 2, damage := 68, block := 9, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s5: raw output of draw 10 on s4 (shuffle [ci10] singleton)
-- (autoDrain = identity, .draw at front)
private def s5 : GameState := {
  hand := [ci10, ci6, ci1, ci3, ci2, ci5, ci4]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustConst
  inUse := [ci0]
  actionQueue := [.draw, .draw, .draw, .discardChoice, .resolveCard 0]
  energy := 2, damage := 68, block := 9, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s6: raw output of failDraw on s5 (drops draws, .discardChoice at front)
-- (autoDrain = identity, can't process .discardChoice)
private def s6 : GameState := {
  hand := [ci10, ci6, ci1, ci3, ci2, ci5, ci4]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustConst
  inUse := [ci0]
  actionQueue := [.discardChoice, .resolveCard 0]
  energy := 2, damage := 68, block := 9, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s7_raw: raw output of discard 2 (Tactician+, +2E) on s6
-- discardChoice consumed, aq=[.resolveCard 0], inUse=[ci0]
private def s7_raw : GameState := {
  hand := [ci10, ci6, ci1, ci3, ci5, ci4]
  drawPile := [], discardPile := [ci2]
  exhaustPile := exhaustConst, inUse := [ci0]
  actionQueue := [.resolveCard 0]
  energy := 4, damage := 68, block := 9, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s7: autoDrain of s7_raw (resolveCard 0 → ci0 to discard)
private def s7 : GameState := {
  hand := [ci10, ci6, ci1, ci3, ci5, ci4]
  drawPile := []
  discardPile := [ci0, ci2]
  exhaustPile := exhaustConst
  inUse := []
  actionQueue := []
  energy := 4, damage := 68, block := 9, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s8: raw output of play 1 on s7 (autoDrain = identity, .draw at front)
private def s8 : GameState := {
  hand := [ci10, ci6, ci3, ci5, ci4]
  drawPile := []
  discardPile := [ci0, ci2]
  exhaustPile := exhaustConst
  inUse := [ci1]
  actionQueue := [.draw, .draw, .draw, .draw, .discardChoice, .resolveCard 1]
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- ============================================================
-- ORACLE-DEPENDENT STATES (oracle 2 branches: x/y)
-- ============================================================

-- After draw d2a (oracle 2 shuffle of [ci0, ci2])
private def s9x : GameState := { s8 with
  hand := [ci0, ci10, ci6, ci3, ci5, ci4], drawPile := [ci2], discardPile := []
  actionQueue := [.draw, .draw, .draw, .discardChoice, .resolveCard 1] }
private def s9y : GameState := { s8 with
  hand := [ci2, ci10, ci6, ci3, ci5, ci4], drawPile := [ci0], discardPile := []
  actionQueue := [.draw, .draw, .draw, .discardChoice, .resolveCard 1] }

-- After draw d2b (from drawPile, no shuffle)
private def s10x : GameState := { s9x with
  hand := [ci2, ci0, ci10, ci6, ci3, ci5, ci4], drawPile := []
  actionQueue := [.draw, .draw, .discardChoice, .resolveCard 1] }
private def s10y : GameState := { s9y with
  hand := [ci0, ci2, ci10, ci6, ci3, ci5, ci4], drawPile := []
  actionQueue := [.draw, .draw, .discardChoice, .resolveCard 1] }

-- After failDraw → drops 2 draws
private def s11x : GameState := { s10x with actionQueue := [.discardChoice, .resolveCard 1] }
private def s11y : GameState := { s10y with actionQueue := [.discardChoice, .resolveCard 1] }

-- s12_raw: raw output of discard 3 (Reflex+, drawCards 3, bottom priority)
-- discardChoice consumed → aq=[.resolveCard 1] → Reflex adds draws at bottom
-- aq=[.resolveCard 1, .draw, .draw, .draw]
private def s12x_raw : GameState := {
  hand := [ci2, ci0, ci10, ci6, ci5, ci4]
  drawPile := [], discardPile := [ci3]
  exhaustPile := exhaustConst, inUse := [ci1]
  actionQueue := [.resolveCard 1, .draw, .draw, .draw]
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}
private def s12y_raw : GameState := {
  hand := [ci0, ci2, ci10, ci6, ci5, ci4]
  drawPile := [], discardPile := [ci3]
  exhaustPile := exhaustConst, inUse := [ci1]
  actionQueue := [.resolveCard 1, .draw, .draw, .draw]
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- s12: autoDrain of s12_raw (resolveCard 1 → ci1 to discard, then stops at .draw)
private def s12x : GameState := {
  hand := [ci2, ci0, ci10, ci6, ci5, ci4]
  drawPile := [], discardPile := [ci1, ci3]
  exhaustPile := exhaustConst, inUse := []
  actionQueue := [.draw, .draw, .draw]
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}
private def s12y : GameState := {
  hand := [ci0, ci2, ci10, ci6, ci5, ci4]
  drawPile := [], discardPile := [ci1, ci3]
  exhaustPile := exhaustConst, inUse := []
  actionQueue := [.draw, .draw, .draw]
  energy := 3, damage := 68, block := 10, stance := .Neutral
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 4, intending := false }
  activePowers := [CaltropPlus, AfterImage]
  nextId := 12, noDraw := false, corruptionActive := false
}

-- ============================================================
-- ORACLE 3 STATES (p/q on top of x/y)
-- ============================================================

-- After draw d3a (oracle 3 shuffle of [ci1, ci3])
private def s13xp : GameState := { s12x with
  hand := [ci1, ci2, ci0, ci10, ci6, ci5, ci4], drawPile := [ci3], discardPile := []
  actionQueue := [.draw, .draw] }
private def s13xq : GameState := { s12x with
  hand := [ci3, ci2, ci0, ci10, ci6, ci5, ci4], drawPile := [ci1], discardPile := []
  actionQueue := [.draw, .draw] }
private def s13yp : GameState := { s12y with
  hand := [ci1, ci0, ci2, ci10, ci6, ci5, ci4], drawPile := [ci3], discardPile := []
  actionQueue := [.draw, .draw] }
private def s13yq : GameState := { s12y with
  hand := [ci3, ci0, ci2, ci10, ci6, ci5, ci4], drawPile := [ci1], discardPile := []
  actionQueue := [.draw, .draw] }

-- After draw d3b (from drawPile, no shuffle)
private def s14xp : GameState := { s13xp with
  hand := [ci3, ci1, ci2, ci0, ci10, ci6, ci5, ci4], drawPile := []
  actionQueue := [.draw] }
private def s14xq : GameState := { s13xq with
  hand := [ci1, ci3, ci2, ci0, ci10, ci6, ci5, ci4], drawPile := []
  actionQueue := [.draw] }
private def s14yp : GameState := { s13yp with
  hand := [ci3, ci1, ci0, ci2, ci10, ci6, ci5, ci4], drawPile := []
  actionQueue := [.draw] }
private def s14yq : GameState := { s13yq with
  hand := [ci1, ci3, ci0, ci2, ci10, ci6, ci5, ci4], drawPile := []
  actionQueue := [.draw] }

-- After failDraw → aq=[]
private def s15xx : GameState := { s14xp with actionQueue := [] }
private def s15xy : GameState := { s14xq with actionQueue := [] }
private def s15yx : GameState := { s14yp with actionQueue := [] }
private def s15yy : GameState := { s14yq with actionQueue := [] }

-- ============================================================
-- L1 STEP THEOREMS
-- ============================================================

theorem hs1 : step cardDB stateA (.play 6) = some s1_raw := by native_decide
theorem hc1 : autoDrain cardDB s1_raw = s1 := by native_decide
theorem hs2 : step cardDB s1 (.play 10) = some s2 := by native_decide
theorem hc2 : autoDrain cardDB s2 = s2 := by native_decide
theorem hs4 : step cardDB s3 (.play 0) = some s4 := by native_decide
theorem hc4 : autoDrain cardDB s4 = s4 := by native_decide
theorem hs6 : step cardDB s5 .failDraw = some s6 := by native_decide
theorem hc6 : autoDrain cardDB s6 = s6 := by native_decide
theorem hs7 : step cardDB s6 (.discard 2) = some s7_raw := by native_decide
theorem hc7 : autoDrain cardDB s7_raw = s7 := by native_decide
theorem hs8 : step cardDB s7 (.play 1) = some s8 := by native_decide
theorem hc8 : autoDrain cardDB s8 = s8 := by native_decide

-- Oracle-dependent steps
theorem hs11x : step cardDB s10x .failDraw = some s11x := by native_decide
theorem hs11y : step cardDB s10y .failDraw = some s11y := by native_decide
theorem hs12x : step cardDB s11x (.discard 3) = some s12x_raw := by native_decide
theorem hc12x : autoDrain cardDB s12x_raw = s12x := by native_decide
theorem hs12y : step cardDB s11y (.discard 3) = some s12y_raw := by native_decide
theorem hc12y : autoDrain cardDB s12y_raw = s12y := by native_decide
theorem hs15xp : step cardDB s14xp .failDraw = some s15xx := by native_decide
theorem hs15xq : step cardDB s14xq .failDraw = some s15xy := by native_decide
theorem hs15yp : step cardDB s14yp .failDraw = some s15yx := by native_decide
theorem hs15yq : step cardDB s14yq .failDraw = some s15yy := by native_decide

-- ============================================================
-- CLEANUP (autoDrain = identity) LEMMAS
-- ============================================================

theorem hc_stateA : autoDrain cardDB stateA = stateA := by native_decide
theorem hc3 : autoDrain cardDB s3_raw = s3 := by native_decide
theorem hc5 : autoDrain cardDB s5 = s5 := by native_decide
theorem hc9x : autoDrain cardDB s9x = s9x := by native_decide
theorem hc9y : autoDrain cardDB s9y = s9y := by native_decide
theorem hc10x : autoDrain cardDB s10x = s10x := by native_decide
theorem hc10y : autoDrain cardDB s10y = s10y := by native_decide
theorem hc11x : autoDrain cardDB s11x = s11x := by native_decide
theorem hc11y : autoDrain cardDB s11y = s11y := by native_decide
theorem hc13xp : autoDrain cardDB s13xp = s13xp := by native_decide
theorem hc13xq : autoDrain cardDB s13xq = s13xq := by native_decide
theorem hc13yp : autoDrain cardDB s13yp = s13yp := by native_decide
theorem hc13yq : autoDrain cardDB s13yq = s13yq := by native_decide
theorem hc14xp : autoDrain cardDB s14xp = s14xp := by native_decide
theorem hc14xq : autoDrain cardDB s14xq = s14xq := by native_decide
theorem hc14yp : autoDrain cardDB s14yp = s14yp := by native_decide
theorem hc14yq : autoDrain cardDB s14yq = s14yq := by native_decide
theorem hc15xx : autoDrain cardDB s15xx = stateBxx := by native_decide
theorem hc15xy : autoDrain cardDB s15xy = stateBxy := by native_decide
theorem hc15yx : autoDrain cardDB s15yx = stateByx := by native_decide
theorem hc15yy : autoDrain cardDB s15yy = stateByy := by native_decide

-- ============================================================
-- ORACLE-DEPENDENT DRAW THEOREMS
-- ============================================================

-- Shuffle 0: singleton [ci6] from s2 (disc=[ci6])
theorem hd3 (oracle : ShuffleOracle) (hv : validOracle oracle) :
    drawCardL2 oracle 0 s2 6 = some (s3_raw, 1) := by
  have hp := perm_one_ci ci6 _ (hv 0 [ci6])
  unfold drawCardL2; simp only [s2, ci6] at hp ⊢; rw [hp]; native_decide

-- Shuffle 1: singleton [ci10] from s4 (disc=[ci10])
theorem hd5 (oracle : ShuffleOracle) (hv : validOracle oracle) :
    drawCardL2 oracle 1 s4 10 = some (s5, 2) := by
  have hp := perm_one_ci ci10 _ (hv 1 [ci10])
  unfold drawCardL2; simp only [s4, ci10] at hp ⊢; rw [hp]; native_decide

-- Shuffle 2: [ci0, ci2] from s8 (disc=[ci0, ci2])
theorem hd9x (oracle : ShuffleOracle) (h : oracle 2 [ci0, ci2] = [ci0, ci2]) :
    drawCardL2 oracle 2 s8 0 = some (s9x, 3) := by
  unfold drawCardL2; simp only [s8, ci0, ci2] at h ⊢; rw [h]; native_decide

theorem hd9y (oracle : ShuffleOracle) (h : oracle 2 [ci0, ci2] = [ci2, ci0]) :
    drawCardL2 oracle 2 s8 2 = some (s9y, 3) := by
  unfold drawCardL2; simp only [s8, ci0, ci2] at h ⊢; rw [h]; native_decide

-- Draw d2b (from drawPile, no shuffle)
theorem hd10x (oracle : ShuffleOracle) :
    drawCardL2 oracle 3 s9x 2 = some (s10x, 3) := rfl
theorem hd10y (oracle : ShuffleOracle) :
    drawCardL2 oracle 3 s9y 0 = some (s10y, 3) := rfl

-- Shuffle 3: [ci1, ci3] from s12x/s12y (disc=[ci1, ci3])
theorem hd13xp (oracle : ShuffleOracle) (h : oracle 3 [ci1, ci3] = [ci1, ci3]) :
    drawCardL2 oracle 3 s12x 1 = some (s13xp, 4) := by
  unfold drawCardL2; simp only [s12x, ci1, ci3] at h ⊢; rw [h]; native_decide

theorem hd13xq (oracle : ShuffleOracle) (h : oracle 3 [ci1, ci3] = [ci3, ci1]) :
    drawCardL2 oracle 3 s12x 3 = some (s13xq, 4) := by
  unfold drawCardL2; simp only [s12x, ci1, ci3] at h ⊢; rw [h]; native_decide

theorem hd13yp (oracle : ShuffleOracle) (h : oracle 3 [ci1, ci3] = [ci1, ci3]) :
    drawCardL2 oracle 3 s12y 1 = some (s13yp, 4) := by
  unfold drawCardL2; simp only [s12y, ci1, ci3] at h ⊢; rw [h]; native_decide

theorem hd13yq (oracle : ShuffleOracle) (h : oracle 3 [ci1, ci3] = [ci3, ci1]) :
    drawCardL2 oracle 3 s12y 3 = some (s13yq, 4) := by
  unfold drawCardL2; simp only [s12y, ci1, ci3] at h ⊢; rw [h]; native_decide

-- Draw d3b (from drawPile, no shuffle)
theorem hd14xp (oracle : ShuffleOracle) :
    drawCardL2 oracle 4 s13xp 3 = some (s14xp, 4) := rfl
theorem hd14xq (oracle : ShuffleOracle) :
    drawCardL2 oracle 4 s13xq 1 = some (s14xq, 4) := rfl
theorem hd14yp (oracle : ShuffleOracle) :
    drawCardL2 oracle 4 s13yp 3 = some (s14yp, 4) := rfl
theorem hd14yq (oracle : ShuffleOracle) :
    drawCardL2 oracle 4 s13yq 1 = some (s14yq, 4) := rfl

-- ============================================================
-- PER-CASE LOOP PROOFS
-- ============================================================

private theorem loop_xx (oracle : ShuffleOracle) (hv : validOracle oracle)
    (h2 : oracle 2 [ci0, ci2] = [ci0, ci2]) (h3 : oracle 3 [ci1, ci3] = [ci1, ci3]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateBxx, 4) := by
  have htrace : mkLoopTrace oracle = [.play 6, .play 10, .draw 6,
      .play 0, .draw 10, .failDraw, .discard 2,
      .play 1,
      .draw 0, .draw 2, .failDraw,
      .discard 3,
      .draw 1, .draw 3, .failDraw] := by
    unfold mkLoopTrace; rw [h2, h3]; simp [ci0, ci1, ci2, ci3]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_draw (hd3 oracle hv))]
  rw [exL2_cons hc3 (sL2_step (by intro c; simp) hs4)]
  rw [exL2_cons hc4 (sL2_draw (hd5 oracle hv))]
  rw [exL2_cons hc5 (sL2_step (by intro c; simp) hs6)]
  rw [exL2_cons hc6 (sL2_step (by intro c; simp) hs7)]
  rw [exL2_cons hc7 (sL2_step (by intro c; simp) hs8)]
  rw [exL2_cons hc8 (sL2_draw (hd9x oracle h2))]
  rw [exL2_cons hc9x (sL2_draw (hd10x oracle))]
  rw [exL2_cons hc10x (sL2_step (by intro c; simp) hs11x)]
  rw [exL2_cons hc11x (sL2_step (by intro c; simp) hs12x)]
  rw [exL2_cons hc12x (sL2_draw (hd13xp oracle h3))]
  rw [exL2_cons hc13xp (sL2_draw (hd14xp oracle))]
  rw [exL2_cons hc14xp (sL2_step (by intro c; simp) hs15xp)]
  simp only [executeL2, hc15xx]

private theorem loop_xy (oracle : ShuffleOracle) (hv : validOracle oracle)
    (h2 : oracle 2 [ci0, ci2] = [ci0, ci2]) (h3 : oracle 3 [ci1, ci3] = [ci3, ci1]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateBxy, 4) := by
  have htrace : mkLoopTrace oracle = [.play 6, .play 10, .draw 6,
      .play 0, .draw 10, .failDraw, .discard 2,
      .play 1,
      .draw 0, .draw 2, .failDraw,
      .discard 3,
      .draw 3, .draw 1, .failDraw] := by
    unfold mkLoopTrace; rw [h2, h3]; simp [ci0, ci1, ci2, ci3]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_draw (hd3 oracle hv))]
  rw [exL2_cons hc3 (sL2_step (by intro c; simp) hs4)]
  rw [exL2_cons hc4 (sL2_draw (hd5 oracle hv))]
  rw [exL2_cons hc5 (sL2_step (by intro c; simp) hs6)]
  rw [exL2_cons hc6 (sL2_step (by intro c; simp) hs7)]
  rw [exL2_cons hc7 (sL2_step (by intro c; simp) hs8)]
  rw [exL2_cons hc8 (sL2_draw (hd9x oracle h2))]
  rw [exL2_cons hc9x (sL2_draw (hd10x oracle))]
  rw [exL2_cons hc10x (sL2_step (by intro c; simp) hs11x)]
  rw [exL2_cons hc11x (sL2_step (by intro c; simp) hs12x)]
  rw [exL2_cons hc12x (sL2_draw (hd13xq oracle h3))]
  rw [exL2_cons hc13xq (sL2_draw (hd14xq oracle))]
  rw [exL2_cons hc14xq (sL2_step (by intro c; simp) hs15xq)]
  simp only [executeL2, hc15xy]

private theorem loop_yx (oracle : ShuffleOracle) (hv : validOracle oracle)
    (h2 : oracle 2 [ci0, ci2] = [ci2, ci0]) (h3 : oracle 3 [ci1, ci3] = [ci1, ci3]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateByx, 4) := by
  have htrace : mkLoopTrace oracle = [.play 6, .play 10, .draw 6,
      .play 0, .draw 10, .failDraw, .discard 2,
      .play 1,
      .draw 2, .draw 0, .failDraw,
      .discard 3,
      .draw 1, .draw 3, .failDraw] := by
    unfold mkLoopTrace; rw [h2, h3]; simp [ci0, ci1, ci2, ci3]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_draw (hd3 oracle hv))]
  rw [exL2_cons hc3 (sL2_step (by intro c; simp) hs4)]
  rw [exL2_cons hc4 (sL2_draw (hd5 oracle hv))]
  rw [exL2_cons hc5 (sL2_step (by intro c; simp) hs6)]
  rw [exL2_cons hc6 (sL2_step (by intro c; simp) hs7)]
  rw [exL2_cons hc7 (sL2_step (by intro c; simp) hs8)]
  rw [exL2_cons hc8 (sL2_draw (hd9y oracle h2))]
  rw [exL2_cons hc9y (sL2_draw (hd10y oracle))]
  rw [exL2_cons hc10y (sL2_step (by intro c; simp) hs11y)]
  rw [exL2_cons hc11y (sL2_step (by intro c; simp) hs12y)]
  rw [exL2_cons hc12y (sL2_draw (hd13yp oracle h3))]
  rw [exL2_cons hc13yp (sL2_draw (hd14yp oracle))]
  rw [exL2_cons hc14yp (sL2_step (by intro c; simp) hs15yp)]
  simp only [executeL2, hc15yx]

private theorem loop_yy (oracle : ShuffleOracle) (hv : validOracle oracle)
    (h2 : oracle 2 [ci0, ci2] = [ci2, ci0]) (h3 : oracle 3 [ci1, ci3] = [ci3, ci1]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateByy, 4) := by
  have htrace : mkLoopTrace oracle = [.play 6, .play 10, .draw 6,
      .play 0, .draw 10, .failDraw, .discard 2,
      .play 1,
      .draw 2, .draw 0, .failDraw,
      .discard 3,
      .draw 3, .draw 1, .failDraw] := by
    unfold mkLoopTrace; rw [h2, h3]; simp [ci0, ci1, ci2, ci3]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_draw (hd3 oracle hv))]
  rw [exL2_cons hc3 (sL2_step (by intro c; simp) hs4)]
  rw [exL2_cons hc4 (sL2_draw (hd5 oracle hv))]
  rw [exL2_cons hc5 (sL2_step (by intro c; simp) hs6)]
  rw [exL2_cons hc6 (sL2_step (by intro c; simp) hs7)]
  rw [exL2_cons hc7 (sL2_step (by intro c; simp) hs8)]
  rw [exL2_cons hc8 (sL2_draw (hd9y oracle h2))]
  rw [exL2_cons hc9y (sL2_draw (hd10y oracle))]
  rw [exL2_cons hc10y (sL2_step (by intro c; simp) hs11y)]
  rw [exL2_cons hc11y (sL2_step (by intro c; simp) hs12y)]
  rw [exL2_cons hc12y (sL2_draw (hd13yq oracle h3))]
  rw [exL2_cons hc13yq (sL2_draw (hd14yq oracle))]
  rw [exL2_cons hc14yq (sL2_step (by intro c; simp) hs15yq)]
  simp only [executeL2, hc15yy]

-- ============================================================
-- MAIN THEOREM
-- ============================================================

theorem ComboAcrobaticsTactician_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hvalid
  have hp2 := hvalid 2 [ci0, ci2]
  have hp3 := hvalid 3 [ci1, ci3]
  have h02 := perm_2_ci (oracle 2 [ci0, ci2]) ci0 ci2 (by decide) hp2
  have h13 := perm_2_ci (oracle 3 [ci1, ci3]) ci1 ci3 (by decide) hp3
  rcases h02 with h2 | h2 <;> rcases h13 with h3 | h3
  · exact ⟨mkLoopTrace oracle, stateBxx, 4,
      loop_xx oracle hvalid h2 h3, noEndTurn_xx oracle h2 h3, same_mod_xx, dealt_dmg_xx⟩
  · exact ⟨mkLoopTrace oracle, stateBxy, 4,
      loop_xy oracle hvalid h2 h3, noEndTurn_xy oracle h2 h3, same_mod_xy, dealt_dmg_xy⟩
  · exact ⟨mkLoopTrace oracle, stateByx, 4,
      loop_yx oracle hvalid h2 h3, noEndTurn_yx oracle h2 h3, same_mod_yx, dealt_dmg_yx⟩
  · exact ⟨mkLoopTrace oracle, stateByy, 4,
      loop_yy oracle hvalid h2 h3, noEndTurn_yy oracle h2 h3, same_mod_yy, dealt_dmg_yy⟩

end ComboAcrobaticsTactician_L2
