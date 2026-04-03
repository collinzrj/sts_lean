/-
  観者 - 標準沙雕無限 (Level 2)
  v2 engine: CardInstance piles, sameModAccum(stateA, stateB),
  execute cardDB, ShuffleOracle on List CardInstance.

  Two 2-element shuffle points → 4 oracle cases total.
  The trace adapts draw order to oracle's top-of-pile.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboStandardWatcher_L2

-- ============================================================
-- CARD INSTANCES
-- ============================================================

private def ci3  : CardInstance := { id := 3,  name := EruptionPlus,       cost := 1, damage := 9 }
private def ci4  : CardInstance := { id := 4,  name := TantrumPlus,        cost := 1, damage := 12 }
private def ci5  : CardInstance := { id := 5,  name := InnerPeacePlus,     cost := 1, damage := 0 }
private def ci6  : CardInstance := { id := 6,  name := FearNoEvilPlus,     cost := 1, damage := 11 }
private def ci7  : CardInstance := { id := 7,  name := FlurryOfBlowsPlus,  cost := 0, damage := 6 }

-- ============================================================
-- FRAMEWORK-GENERATED
-- ============================================================

def cards : List (CardName × Nat) :=
  [ (Rushdown, 2), (MentalFortressPlus, 1), (EruptionPlus, 1),
    (TantrumPlus, 1), (InnerPeacePlus, 1), (FearNoEvilPlus, 1),
    (FlurryOfBlowsPlus, 1), (Scrawl, 1), (VaultPlus, 1),
    (DeusExMachina, 1), (TalkToTheHandPlus, 1) ]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := true }

-- ============================================================
-- SETUP TRACE
-- ============================================================

def setupTrace : List Action := [
  .draw 10, .draw 0, .draw 1, .draw 2, .draw 5,
  .resolveDrawTrigger 10,
  .play 0, .play 1, .play 2,
  .play 12, .play 13,
  .play 5,
  .endTurn,
  .draw 4, .draw 6, .draw 11, .draw 9, .draw 8,
  .play 4,
  .resolveRushdown,
  .draw 3, .draw 7, .draw 4, .draw 5,
  .play 11, .play 9, .play 8,
  .failDraw,
  .endTurn,
  .draw 4, .draw 6, .draw 3, .draw 7, .draw 5,
  .play 6, .play 3,
  .resolveRushdown,
  .draw 6, .draw 3,
  .failDraw,
  .play 7, .play 5,
  .autoPlayFlurry 7
]

-- ============================================================
-- STATES
-- ============================================================

private def exhaustPileConst : List CardInstance :=
  [ { id := 8,  name := Scrawl,             cost := 1, damage := 0 },
    { id := 9,  name := VaultPlus,           cost := 2, damage := 0 },
    { id := 11, name := TalkToTheHandPlus,   cost := 1, damage := 7 },
    { id := 13, name := Miracle,             cost := 0, damage := 0 },
    { id := 12, name := Miracle,             cost := 0, damage := 0 },
    { id := 10, name := DeusExMachina,       cost := 0, damage := 0 } ]

def stateA : GameState := {
  hand := [ci3, ci6, ci4]
  drawPile := []
  discardPile := [ci5, ci7]
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := []
  energy := 2
  damage := 75
  block := 18
  stance := .Calm
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14
  noDraw := false
  corruptionActive := false
}

-- Two possible final states depending on 2nd shuffle (hand order differs)
-- oracle 1 [ci3,ci6] = [ci3,ci6]: draws ci3 first → hand = [ci6,ci3,ci4]
def stateBx : GameState := {
  hand := [ci6, ci3, ci4]
  drawPile := []
  discardPile := [ci5, ci7]
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := []
  energy := 2
  damage := 148
  block := 42
  stance := .Calm
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14
  noDraw := false
  corruptionActive := false
}

-- oracle 1 [ci3,ci6] = [ci6,ci3]: draws ci6 first → hand = [ci3,ci6,ci4]
def stateBy : GameState := {
  hand := [ci3, ci6, ci4]
  drawPile := []
  discardPile := [ci5, ci7]
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := []
  energy := 2
  damage := 148
  block := 42
  stance := .Calm
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14
  noDraw := false
  corruptionActive := false
}

-- ============================================================
-- BASIC VERIFICATION
-- ============================================================

theorem setup_ok :
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by
  native_decide

theorem same_mod_x : sameModAccum stateA stateBx = true := by native_decide
theorem same_mod_y : sameModAccum stateA stateBy = true := by native_decide
theorem dealt_dmg_x : dealtDamage stateA stateBx = true := by native_decide
theorem dealt_dmg_y : dealtDamage stateA stateBy = true := by native_decide

-- ============================================================
-- ORACLE-ADAPTIVE LOOP TRACE
-- ============================================================

def mkLoopTrace (oracle : ShuffleOracle) : List Action :=
  let shuf1 := oracle 0 [ci5, ci7]
  let shuf2 := oracle 1 [ci3, ci6]
  match shuf1, shuf2 with
  | d1a :: d1b :: _, d2a :: d2b :: _ =>
    [ .play 4, .resolveRushdown, .autoPlayFlurry 7,
      .draw 4, .draw d1a.id, .draw d1b.id, .failDraw,
      .play 6, .play 3, .resolveRushdown,
      .draw d2a.id, .draw d2b.id, .failDraw,
      .play 7, .play 5, .autoPlayFlurry 7 ]
  | _, _ => []

private theorem noEndTurn_a1 (oracle : ShuffleOracle)
    (h1 : oracle 0 [ci5, ci7] = [ci5, ci7]) (h2 : oracle 1 [ci3, ci6] = [ci3, ci6]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h1, h2]; native_decide
private theorem noEndTurn_a2 (oracle : ShuffleOracle)
    (h1 : oracle 0 [ci5, ci7] = [ci5, ci7]) (h2 : oracle 1 [ci3, ci6] = [ci6, ci3]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h1, h2]; native_decide
private theorem noEndTurn_b1 (oracle : ShuffleOracle)
    (h1 : oracle 0 [ci5, ci7] = [ci7, ci5]) (h2 : oracle 1 [ci3, ci6] = [ci3, ci6]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h1, h2]; native_decide
private theorem noEndTurn_b2 (oracle : ShuffleOracle)
    (h1 : oracle 0 [ci5, ci7] = [ci7, ci5]) (h2 : oracle 1 [ci3, ci6] = [ci6, ci3]) :
    noEndTurn (mkLoopTrace oracle) = true := by
  unfold mkLoopTrace; rw [h1, h2]; native_decide

-- ============================================================
-- PERMUTATION ENUMERATION (2-element, CardInstance)
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

-- After play c4 (Tantrum+): shuffles self into draw (resolveCard in queue)
private def s1 : GameState := {
  hand := [ci3, ci6]
  drawPile := []
  discardPile := [ci5, ci7]
  exhaustPile := exhaustPileConst
  inUse := [ci4]
  actionQueue := [.resolveCard 4]
  energy := 3
  damage := 87
  block := 24
  stance := .Wrath
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14
  noDraw := false
  corruptionActive := false
}

-- resolveInUse: Tantrum+ has shuffleSelf → goes to drawPile
private def s1r : GameState := {
  hand := [ci3, ci6]
  drawPile := [ci4]
  discardPile := [ci5, ci7]
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := []
  energy := 3
  damage := 87
  block := 24
  stance := .Wrath
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14
  noDraw := false
  corruptionActive := false
}

-- After resolveRushdown: +4 draws
private def s2 : GameState := { s1r with actionQueue := [.draw, .draw, .draw, .draw] }

-- After autoPlayFlurry c7: +12 dmg (6*2 Wrath) → 87+12=99
private def s3 : GameState := { s2 with damage := 99 }

-- After draw c4 from drawPile=[c4] (no shuffle): hand=[c4,c3,c6], draw=[], aq=[.draw,.draw,.draw]
private def s4 : GameState := {
  hand := [ci4, ci3, ci6]
  drawPile := []
  discardPile := [ci5, ci7]
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := [.draw, .draw, .draw]
  energy := 3
  damage := 99
  block := 24
  stance := .Wrath
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14
  noDraw := false
  corruptionActive := false
}

-- Shuffle 1: [ci5,ci7] → path a (ci5 first) or path b (ci7 first)
-- After draw first from shuffle:
private def s5a : GameState := { -- draw ci5
  hand := [ci5, ci4, ci3, ci6]
  drawPile := [ci7]
  discardPile := []
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := [.draw, .draw]
  energy := 3, damage := 99, block := 24, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}
private def s5b : GameState := { -- draw ci7
  hand := [ci7, ci4, ci3, ci6]
  drawPile := [ci5]
  discardPile := []
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := [.draw, .draw]
  energy := 3, damage := 99, block := 24, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}

-- After draw second (no shuffle):
private def s6a : GameState := { -- draw ci7 from [ci7]
  hand := [ci7, ci5, ci4, ci3, ci6]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := [.draw]
  energy := 3, damage := 99, block := 24, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}
private def s6b : GameState := { -- draw ci5 from [ci5]
  hand := [ci5, ci7, ci4, ci3, ci6]
  drawPile := []
  discardPile := []
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := [.draw]
  energy := 3, damage := 99, block := 24, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}

-- After failDraw: drop leading draws → aq=[]
private def s7a : GameState := { s6a with actionQueue := [] }
private def s7b : GameState := { s6b with actionQueue := [] }

-- After play c6 (FearNoEvil+): Wrath→Calm, +2E, 11 dmg (in Wrath = 22), +6 block
-- card in inUse, resolves to discard
private def s8a : GameState := {
  hand := [ci7, ci5, ci4, ci3]
  drawPile := []
  discardPile := [ci6]
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := []
  energy := 2
  damage := 121
  block := 30
  stance := .Calm
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}
private def s8b : GameState := {
  hand := [ci5, ci7, ci4, ci3]
  drawPile := []
  discardPile := [ci6]
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := []
  energy := 2
  damage := 121
  block := 30
  stance := .Calm
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}

-- After play c3 (Eruption+): Calm→Wrath, 9 dmg (Calm, no mult), +2E, +6 block
-- card in inUse, resolves to discard
private def s9a : GameState := {
  hand := [ci7, ci5, ci4]
  drawPile := []
  discardPile := [ci3, ci6]
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := []
  energy := 3
  damage := 130
  block := 36
  stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}
private def s9b : GameState := {
  hand := [ci5, ci7, ci4]
  drawPile := []
  discardPile := [ci3, ci6]
  exhaustPile := exhaustPileConst
  inUse := []
  actionQueue := []
  energy := 3
  damage := 130
  block := 36
  stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}

-- After resolveRushdown: +4 draws
private def s10a : GameState := { s9a with actionQueue := [.draw, .draw, .draw, .draw] }
private def s10b : GameState := { s9b with actionQueue := [.draw, .draw, .draw, .draw] }

-- Shuffle 2: disc=[ci3,ci6]
-- Path a1: a + [ci3,ci6] → draw ci3 first
private def s11a1 : GameState := {
  hand := [ci3, ci7, ci5, ci4], drawPile := [ci6], discardPile := []
  exhaustPile := exhaustPileConst, inUse := []
  actionQueue := [.draw, .draw, .draw]
  energy := 3, damage := 130, block := 36, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}
private def s12a1 : GameState := {
  hand := [ci6, ci3, ci7, ci5, ci4], drawPile := [], discardPile := []
  exhaustPile := exhaustPileConst, inUse := []
  actionQueue := [.draw, .draw]
  energy := 3, damage := 130, block := 36, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}

-- Path a2: a + [ci6,ci3] → draw ci6 first
private def s11a2 : GameState := {
  hand := [ci6, ci7, ci5, ci4], drawPile := [ci3], discardPile := []
  exhaustPile := exhaustPileConst, inUse := []
  actionQueue := [.draw, .draw, .draw]
  energy := 3, damage := 130, block := 36, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}
private def s12a2 : GameState := {
  hand := [ci3, ci6, ci7, ci5, ci4], drawPile := [], discardPile := []
  exhaustPile := exhaustPileConst, inUse := []
  actionQueue := [.draw, .draw]
  energy := 3, damage := 130, block := 36, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}

-- Path b1: b + [ci3,ci6] → draw ci3 first
private def s11b1 : GameState := {
  hand := [ci3, ci5, ci7, ci4], drawPile := [ci6], discardPile := []
  exhaustPile := exhaustPileConst, inUse := []
  actionQueue := [.draw, .draw, .draw]
  energy := 3, damage := 130, block := 36, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}
private def s12b1 : GameState := {
  hand := [ci6, ci3, ci5, ci7, ci4], drawPile := [], discardPile := []
  exhaustPile := exhaustPileConst, inUse := []
  actionQueue := [.draw, .draw]
  energy := 3, damage := 130, block := 36, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}

-- Path b2: b + [ci6,ci3] → draw ci6 first
private def s11b2 : GameState := {
  hand := [ci6, ci5, ci7, ci4], drawPile := [ci3], discardPile := []
  exhaustPile := exhaustPileConst, inUse := []
  actionQueue := [.draw, .draw, .draw]
  energy := 3, damage := 130, block := 36, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}
private def s12b2 : GameState := {
  hand := [ci3, ci6, ci5, ci7, ci4], drawPile := [], discardPile := []
  exhaustPile := exhaustPileConst, inUse := []
  actionQueue := [.draw, .draw]
  energy := 3, damage := 130, block := 36, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}

-- failDraw states
private def s13a1 : GameState := { s12a1 with actionQueue := [] }
private def s13a2 : GameState := { s12a2 with actionQueue := [] }
private def s13b1 : GameState := { s12b1 with actionQueue := [] }
private def s13b2 : GameState := { s12b2 with actionQueue := [] }

-- After play c7 (Flurry): dmg += 12 (6*2 Wrath)
-- After play c5 (InnerPeace+): Wrath→Calm +6blk, E-1
-- After autoPlayFlurry c7: dmg += 6 (Calm)
-- Only the 2nd shuffle order matters for final hand order

-- ============================================================
-- L1 STEP THEOREMS
-- ============================================================

-- Steps 1-3: play c4, resolveRushdown, autoPlayFlurry c7

-- play c4 (Tantrum+)
theorem hs1 : step cardDB stateA (.play 4) = some s1 := by native_decide
theorem hc1 : autoDrain cardDB s1 = s1r := by native_decide

theorem hs2 : step cardDB s1r .resolveRushdown = some s2 := by native_decide
theorem hc2 : autoDrain cardDB s2 = s2 := by native_decide

theorem hs3 : step cardDB s2 (.autoPlayFlurry 7) = some s3 := by native_decide
theorem hc3 : autoDrain cardDB s3 = s3 := by native_decide

-- draw c4 from drawPile=[c4] (no shuffle, oracle-independent)
theorem hd4 (oracle : ShuffleOracle) :
    drawCardL2 oracle 0 s3 4 = some (s4, 0) := rfl

theorem hc4 : autoDrain cardDB s4 = s4 := by native_decide

-- Shuffle 1 draws
theorem hd5a (oracle : ShuffleOracle) (h : oracle 0 [ci5, ci7] = [ci5, ci7]) :
    drawCardL2 oracle 0 s4 5 = some (s5a, 1) := by
  unfold drawCardL2; simp only [s4, ci5, ci7] at h ⊢; rw [h]; native_decide

theorem hd5b (oracle : ShuffleOracle) (h : oracle 0 [ci5, ci7] = [ci7, ci5]) :
    drawCardL2 oracle 0 s4 7 = some (s5b, 1) := by
  unfold drawCardL2; simp only [s4, ci5, ci7] at h ⊢; rw [h]; native_decide

theorem hd6a (oracle : ShuffleOracle) :
    drawCardL2 oracle 1 s5a 7 = some (s6a, 1) := rfl

theorem hd6b (oracle : ShuffleOracle) :
    drawCardL2 oracle 1 s5b 5 = some (s6b, 1) := rfl

theorem hc_stateA : autoDrain cardDB stateA = stateA := by native_decide
theorem hc5a : autoDrain cardDB s5a = s5a := by native_decide
theorem hc5b : autoDrain cardDB s5b = s5b := by native_decide
theorem hc6a : autoDrain cardDB s6a = s6a := by native_decide
theorem hc6b : autoDrain cardDB s6b = s6b := by native_decide

-- failDraw, play c6, play c3, resolveRushdown
theorem hs7a : step cardDB s6a .failDraw = some s7a := by native_decide
theorem hc7a : autoDrain cardDB s7a = s7a := by native_decide
theorem hs7b : step cardDB s6b .failDraw = some s7b := by native_decide
theorem hc7b : autoDrain cardDB s7b = s7b := by native_decide

-- play c6: need raw+resolved states
private def s8a_raw : GameState := {
  hand := [ci7, ci5, ci4, ci3]
  drawPile := [], discardPile := []
  exhaustPile := exhaustPileConst
  inUse := [ci6]
  actionQueue := [.resolveCard 6]
  energy := 2, damage := 121, block := 30, stance := .Calm
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}
private def s8b_raw : GameState := {
  hand := [ci5, ci7, ci4, ci3]
  drawPile := [], discardPile := []
  exhaustPile := exhaustPileConst
  inUse := [ci6]
  actionQueue := [.resolveCard 6]
  energy := 2, damage := 121, block := 30, stance := .Calm
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}

theorem hs8a : step cardDB s7a (.play 6) = some s8a_raw := by native_decide
theorem hc8a : autoDrain cardDB s8a_raw = s8a := by native_decide
theorem hs8b : step cardDB s7b (.play 6) = some s8b_raw := by native_decide
theorem hc8b : autoDrain cardDB s8b_raw = s8b := by native_decide

-- play c3 (Eruption+)
private def s9a_raw : GameState := {
  hand := [ci7, ci5, ci4]
  drawPile := [], discardPile := [ci6]
  exhaustPile := exhaustPileConst
  inUse := [ci3]
  actionQueue := [.resolveCard 3]
  energy := 3, damage := 130, block := 36, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}
private def s9b_raw : GameState := {
  hand := [ci5, ci7, ci4]
  drawPile := [], discardPile := [ci6]
  exhaustPile := exhaustPileConst
  inUse := [ci3]
  actionQueue := [.resolveCard 3]
  energy := 3, damage := 130, block := 36, stance := .Wrath
  orbs := [], orbSlots := 3, focus := 0
  enemy := { vulnerable := 0, weak := 0, intending := true }
  activePowers := [MentalFortressPlus, Rushdown, Rushdown]
  nextId := 14, noDraw := false, corruptionActive := false
}

theorem hs9a : step cardDB s8a (.play 3) = some s9a_raw := by native_decide
theorem hc9a : autoDrain cardDB s9a_raw = s9a := by native_decide
theorem hs9b : step cardDB s8b (.play 3) = some s9b_raw := by native_decide
theorem hc9b : autoDrain cardDB s9b_raw = s9b := by native_decide

theorem hs10a : step cardDB s9a .resolveRushdown = some s10a := by native_decide
theorem hc10a : autoDrain cardDB s10a = s10a := by native_decide
theorem hs10b : step cardDB s9b .resolveRushdown = some s10b := by native_decide
theorem hc10b : autoDrain cardDB s10b = s10b := by native_decide

-- Shuffle 2 draws
theorem hd11a1 (oracle : ShuffleOracle) (h : oracle 1 [ci3, ci6] = [ci3, ci6]) :
    drawCardL2 oracle 1 s10a 3 = some (s11a1, 2) := by
  unfold drawCardL2; simp only [s10a, s9a, ci3, ci6] at h ⊢; rw [h]; native_decide
theorem hd12a1 (oracle : ShuffleOracle) :
    drawCardL2 oracle 2 s11a1 6 = some (s12a1, 2) := rfl

theorem hd11a2 (oracle : ShuffleOracle) (h : oracle 1 [ci3, ci6] = [ci6, ci3]) :
    drawCardL2 oracle 1 s10a 6 = some (s11a2, 2) := by
  unfold drawCardL2; simp only [s10a, s9a, ci3, ci6] at h ⊢; rw [h]; native_decide
theorem hd12a2 (oracle : ShuffleOracle) :
    drawCardL2 oracle 2 s11a2 3 = some (s12a2, 2) := rfl

theorem hd11b1 (oracle : ShuffleOracle) (h : oracle 1 [ci3, ci6] = [ci3, ci6]) :
    drawCardL2 oracle 1 s10b 3 = some (s11b1, 2) := by
  unfold drawCardL2; simp only [s10b, s9b, ci3, ci6] at h ⊢; rw [h]; native_decide
theorem hd12b1 (oracle : ShuffleOracle) :
    drawCardL2 oracle 2 s11b1 6 = some (s12b1, 2) := rfl

theorem hd11b2 (oracle : ShuffleOracle) (h : oracle 1 [ci3, ci6] = [ci6, ci3]) :
    drawCardL2 oracle 1 s10b 6 = some (s11b2, 2) := by
  unfold drawCardL2; simp only [s10b, s9b, ci3, ci6] at h ⊢; rw [h]; native_decide
theorem hd12b2 (oracle : ShuffleOracle) :
    drawCardL2 oracle 2 s11b2 3 = some (s12b2, 2) := rfl

-- Cleanup lemmas for shuffle draw states
theorem hc11a1 : autoDrain cardDB s11a1 = s11a1 := by native_decide
theorem hc11a2 : autoDrain cardDB s11a2 = s11a2 := by native_decide
theorem hc11b1 : autoDrain cardDB s11b1 = s11b1 := by native_decide
theorem hc11b2 : autoDrain cardDB s11b2 = s11b2 := by native_decide
theorem hc12a1 : autoDrain cardDB s12a1 = s12a1 := by native_decide
theorem hc12a2 : autoDrain cardDB s12a2 = s12a2 := by native_decide
theorem hc12b1 : autoDrain cardDB s12b1 = s12b1 := by native_decide
theorem hc12b2 : autoDrain cardDB s12b2 = s12b2 := by native_decide

-- failDraw + tail: play c7, play c5, autoPlayFlurry c7
-- These converge: a1=b1 → stateBx, a2=b2 → stateBy
theorem hs13a1 : step cardDB s12a1 .failDraw = some s13a1 := by native_decide
theorem hc13a1 : autoDrain cardDB s13a1 = s13a1 := by native_decide
theorem hs13a2 : step cardDB s12a2 .failDraw = some s13a2 := by native_decide
theorem hc13a2 : autoDrain cardDB s13a2 = s13a2 := by native_decide
theorem hs13b1 : step cardDB s12b1 .failDraw = some s13b1 := by native_decide
theorem hc13b1 : autoDrain cardDB s13b1 = s13b1 := by native_decide
theorem hs13b2 : step cardDB s12b2 .failDraw = some s13b2 := by native_decide
theorem hc13b2 : autoDrain cardDB s13b2 = s13b2 := by native_decide

-- Verify tails by native_decide
theorem tail_a1 : executeL2 cardDB (fun _ _ => []) 2 s13a1
    [.play 7, .play 5, .autoPlayFlurry 7] = some (stateBx, 2) := by native_decide
theorem tail_a2 : executeL2 cardDB (fun _ _ => []) 2 s13a2
    [.play 7, .play 5, .autoPlayFlurry 7] = some (stateBy, 2) := by native_decide
theorem tail_b1 : executeL2 cardDB (fun _ _ => []) 2 s13b1
    [.play 7, .play 5, .autoPlayFlurry 7] = some (stateBx, 2) := by native_decide
theorem tail_b2 : executeL2 cardDB (fun _ _ => []) 2 s13b2
    [.play 7, .play 5, .autoPlayFlurry 7] = some (stateBy, 2) := by native_decide

-- Tail oracle-independence
theorem tail_oracle_indep (o1 o2 : ShuffleOracle) (idx : Nat) (s : GameState) :
    executeL2 cardDB o1 idx s [.play 7, .play 5, .autoPlayFlurry 7] =
    executeL2 cardDB o2 idx s [.play 7, .play 5, .autoPlayFlurry 7] := by
  simp only [executeL2, stepL2]

theorem hc_Bx : autoDrain cardDB stateBx = stateBx := by native_decide
theorem hc_By : autoDrain cardDB stateBy = stateBy := by native_decide

-- ============================================================
-- PER-CASE LOOP PROOFS
-- ============================================================

private theorem loop_a1 (oracle : ShuffleOracle)
    (h1 : oracle 0 [ci5, ci7] = [ci5, ci7]) (h2 : oracle 1 [ci3, ci6] = [ci3, ci6]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateBx, 2) := by
  have htrace : mkLoopTrace oracle = [.play 4, .resolveRushdown, .autoPlayFlurry 7,
      .draw 4, .draw 5, .draw 7, .failDraw,
      .play 6, .play 3, .resolveRushdown,
      .draw 3, .draw 6, .failDraw,
      .play 7, .play 5, .autoPlayFlurry 7] := by
    unfold mkLoopTrace; rw [h1, h2]; simp [ci3, ci5, ci6, ci7]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_step (by intro c; simp) hs3)]
  rw [exL2_cons hc3 (sL2_draw (hd4 oracle))]
  rw [exL2_cons hc4 (sL2_draw (hd5a oracle h1))]
  rw [exL2_cons hc5a (sL2_draw (hd6a oracle))]
  rw [exL2_cons hc6a (sL2_step (by intro c; simp) hs7a)]
  rw [exL2_cons hc7a (sL2_step (by intro c; simp) hs8a)]
  rw [exL2_cons hc8a (sL2_step (by intro c; simp) hs9a)]
  rw [exL2_cons hc9a (sL2_step (by intro c; simp) hs10a)]
  rw [exL2_cons hc10a (sL2_draw (hd11a1 oracle h2))]
  rw [exL2_cons hc11a1 (sL2_draw (hd12a1 oracle))]
  rw [exL2_cons hc12a1 (sL2_step (by intro c; simp) hs13a1)]
  rw [tail_oracle_indep oracle (fun _ _ => []) 2 s13a1]
  exact tail_a1

private theorem loop_a2 (oracle : ShuffleOracle)
    (h1 : oracle 0 [ci5, ci7] = [ci5, ci7]) (h2 : oracle 1 [ci3, ci6] = [ci6, ci3]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateBy, 2) := by
  have htrace : mkLoopTrace oracle = [.play 4, .resolveRushdown, .autoPlayFlurry 7,
      .draw 4, .draw 5, .draw 7, .failDraw,
      .play 6, .play 3, .resolveRushdown,
      .draw 6, .draw 3, .failDraw,
      .play 7, .play 5, .autoPlayFlurry 7] := by
    unfold mkLoopTrace; rw [h1, h2]; simp [ci3, ci5, ci6, ci7]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_step (by intro c; simp) hs3)]
  rw [exL2_cons hc3 (sL2_draw (hd4 oracle))]
  rw [exL2_cons hc4 (sL2_draw (hd5a oracle h1))]
  rw [exL2_cons hc5a (sL2_draw (hd6a oracle))]
  rw [exL2_cons hc6a (sL2_step (by intro c; simp) hs7a)]
  rw [exL2_cons hc7a (sL2_step (by intro c; simp) hs8a)]
  rw [exL2_cons hc8a (sL2_step (by intro c; simp) hs9a)]
  rw [exL2_cons hc9a (sL2_step (by intro c; simp) hs10a)]
  rw [exL2_cons hc10a (sL2_draw (hd11a2 oracle h2))]
  rw [exL2_cons hc11a2 (sL2_draw (hd12a2 oracle))]
  rw [exL2_cons hc12a2 (sL2_step (by intro c; simp) hs13a2)]
  rw [tail_oracle_indep oracle (fun _ _ => []) 2 s13a2]
  exact tail_a2

private theorem loop_b1 (oracle : ShuffleOracle)
    (h1 : oracle 0 [ci5, ci7] = [ci7, ci5]) (h2 : oracle 1 [ci3, ci6] = [ci3, ci6]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateBx, 2) := by
  have htrace : mkLoopTrace oracle = [.play 4, .resolveRushdown, .autoPlayFlurry 7,
      .draw 4, .draw 7, .draw 5, .failDraw,
      .play 6, .play 3, .resolveRushdown,
      .draw 3, .draw 6, .failDraw,
      .play 7, .play 5, .autoPlayFlurry 7] := by
    unfold mkLoopTrace; rw [h1, h2]; simp [ci3, ci5, ci6, ci7]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_step (by intro c; simp) hs3)]
  rw [exL2_cons hc3 (sL2_draw (hd4 oracle))]
  rw [exL2_cons hc4 (sL2_draw (hd5b oracle h1))]
  rw [exL2_cons hc5b (sL2_draw (hd6b oracle))]
  rw [exL2_cons hc6b (sL2_step (by intro c; simp) hs7b)]
  rw [exL2_cons hc7b (sL2_step (by intro c; simp) hs8b)]
  rw [exL2_cons hc8b (sL2_step (by intro c; simp) hs9b)]
  rw [exL2_cons hc9b (sL2_step (by intro c; simp) hs10b)]
  rw [exL2_cons hc10b (sL2_draw (hd11b1 oracle h2))]
  rw [exL2_cons hc11b1 (sL2_draw (hd12b1 oracle))]
  rw [exL2_cons hc12b1 (sL2_step (by intro c; simp) hs13b1)]
  rw [tail_oracle_indep oracle (fun _ _ => []) 2 s13b1]
  exact tail_b1

private theorem loop_b2 (oracle : ShuffleOracle)
    (h1 : oracle 0 [ci5, ci7] = [ci7, ci5]) (h2 : oracle 1 [ci3, ci6] = [ci6, ci3]) :
    executeL2 cardDB oracle 0 stateA (mkLoopTrace oracle) = some (stateBy, 2) := by
  have htrace : mkLoopTrace oracle = [.play 4, .resolveRushdown, .autoPlayFlurry 7,
      .draw 4, .draw 7, .draw 5, .failDraw,
      .play 6, .play 3, .resolveRushdown,
      .draw 6, .draw 3, .failDraw,
      .play 7, .play 5, .autoPlayFlurry 7] := by
    unfold mkLoopTrace; rw [h1, h2]; simp [ci3, ci5, ci6, ci7]
  rw [htrace]
  rw [exL2_cons hc_stateA (sL2_step (by intro c; simp) hs1)]
  rw [exL2_cons hc1 (sL2_step (by intro c; simp) hs2)]
  rw [exL2_cons hc2 (sL2_step (by intro c; simp) hs3)]
  rw [exL2_cons hc3 (sL2_draw (hd4 oracle))]
  rw [exL2_cons hc4 (sL2_draw (hd5b oracle h1))]
  rw [exL2_cons hc5b (sL2_draw (hd6b oracle))]
  rw [exL2_cons hc6b (sL2_step (by intro c; simp) hs7b)]
  rw [exL2_cons hc7b (sL2_step (by intro c; simp) hs8b)]
  rw [exL2_cons hc8b (sL2_step (by intro c; simp) hs9b)]
  rw [exL2_cons hc9b (sL2_step (by intro c; simp) hs10b)]
  rw [exL2_cons hc10b (sL2_draw (hd11b2 oracle h2))]
  rw [exL2_cons hc11b2 (sL2_draw (hd12b2 oracle))]
  rw [exL2_cons hc12b2 (sL2_step (by intro c; simp) hs13b2)]
  rw [tail_oracle_indep oracle (fun _ _ => []) 2 s13b2]
  exact tail_b2

-- ============================================================
-- MAIN THEOREM
-- ============================================================

theorem ComboStandardWatcher_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hvalid
  have hp1 := hvalid 0 [ci5, ci7]
  have hp2 := hvalid 1 [ci3, ci6]
  have h57 := perm_2_ci (oracle 0 [ci5, ci7]) ci5 ci7 (by decide) hp1
  have h36 := perm_2_ci (oracle 1 [ci3, ci6]) ci3 ci6 (by decide) hp2
  rcases h57 with h1 | h1 <;> rcases h36 with h2 | h2
  · exact ⟨mkLoopTrace oracle, stateBx, 2, loop_a1 oracle h1 h2, noEndTurn_a1 oracle h1 h2, same_mod_x, dealt_dmg_x⟩
  · exact ⟨mkLoopTrace oracle, stateBy, 2, loop_a2 oracle h1 h2, noEndTurn_a2 oracle h1 h2, same_mod_y, dealt_dmg_y⟩
  · exact ⟨mkLoopTrace oracle, stateBx, 2, loop_b1 oracle h1 h2, noEndTurn_b1 oracle h1 h2, same_mod_x, dealt_dmg_x⟩
  · exact ⟨mkLoopTrace oracle, stateBy, 2, loop_b2 oracle h1 h2, noEndTurn_b2 oracle h1 h2, same_mod_y, dealt_dmg_y⟩

end ComboStandardWatcher_L2
