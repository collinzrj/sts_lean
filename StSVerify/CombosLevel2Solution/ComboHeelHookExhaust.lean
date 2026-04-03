/-
  Silent - Heel Hook + Exhaust Streamlined (Level 2 Strict)
  Cards: 10
  v2 engine rewrite

  Key insight: exhaust all cards except HH1 (id=0), HH2 (id=1), Neutralize+ (id=2),
  EscapePlan+ (id=8), Backflip+ (id=9). Loop alternates two Heel Hooks.
  Each shuffle is singleton -> deterministic.

  STRICT: native_decide only in helper lemmas, not in main proof body.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboHeelHookExhaust_L2_Strict

-- ============================================================
-- Deck definition (v2: CardName x count)
-- IDs: HH1=0, HH2=1, N=2, Mal=3, PW=4, Adr=5, DDD=6, AI=7, EP=8, BF=9
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(HeelHookPlus, 2), (NeutralizePlus, 1), (MalaisePlus, 1), (PiercingWail, 1),
   (AdrenalinePlus, 1), (DieDieDiePlus, 1), (AfterImage, 1), (EscapePlanPlus, 1),
   (BackflipPlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 2, intending := false }

-- Card instance abbreviations
def hh1 : CardInstance := { id := 0, name := HeelHookPlus, cost := 1, damage := 8 }
def hh2 : CardInstance := { id := 1, name := HeelHookPlus, cost := 1, damage := 8 }
def neut : CardInstance := { id := 2, name := NeutralizePlus, cost := 0, damage := 4 }
def ep : CardInstance := { id := 8, name := EscapePlanPlus, cost := 0, damage := 0 }
def bf : CardInstance := { id := 9, name := BackflipPlus, cost := 1, damage := 0 }

-- ============================================================
-- Traces
-- ============================================================

def setupTrace : List Action := [
  -- Turn 1: draw exhaust/power cards
  .draw 5, .draw 3, .draw 4, .draw 6, .draw 7,
  .play 3,                        -- Malaise+ (0E, exhaust self)
  .play 5,                        -- Adrenaline+ (0E, +2E, draw 2, exhaust self)
  .draw 8, .draw 9,
  .play 7,                        -- After Image (1E, power)
  .play 4,                        -- Piercing Wail (1E, exhaust self)
  .play 6,                        -- Die Die Die+ (1E, 17dmg, exhaust self)
  .play 8,                        -- Escape Plan+ (0E, draw 1)
  .draw 0,                        -- draw HH1
  .play 9,                        -- Backflip+ (1E, +8blk, draw 2)
  .draw 1, .draw 2,
  .endTurn,
  -- Turn 2
  .draw 0, .draw 1, .draw 2, .draw 8, .draw 9,
  .play 0,                        -- HH1: 8dmg, weak -> +1E, +1draw
  .failDraw                       -- piles empty; HH1 -> discard via autoDrain resolveCard
]

def stateA : GameState := {
  hand := [bf, ep, neut, hh2]
  drawPile := []
  discardPile := [hh1]
  exhaustPile := [{ id := 6, name := DieDieDiePlus, cost := 1, damage := 17 },
                  { id := 4, name := PiercingWail, cost := 1, damage := 0 },
                  { id := 5, name := AdrenalinePlus, cost := 0, damage := 0 },
                  { id := 3, name := MalaisePlus, cost := 0, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 3
  damage := 25
  block := 1
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := [AfterImage]
  nextId := 10
  noDraw := false
  corruptionActive := false
}

def loopTrace : List Action := [
  .play 1,                        -- HH2: 8dmg, +1E, +1draw; queue=[draw, resolveCard 1]
  .draw 0,                        -- shuffle [HH1] from discard->draw, draw HH1; autoDrain resolves hh2->discard
  .play 0,                        -- HH1: 8dmg, +1E, +1draw; queue=[draw, resolveCard 0]
  .draw 1                         -- shuffle [HH2] from discard->draw, draw HH2; autoDrain resolves hh1->discard
]

def stateB : GameState := {
  hand := [hh2, bf, ep, neut]
  drawPile := []
  discardPile := [hh1]
  exhaustPile := stateA.exhaustPile
  inUse := []
  actionQueue := []
  energy := 3
  damage := 41
  block := 3
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := [AfterImage]
  nextId := 10
  noDraw := false
  corruptionActive := false
}

-- Intermediate: after play HH2 (card in inUse, queue=[draw, resolveCard 1])
def stateS1 : GameState := {
  hand := [bf, ep, neut]
  drawPile := []
  discardPile := [hh1]
  exhaustPile := stateA.exhaustPile
  inUse := [hh2]
  actionQueue := [.draw, .resolveCard 1]
  energy := 3
  damage := 33
  block := 2
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := [AfterImage]
  nextId := 10
  noDraw := false
  corruptionActive := false
}

-- Raw state after draw HH1 (before autoDrain resolves resolveCard 1)
def stateR2 : GameState := {
  hand := [hh1, bf, ep, neut]
  drawPile := []
  discardPile := []
  exhaustPile := stateA.exhaustPile
  inUse := [hh2]
  actionQueue := [.resolveCard 1]
  energy := 3
  damage := 33
  block := 2
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := [AfterImage]
  nextId := 10
  noDraw := false
  corruptionActive := false
}

-- After autoDrain resolves resolveCard 1: HH2 -> discard
def stateS2 : GameState := {
  hand := [hh1, bf, ep, neut]
  drawPile := []
  discardPile := [hh2]
  exhaustPile := stateA.exhaustPile
  inUse := []
  actionQueue := []
  energy := 3
  damage := 33
  block := 2
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := [AfterImage]
  nextId := 10
  noDraw := false
  corruptionActive := false
}

-- After play HH1 (card in inUse, queue=[draw, resolveCard 0])
def stateS3 : GameState := {
  hand := [bf, ep, neut]
  drawPile := []
  discardPile := [hh2]
  exhaustPile := stateA.exhaustPile
  inUse := [hh1]
  actionQueue := [.draw, .resolveCard 0]
  energy := 3
  damage := 41
  block := 3
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := [AfterImage]
  nextId := 10
  noDraw := false
  corruptionActive := false
}

-- Raw state after draw HH2 (before autoDrain resolves resolveCard 0)
def stateR4 : GameState := {
  hand := [hh2, bf, ep, neut]
  drawPile := []
  discardPile := []
  exhaustPile := stateA.exhaustPile
  inUse := [hh1]
  actionQueue := [.resolveCard 0]
  energy := 3
  damage := 41
  block := 3
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 0, weak := 2, intending := false }
  activePowers := [AfterImage]
  nextId := 10
  noDraw := false
  corruptionActive := false
}

-- ============================================================
-- VERIFICATION (Level 2 Strict: native_decide only in helpers)
-- ============================================================

-- Helper lemmas (native_decide allowed: all inputs concrete)
theorem setup_ok :
    execute cardDB (mkInitialState cardDB allCards enemy) setupTrace = some stateA := by
  native_decide

theorem no_end : noEndTurn loopTrace = true := by native_decide
theorem same_mod : sameModAccum stateA stateB = true := by native_decide
theorem dealt_dmg : dealtDamage stateA stateB = true := by native_decide

private theorem perm_singleton_eq (a : CardInstance) (l : List CardInstance)
    (h : List.Perm l [a]) : l = [a] :=
  List.perm_singleton.mp h

-- Clean state lemmas (autoDrain handles resolveCard)
private theorem clean_stateA : autoDrain cardDB stateA = stateA := by
  native_decide

-- Step 1: play HH2 -> stateS1
private theorem step1_val :
    step cardDB stateA (.play 1) = some stateS1 := by native_decide

private theorem clean_stateS1 : autoDrain cardDB stateS1 = stateS1 := by
  native_decide

-- Step 2: draw HH1 (oracle shuffles singleton [hh1])
private theorem step2_raw (oracle : ShuffleOracle) (hValid : validOracle oracle) :
    drawCardL2 oracle 0 stateS1 0 = some (stateR2, 1) := by
  have hp : oracle 0 [hh1] = [hh1] := perm_singleton_eq hh1 _ (hValid 0 [hh1])
  simp only [hh1] at hp
  unfold drawCardL2
  simp only [stateS1, stateR2, hh1, hh2, neut, ep, bf]
  rw [hp]
  native_decide

-- autoDrain on stateR2 resolves resolveCard 1 -> stateS2
private theorem clean_stateR2 : autoDrain cardDB stateR2 = stateS2 := by
  native_decide

-- Step 3: play HH1 -> stateS3
private theorem step3_val :
    step cardDB stateS2 (.play 0) = some stateS3 := by native_decide

private theorem clean_stateS3 : autoDrain cardDB stateS3 = stateS3 := by
  native_decide

-- Step 4: draw HH2 (oracle shuffles singleton [hh2])
private theorem step4_raw (oracle : ShuffleOracle) (hValid : validOracle oracle) :
    drawCardL2 oracle 1 stateS3 1 = some (stateR4, 2) := by
  have hp : oracle 1 [hh2] = [hh2] := perm_singleton_eq hh2 _ (hValid 1 [hh2])
  simp only [hh2] at hp
  unfold drawCardL2
  simp only [stateS3, stateR4, hh1, hh2, neut, ep, bf]
  rw [hp]
  native_decide

-- autoDrain on stateR4 resolves resolveCard 0 -> stateB
private theorem clean_stateR4 : autoDrain cardDB stateR4 = stateB := by
  native_decide

-- Main loop theorem (NO native_decide -- only rw/simp)
theorem loop_l2 (oracle : ShuffleOracle) (hv : validOracle oracle) :
    executeL2 cardDB oracle 0 stateA loopTrace = some (stateB, 2) := by
  simp only [loopTrace, executeL2, stepL2]
  rw [clean_stateA]
  rw [step1_val]; simp only []
  rw [clean_stateS1]
  rw [step2_raw oracle hv]; simp only []
  rw [clean_stateR2]
  rw [step3_val]; simp only []
  rw [clean_stateS3]
  rw [step4_raw oracle hv]; simp only []
  rw [clean_stateR4]

-- Main theorem (NO native_decide -- only refine/intro/exact)
theorem ComboHeelHookExhaust_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB allCards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  exact ⟨loopTrace, stateB, 2, loop_l2 oracle hValid, no_end, same_mod, dealt_dmg⟩

end ComboHeelHookExhaust_L2_Strict
