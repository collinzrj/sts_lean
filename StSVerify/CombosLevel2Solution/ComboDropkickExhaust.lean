/-
  Ironclad - Dropkick Exhaust Streamlined Infinite (Level 2 Strict)
  Cards: 11
  v2 engine rewrite

  Key insight: exhaust all cards except Bash+ (id=0), DK1 (id=1), DK2 (id=2), TG+ (id=3).
  Loop alternates two Dropkicks. Each shuffle is singleton -> deterministic.

  STRICT: native_decide only in helper lemmas, not in main proof body.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboDropkickExhaust_L2_Strict

-- ============================================================
-- Deck definition (v2: CardName x count)
-- IDs: Bash+=0, DK1=1, DK2=2, TG1=3, TG2=4, BP=5, SIO+=6, Off+=7, Pur=8, BC+=9, PS+=10
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(BashPlus, 1), (Dropkick, 2), (TrueGritPlus, 2), (BurningPactPlus, 1),
   (ShrugItOffPlus, 1), (OfferingPlus, 1), (Purity, 1), (BattleCryPlus, 1),
   (PommelStrikePlus, 1)]

def enemy : EnemyState := { vulnerable := 3, weak := 0, intending := false }

-- Card instance abbreviations
def dk1 : CardInstance := { id := 1, name := Dropkick, cost := 1, damage := 5 }
def dk2 : CardInstance := { id := 2, name := Dropkick, cost := 1, damage := 5 }
def bash : CardInstance := { id := 0, name := BashPlus, cost := 2, damage := 10 }
def tg : CardInstance := { id := 3, name := TrueGritPlus, cost := 1, damage := 0 }

-- ============================================================
-- Traces
-- ============================================================

def setupTrace : List Action := [
  -- Turn 1: exhaust junk cards
  .draw 8, .draw 7, .draw 5, .draw 6, .draw 10,
  .play 8,                        -- Purity: exhaust self + exhaust 3 from hand
  .exhaust 5, .exhaust 6, .exhaust 10,
  .play 7,                        -- Offering+: +2E, draw 5, exhaust self
  .draw 0, .draw 1, .draw 2, .draw 3, .draw 4,
  .play 3, .exhaust 4,           -- TrueGrit+#1: +9blk, exhaust TG#2
  .play 1,                        -- Dropkick#1: 7dmg (vuln), +1E, +1draw
  .draw 9,                        -- draw BattleCry+
  .play 9,                        -- BattleCry+: exhaust self
  .endTurn,
  -- Turn 2: establish loop state
  .draw 0, .draw 1, .draw 3, .draw 2,
  .failDraw,                       -- only 4 cards in deck
  .play 0,                        -- Bash+: 15dmg (vuln), +3 vuln
  .play 1,                        -- Dropkick#1: 7dmg, +1E, +1draw
  .draw 0,                        -- shuffle discard -> draw, draw Bash+
  .play 2,                        -- Dropkick#2: 7dmg, +1E, +1draw
  .draw 1                         -- draw DK#1
]

def stateA : GameState := {
  hand := [dk1, bash, tg]
  drawPile := []
  discardPile := [dk2]
  exhaustPile := [{ id := 9, name := BattleCryPlus, cost := 0, damage := 0 },
                  { id := 4, name := TrueGritPlus, cost := 1, damage := 0 },
                  { id := 7, name := OfferingPlus, cost := 0, damage := 0 },
                  { id := 8, name := Purity, cost := 0, damage := 0 },
                  { id := 10, name := PommelStrikePlus, cost := 1, damage := 10 },
                  { id := 6, name := ShrugItOffPlus, cost := 1, damage := 0 },
                  { id := 5, name := BurningPactPlus, cost := 1, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 1
  damage := 36
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 6, weak := 0, intending := false }
  activePowers := []
  nextId := 11
  noDraw := false
  corruptionActive := false
}

def loopTrace : List Action := [
  .play 1,                        -- DK#1: 7dmg, +1E, +1draw; queue=[draw, resolveCard 1]
  .draw 2,                        -- shuffle [DK#2] from discard->draw, draw DK#2; autoDrain resolves dk1->discard
  .play 2,                        -- DK#2: 7dmg, +1E, +1draw; queue=[draw, resolveCard 2]
  .draw 1                         -- shuffle [DK#1] from discard->draw, draw DK#1; autoDrain resolves dk2->discard
]

def stateB : GameState :=
  { stateA with damage := 50 }

-- After play DK#1: card in inUse, queue has [draw, resolveCard 1]
def stateS1 : GameState := {
  hand := [bash, tg]
  drawPile := []
  discardPile := [dk2]
  exhaustPile := stateA.exhaustPile
  inUse := [dk1]
  actionQueue := [.draw, .resolveCard 1]
  energy := 1
  damage := 43
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 6, weak := 0, intending := false }
  activePowers := []
  nextId := 11
  noDraw := false
  corruptionActive := false
}

-- After draw DK#2 (raw, before autoDrain resolves resolveCard 1)
def stateR2 : GameState := {
  hand := [dk2, bash, tg]
  drawPile := []
  discardPile := []
  exhaustPile := stateA.exhaustPile
  inUse := [dk1]
  actionQueue := [.resolveCard 1]
  energy := 1
  damage := 43
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 6, weak := 0, intending := false }
  activePowers := []
  nextId := 11
  noDraw := false
  corruptionActive := false
}

-- After autoDrain resolves resolveCard 1: dk1 -> discard
def stateS2 : GameState := {
  hand := [dk2, bash, tg]
  drawPile := []
  discardPile := [dk1]
  exhaustPile := stateA.exhaustPile
  inUse := []
  actionQueue := []
  energy := 1
  damage := 43
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 6, weak := 0, intending := false }
  activePowers := []
  nextId := 11
  noDraw := false
  corruptionActive := false
}

-- After play DK#2: card in inUse, queue has [draw, resolveCard 2]
def stateS3 : GameState := {
  hand := [bash, tg]
  drawPile := []
  discardPile := [dk1]
  exhaustPile := stateA.exhaustPile
  inUse := [dk2]
  actionQueue := [.draw, .resolveCard 2]
  energy := 1
  damage := 50
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 6, weak := 0, intending := false }
  activePowers := []
  nextId := 11
  noDraw := false
  corruptionActive := false
}

-- After draw DK#1 (raw, before autoDrain resolves resolveCard 2)
def stateR4 : GameState := {
  hand := [dk1, bash, tg]
  drawPile := []
  discardPile := []
  exhaustPile := stateA.exhaustPile
  inUse := [dk2]
  actionQueue := [.resolveCard 2]
  energy := 1
  damage := 50
  block := 0
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 6, weak := 0, intending := false }
  activePowers := []
  nextId := 11
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

-- Clean state lemmas (autoDrain now handles resolveCard)
private theorem clean_stateA : autoDrain cardDB stateA = stateA := by
  native_decide

-- Step 1: play DK#1 -> stateS1
private theorem step1_val :
    step cardDB stateA (.play 1) = some stateS1 := by native_decide

private theorem clean_stateS1 : autoDrain cardDB stateS1 = stateS1 := by
  native_decide

-- Step 2: draw DK#2 (oracle shuffles singleton [dk2])
private theorem step2_raw (oracle : ShuffleOracle) (hValid : validOracle oracle) :
    drawCardL2 cardDB oracle 0 stateS1 2 = some (stateR2, 1) := by
  have hp : oracle 0 [dk2] = [dk2] := perm_singleton_eq dk2 _ (hValid 0 [dk2])
  simp only [dk2] at hp
  unfold drawCardL2
  simp only [stateS1, stateR2, dk1, dk2, bash, tg]
  rw [hp]
  native_decide

-- autoDrain on stateR2 resolves resolveCard 1 -> stateS2
private theorem clean_stateR2 : autoDrain cardDB stateR2 = stateS2 := by
  native_decide

-- Step 3: play DK#2 -> stateS3
private theorem step3_val :
    step cardDB stateS2 (.play 2) = some stateS3 := by native_decide

private theorem clean_stateS3 : autoDrain cardDB stateS3 = stateS3 := by
  native_decide

-- Step 4: draw DK#1 (oracle shuffles singleton [dk1])
private theorem step4_raw (oracle : ShuffleOracle) (hValid : validOracle oracle) :
    drawCardL2 cardDB oracle 1 stateS3 1 = some (stateR4, 2) := by
  have hp : oracle 1 [dk1] = [dk1] := perm_singleton_eq dk1 _ (hValid 1 [dk1])
  simp only [dk1] at hp
  unfold drawCardL2
  simp only [stateS3, stateR4, dk1, dk2, bash, tg]
  rw [hp]
  native_decide

-- autoDrain on stateR4 resolves resolveCard 2 -> stateB
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
theorem ComboDropkickExhaust_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB allCards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle h_valid
  exact ⟨loopTrace, stateB, 2, loop_l2 oracle h_valid, no_end, same_mod, dealt_dmg⟩

end ComboDropkickExhaust_L2_Strict
