/-
  Ironclad - Corruption Exhaust + Dropkick (Level 2 Strict)
  Cards: 13
  v2 engine rewrite

  Key insight: exhaust all cards except DK#1 (id=4), DK#2 (id=5), Bash+ (id=3).
  Loop alternates two Dropkicks. Each shuffle is of a singleton list,
  so the oracle cannot affect the order.

  STRICT: native_decide only in helper lemmas, not in main proof body.
-/

import StSVerify.Engine
import StSVerify.CardDB

open CardName Action

namespace ComboCorruptionDropkick_L2_Strict

-- ============================================================
-- Deck definition (v2: CardName x count)
-- IDs: Corr=0, DE+=1, FNP+=2, Bash+=3, DK1=4, DK2=5,
--      SIO1=6, SIO2=7, TG+=8, Met+=9, Imp+=10, Off=11, BT+=12
-- ============================================================

def allCards : List (CardName × Nat) :=
  [(Corruption, 1), (DarkEmbracePlus, 1), (FeelNoPainPlus, 1), (BashPlus, 1),
   (Dropkick, 2), (ShrugItOff, 2), (TrueGritPlus, 1), (MetallicizePlus, 1),
   (ImperviousPlus, 1), (Offering, 1), (BattleTrancePlus, 1)]

def enemy : EnemyState := { vulnerable := 3, weak := 0, intending := false }

-- Card instance abbreviations for readability
def dk1 : CardInstance := { id := 4, name := Dropkick, cost := 1, damage := 5 }
def dk2 : CardInstance := { id := 5, name := Dropkick, cost := 1, damage := 5 }
def bash : CardInstance := { id := 3, name := BashPlus, cost := 2, damage := 10 }

-- ============================================================
-- Traces
-- ============================================================

def setupTrace : List Action := [
  -- Turn 1: play powers + exhaust junk
  .draw 11, .draw 0, .draw 1, .draw 2, .draw 8,
  .play 11,                       -- Offering (0E): +2E, draw 3, exhaust self
  .draw 9, .draw 12, .draw 3,
  .play 0, .play 1, .play 2,     -- Corruption(3E), DarkEmbrace+(1E), FeelNoPain+(1E)
  .play 8,                        -- TrueGrit+ (0 cost, corruption): +9blk, exhaust 1, self exhausts
  .exhaust 12,                    -- Exhaust BattleTrance+ -> DE+1 draw, FNP+4 block
  .draw 4, .draw 5,              -- Draw both Dropkicks (2 draws: DE on TG+ exhaust + DE on BT+ exhaust)
  .endTurn,
  -- Turn 2: play Met+, exhaust remaining junk, establish loop
  .draw 6, .draw 7, .draw 10,
  .draw 9, .draw 4,              -- shuffle discard -> draw; draw Met+ and DK#1
  .play 9,                        -- Metallicize+ (1E, power)
  .play 6,                        -- ShrugItOff#1 (0 cost, corruption): +8blk, draw 1, exhausts -> DE+1, FNP+4
  .draw 5, .draw 3,              -- SIO draw + DE draw
  .play 7,                        -- ShrugItOff#2 (0 cost, corruption): +8blk, draw 1, exhausts -> DE+1, FNP+4
  .failDraw,                      -- piles empty (first draw)
  .failDraw,                      -- piles empty (DE draw after resolveCard 7)
  .play 10,                       -- Impervious+ (0 cost, corruption): +40blk, exhausts -> DE+1, FNP+4
  .failDraw,                      -- piles empty
  .play 5,                        -- DK#2: 7dmg, +1E, +1draw
  .failDraw,                      -- piles empty (DK#2 still in inUse)
  .play 4,                        -- DK#1: 7dmg, +1E, +1draw
  .draw 5                         -- shuffle DK#2 from discard -> draw, draw DK#2
]

def loopTrace : List Action := [
  .play 5,                        -- DK#2: 7dmg, +1E, +1draw; queue=[draw, resolveCard 5]
  .draw 4,                        -- shuffle DK#1 from discard->draw, draw DK#1; autoDrain resolves dk2->discard
  .play 4,                        -- DK#1: 7dmg, +1E, +1draw; queue=[draw, resolveCard 4]
  .draw 5                         -- shuffle DK#2 from discard->draw, draw DK#2; autoDrain resolves dk1->discard
]

def stateA : GameState := {
  hand := [dk2, bash]
  drawPile := []
  discardPile := [dk1]
  exhaustPile := [{ id := 10, name := ImperviousPlus, cost := 2, damage := 0 },
                  { id := 7, name := ShrugItOff, cost := 1, damage := 0 },
                  { id := 6, name := ShrugItOff, cost := 1, damage := 0 },
                  { id := 8, name := TrueGritPlus, cost := 1, damage := 0 },
                  { id := 12, name := BattleTrancePlus, cost := 0, damage := 0 },
                  { id := 11, name := Offering, cost := 0, damage := 0 }]
  inUse := []
  actionQueue := []
  energy := 2
  damage := 14
  block := 68
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 3, weak := 0, intending := false }
  activePowers := [MetallicizePlus, FeelNoPainPlus, DarkEmbracePlus, Corruption]
  nextId := 13
  noDraw := false
  corruptionActive := true
}

def stateB : GameState :=
  { stateA with damage := 28 }

-- Intermediate: after play DK#2 (card in inUse, queue=[draw, resolveCard 5])
def stateS1 : GameState := {
  hand := [bash]
  drawPile := []
  discardPile := [dk1]
  exhaustPile := stateA.exhaustPile
  inUse := [dk2]
  actionQueue := [.draw, .resolveCard 5]
  energy := 2
  damage := 21
  block := 68
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 3, weak := 0, intending := false }
  activePowers := [MetallicizePlus, FeelNoPainPlus, DarkEmbracePlus, Corruption]
  nextId := 13
  noDraw := false
  corruptionActive := true
}

-- Raw state after draw DK#1 (before autoDrain resolves resolveCard 5)
def stateR2 : GameState := {
  hand := [dk1, bash]
  drawPile := []
  discardPile := []
  exhaustPile := stateA.exhaustPile
  inUse := [dk2]
  actionQueue := [.resolveCard 5]
  energy := 2
  damage := 21
  block := 68
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 3, weak := 0, intending := false }
  activePowers := [MetallicizePlus, FeelNoPainPlus, DarkEmbracePlus, Corruption]
  nextId := 13
  noDraw := false
  corruptionActive := true
}

-- After autoDrain resolves resolveCard 5: DK#2 moves to discard
def stateS2 : GameState := {
  hand := [dk1, bash]
  drawPile := []
  discardPile := [dk2]
  exhaustPile := stateA.exhaustPile
  inUse := []
  actionQueue := []
  energy := 2
  damage := 21
  block := 68
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 3, weak := 0, intending := false }
  activePowers := [MetallicizePlus, FeelNoPainPlus, DarkEmbracePlus, Corruption]
  nextId := 13
  noDraw := false
  corruptionActive := true
}

-- After play DK#1 (card in inUse, queue=[draw, resolveCard 4])
def stateS3 : GameState := {
  hand := [bash]
  drawPile := []
  discardPile := [dk2]
  exhaustPile := stateA.exhaustPile
  inUse := [dk1]
  actionQueue := [.draw, .resolveCard 4]
  energy := 2
  damage := 28
  block := 68
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 3, weak := 0, intending := false }
  activePowers := [MetallicizePlus, FeelNoPainPlus, DarkEmbracePlus, Corruption]
  nextId := 13
  noDraw := false
  corruptionActive := true
}

-- Raw state after draw DK#2 (before autoDrain resolves resolveCard 4)
def stateR4 : GameState := {
  hand := [dk2, bash]
  drawPile := []
  discardPile := []
  exhaustPile := stateA.exhaustPile
  inUse := [dk1]
  actionQueue := [.resolveCard 4]
  energy := 2
  damage := 28
  block := 68
  stance := .Neutral
  orbs := []
  orbSlots := 3
  focus := 0
  enemy := { vulnerable := 3, weak := 0, intending := false }
  activePowers := [MetallicizePlus, FeelNoPainPlus, DarkEmbracePlus, Corruption]
  nextId := 13
  noDraw := false
  corruptionActive := true
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

-- Step 1: play DK#2 -> stateS1
private theorem step1_play :
    step cardDB stateA (.play 5) = some stateS1 := by native_decide

private theorem clean_stateS1 : autoDrain cardDB stateS1 = stateS1 := by
  native_decide

-- Step 2: draw DK#1 with oracle (singleton shuffle)
private theorem step2_draw_raw (oracle : ShuffleOracle) (hValid : validOracle oracle) :
    drawCardL2 oracle 0 stateS1 4 = some (stateR2, 1) := by
  have hp : oracle 0 [dk1] = [dk1] := perm_singleton_eq dk1 _ (hValid 0 [dk1])
  simp only [dk1] at hp
  unfold drawCardL2
  simp only [stateS1, stateR2, dk1, dk2, bash]
  rw [hp]
  native_decide

-- autoDrain on stateR2 resolves resolveCard 5 -> stateS2
private theorem clean_stateR2 : autoDrain cardDB stateR2 = stateS2 := by
  native_decide

-- Step 3: play DK#1 -> stateS3
private theorem step3_play :
    step cardDB stateS2 (.play 4) = some stateS3 := by native_decide

private theorem clean_stateS3 : autoDrain cardDB stateS3 = stateS3 := by
  native_decide

-- Step 4: draw DK#2 with oracle (singleton shuffle)
private theorem step4_draw_raw (oracle : ShuffleOracle) (hValid : validOracle oracle) :
    drawCardL2 oracle 1 stateS3 5 = some (stateR4, 2) := by
  have hp : oracle 1 [dk2] = [dk2] := perm_singleton_eq dk2 _ (hValid 1 [dk2])
  simp only [dk2] at hp
  unfold drawCardL2
  simp only [stateS3, stateR4, dk1, dk2, bash]
  rw [hp]
  native_decide

-- autoDrain on stateR4 resolves resolveCard 4 -> stateB
private theorem clean_stateR4 : autoDrain cardDB stateR4 = stateB := by
  native_decide

-- Main loop theorem (NO native_decide -- only rw/simp)
theorem loop_l2 (oracle : ShuffleOracle) (hv : validOracle oracle) :
    executeL2 cardDB oracle 0 stateA loopTrace = some (stateB, 2) := by
  simp only [loopTrace, executeL2, stepL2]
  rw [clean_stateA]
  rw [step1_play]; simp only []
  rw [clean_stateS1]
  rw [step2_draw_raw oracle hv]; simp only []
  rw [clean_stateR2]
  rw [step3_play]; simp only []
  rw [clean_stateS3]
  rw [step4_draw_raw oracle hv]; simp only []
  rw [clean_stateR4]

-- Main theorem (NO native_decide -- only refine/intro/exact)
theorem ComboCorruptionDropkick_guaranteed_infinite :
    GuaranteedInfiniteCombo cardDB allCards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle h_valid
  exact ⟨loopTrace, stateB, 2, loop_l2 oracle h_valid, no_end, same_mod, dealt_dmg⟩

end ComboCorruptionDropkick_L2_Strict
