/-
  観者 - 真言/神格混合無限 (Level 2)
  Watcher Mantra/Divine combo: Eruption+, InnerPeace, Rushdown×2, MentalFortress+,
  FlurryOfBlows+, EmptyMind+, Prostrate+, plus setup-only cards.
  48 oracle cases (24 × 2), split into individual native_decide theorems.
-/
import StSVerify.CombosSpecL2.ComboMantraDivine
import StSVerify.EngineHelperLemmas
open CardName Action
namespace ComboMantraDivine_L2
private def ci3 : CardInstance := {id:=3,name:=EruptionPlus,cost:=1,damage:=9}
private def ci4 : CardInstance := {id:=4,name:=InnerPeace,cost:=1,damage:=0}
private def ci6 : CardInstance := {id:=6,name:=ProstatePlus,cost:=0,damage:=0}
private def ci7 : CardInstance := {id:=7,name:=EmptyMindPlus,cost:=1,damage:=0}
private def ci8 : CardInstance := {id:=8,name:=FlurryOfBlowsPlus,cost:=0,damage:=6}
def setupTrace : List Action := [.draw 9,.draw 0,.draw 1,.draw 2,.draw 11,.resolveDrawTrigger 11,.play 13,.play 14,.play 0,.play 1,.play 2,.play 9,.draw 3,.draw 4,.draw 5,.draw 6,.draw 7,.draw 8,.draw 10,.draw 12,.failDraw,.play 8,.play 6,.play 4,.endTurn,.draw 3,.draw 4,.draw 5,.draw 10,.draw 12,.play 4,.draw 6,.draw 8,.draw 7,.play 8,.play 6,.play 7,.draw 4,.draw 8,.draw 6,.play 4,.play 8]
def stateA : GameState := {hand:=[ci6,{id:=12,name:=OmnisciencePlus,cost:=3,damage:=0},{id:=10,name:=VaultPlus,cost:=2,damage:=0},{id:=5,name:=PrayPlus,cost:=1,damage:=0},ci3],drawPile:=[],discardPile:=[ci8,ci4,ci7],exhaustPile:=[{id:=9,name:=Scrawl,cost:=1,damage:=0},{id:=14,name:=Miracle,cost:=0,damage:=0},{id:=13,name:=Miracle,cost:=0,damage:=0},{id:=11,name:=DeusExMachina,cost:=0,damage:=0}],inUse:=[],actionQueue:=[],energy:=2,damage:=30,block:=17,stance:=.Calm,orbs:=[],orbSlots:=3,focus:=0,enemy:={vulnerable:=0,weak:=0,intending:=false},activePowers:=[MentalFortressPlus,Rushdown,Rushdown],nextId:=15,noDraw:=false,corruptionActive:=false}
private def stateB : GameState := {hand:=[ci3,ci6,{id:=12,name:=OmnisciencePlus,cost:=3,damage:=0},{id:=10,name:=VaultPlus,cost:=2,damage:=0},{id:=5,name:=PrayPlus,cost:=1,damage:=0}],drawPile:=[],discardPile:=[ci8,ci4,ci7],exhaustPile:=stateA.exhaustPile,inUse:=[],actionQueue:=[],energy:=2,damage:=81,block:=41,stance:=.Calm,orbs:=[],orbSlots:=3,focus:=0,enemy:={vulnerable:=0,weak:=0,intending:=false},activePowers:=[MentalFortressPlus,Rushdown,Rushdown],nextId:=15,noDraw:=false,corruptionActive:=false}
private def pile0 : List CardInstance := [ci3,ci8,ci4,ci7]
private def pile1 : List CardInstance := [ci4,ci8]
private def fixedOracle (p0 p1 : List CardInstance) : ShuffleOracle := fun idx _ => if idx == 0 then p0 else if idx == 1 then p1 else []
private def drawCondBool (fo : ShuffleOracle) (si : Nat) (s : GameState) : List Action → Bool
  | [] => true
  | a :: rest => let sc := autoDrain cardDB s; let dpOk := match a with | .draw _ => sc.drawPile.length > 0 || (decide (si = 0) && decide (sc.discardPile = pile0)) || (decide (si = 1) && decide (sc.discardPile = pile1)) | _ => true; match stepL2 cardDB fo si sc a with | some (s', si') => dpOk && drawCondBool fo si' s' rest | none => false
private def mkLoopTrace (perm1 perm2 : List CardInstance) : List Action := [.play 3] ++ (perm1.map fun c => Action.draw c.id) ++ [.play 8,.play 4,.play 7] ++ (perm2.map fun c => Action.draw c.id) ++ [.failDraw,.play 4,.play 8]

private theorem props_ok : sameModAccum stateA stateB = true ∧ dealtDamage stateA stateB = true := by native_decide
theorem setup_ok : execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA := by native_decide

private theorem drawCondBool_bridge (oracle fo : ShuffleOracle) (h0 : oracle 0 pile0 = fo 0 pile0) (h1 : oracle 1 pile1 = fo 1 pile1) (si : Nat) (s : GameState) (trace : List Action) (hb : drawCondBool fo si s trace = true) : executeL2 cardDB oracle si s trace = executeL2 cardDB fo si s trace := by
  induction trace generalizing si s with
  | nil => rfl
  | cons a rest ih =>
    simp only [drawCondBool] at hb
    match hfo : stepL2 cardDB fo si (autoDrain cardDB s) a with
    | none => rw [hfo] at hb; simp at hb
    | some (s', si') =>
      rw [hfo] at hb; simp only [Bool.and_eq_true] at hb; obtain ⟨hdpOk, hrest⟩ := hb
      have h_step_eq : stepL2 cardDB oracle si (autoDrain cardDB s) a = stepL2 cardDB fo si (autoDrain cardDB s) a := by
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
      show (let sc := autoDrain cardDB s; match stepL2 cardDB oracle si sc a with | none => none | some (s'', si'') => executeL2 cardDB oracle si'' s'' rest) = (let sc := autoDrain cardDB s; match stepL2 cardDB fo si sc a with | none => none | some (s'', si'') => executeL2 cardDB fo si'' s'' rest)
      simp only [h_step_eq, hfo]; exact ih si' s' hrest

private theorem lift (p0 p1 : List CardInstance)
    (hE : executeL2 cardDB (fixedOracle p0 p1) 0 stateA (mkLoopTrace p0 p1) = some (stateB, 2))
    (hD : drawCondBool (fixedOracle p0 p1) 0 stateA (mkLoopTrace p0 p1) = true)
    (hN : noEndTurn (mkLoopTrace p0 p1) = true)
    (oracle : ShuffleOracle) (h0 : oracle 0 pile0 = p0) (h1 : oracle 1 pile1 = p1) :
    ∃ t sB fi, executeL2 cardDB oracle 0 stateA t = some (sB, fi) ∧ noEndTurn t = true ∧ sameModAccum stateA sB = true ∧ dealtDamage stateA sB = true := by
  refine ⟨mkLoopTrace p0 p1, stateB, 2, ?_, hN, props_ok.1, props_ok.2⟩
  have hBr := drawCondBool_bridge oracle (fixedOracle p0 p1) (by simp [fixedOracle]; exact h0) (by simp [fixedOracle]; exact h1) 0 stateA _ hD
  rw [hBr]; exact hE

-- 48 concrete handlers: 24 p0 × 2 p1
private abbrev G (oracle : ShuffleOracle) := ∃ t sB fi, executeL2 cardDB oracle 0 stateA t = some (sB, fi) ∧ noEndTurn t = true ∧ sameModAccum stateA sB = true ∧ dealtDamage stateA sB = true

set_option maxHeartbeats 4000000 in
private theorem h00a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci8,ci4,ci7]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h00b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci8,ci4,ci7]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h01a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci8,ci7,ci4]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h01b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci8,ci7,ci4]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h02a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci4,ci8,ci7]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h02b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci4,ci8,ci7]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h03a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci4,ci7,ci8]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h03b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci4,ci7,ci8]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h04a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci7,ci8,ci4]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h04b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci7,ci8,ci4]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h05a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci7,ci4,ci8]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h05b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci3,ci7,ci4,ci8]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h06a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci3,ci4,ci7]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h06b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci3,ci4,ci7]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h07a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci3,ci7,ci4]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h07b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci3,ci7,ci4]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h08a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci4,ci3,ci7]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h08b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci4,ci3,ci7]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h09a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci4,ci7,ci3]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h09b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci4,ci7,ci3]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h10a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci7,ci3,ci4]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h10b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci7,ci3,ci4]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h11a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci7,ci4,ci3]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h11b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci8,ci7,ci4,ci3]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h12a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci3,ci8,ci7]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h12b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci3,ci8,ci7]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h13a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci3,ci7,ci8]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h13b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci3,ci7,ci8]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h14a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci8,ci3,ci7]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h14b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci8,ci3,ci7]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h15a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci8,ci7,ci3]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h15b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci8,ci7,ci3]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h16a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci7,ci3,ci8]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h16b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci7,ci3,ci8]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h17a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci7,ci8,ci3]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h17b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci4,ci7,ci8,ci3]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h18a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci3,ci8,ci4]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h18b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci3,ci8,ci4]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h19a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci3,ci4,ci8]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h19b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci3,ci4,ci8]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h20a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci8,ci3,ci4]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h20b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci8,ci3,ci4]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h21a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci8,ci4,ci3]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h21b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci8,ci4,ci3]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h22a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci4,ci3,ci8]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h22b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci4,ci3,ci8]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h23a (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci4,ci8,ci3]) (h1 : o 1 pile1 = [ci4,ci8]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1
set_option maxHeartbeats 4000000 in
private theorem h23b (o : ShuffleOracle) (h0 : o 0 pile0 = [ci7,ci4,ci8,ci3]) (h1 : o 1 pile1 = [ci8,ci4]) : G o := lift _ _ (by native_decide) (by native_decide) (by native_decide) o h0 h1

private theorem perm_2_ci (l : List CardInstance) (x y : CardInstance) (hne : x ≠ y) (hp : List.Perm l [x, y]) : l = [x, y] ∨ l = [y, x] := by
  have hlen := hp.length_eq; simp at hlen; match l, hlen with | [a, b], _ => have hx : x ∈ [a, b] := hp.mem_iff.mpr (by simp); have hy : y ∈ [a, b] := hp.mem_iff.mpr (by simp); simp [List.mem_cons, List.mem_nil_iff] at hx hy; have hnd : [a, b].Nodup := hp.nodup_iff.mpr (by simp [hne]); rw [List.nodup_cons] at hnd; simp [List.mem_cons, List.mem_nil_iff] at hnd; rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> (first | simp_all | omega)

set_option maxHeartbeats 1600000 in
private theorem perm4_dispatch (l : List CardInstance) (hp : l.Perm pile0)
    (p1 : List CardInstance) (hp1 : p1 = [ci4, ci8] ∨ p1 = [ci8, ci4])
    (o : ShuffleOracle) (h0 : o 0 pile0 = l) (h1 : o 1 pile1 = p1) : G o := by
  have hlen := hp.length_eq; simp [pile0] at hlen
  match l, hlen with
  | [a, b, c, d], _ =>
    have ha : a ∈ pile0 := hp.mem_iff.mp (by simp)
    have hb : b ∈ pile0 := hp.mem_iff.mp (by simp)
    have hc : c ∈ pile0 := hp.mem_iff.mp (by simp)
    have hd : d ∈ pile0 := hp.mem_iff.mp (by simp)
    simp only [pile0, ci3, ci4, ci7, ci8, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at ha hb hc hd
    have hnd : [a, b, c, d].Nodup := hp.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or, List.not_mem_nil, not_false_eq_true, and_true, and_self] at hnd
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
      rcases hp1 with rfl | rfl <;>
      first
      | exact h00a o h0 h1 | exact h00b o h0 h1 | exact h01a o h0 h1 | exact h01b o h0 h1
      | exact h02a o h0 h1 | exact h02b o h0 h1 | exact h03a o h0 h1 | exact h03b o h0 h1
      | exact h04a o h0 h1 | exact h04b o h0 h1 | exact h05a o h0 h1 | exact h05b o h0 h1
      | exact h06a o h0 h1 | exact h06b o h0 h1 | exact h07a o h0 h1 | exact h07b o h0 h1
      | exact h08a o h0 h1 | exact h08b o h0 h1 | exact h09a o h0 h1 | exact h09b o h0 h1
      | exact h10a o h0 h1 | exact h10b o h0 h1 | exact h11a o h0 h1 | exact h11b o h0 h1
      | exact h12a o h0 h1 | exact h12b o h0 h1 | exact h13a o h0 h1 | exact h13b o h0 h1
      | exact h14a o h0 h1 | exact h14b o h0 h1 | exact h15a o h0 h1 | exact h15b o h0 h1
      | exact h16a o h0 h1 | exact h16b o h0 h1 | exact h17a o h0 h1 | exact h17b o h0 h1
      | exact h18a o h0 h1 | exact h18b o h0 h1 | exact h19a o h0 h1 | exact h19b o h0 h1
      | exact h20a o h0 h1 | exact h20b o h0 h1 | exact h21a o h0 h1 | exact h21b o h0 h1
      | exact h22a o h0 h1 | exact h22b o h0 h1 | exact h23a o h0 h1 | exact h23b o h0 h1

theorem ComboMantraDivine_guaranteed_infinite : GuaranteedInfiniteCombo cardDB cards enemy := by
  refine ⟨setupTrace, stateA, setup_ok, ?_⟩
  intro oracle hValid
  have hp0 := hValid 0 pile0
  have hp1 := perm_2_ci _ ci4 ci8 (by decide) (hValid 1 pile1)
  exact perm4_dispatch _ hp0 _ hp1 oracle rfl rfl

theorem proof : GuaranteedInfiniteCombo cardDB cards enemy := ComboMantraDivine_guaranteed_infinite

end ComboMantraDivine_L2
