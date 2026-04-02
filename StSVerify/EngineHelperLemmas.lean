/-
  Helper lemmas about the L2 engine (oracle bridge framework).
  These are properties of drawCardL2/stepL2/executeL2, not part of the engine itself.
-/
import StSVerify.Engine

/-- If two shuffle oracles agree on all inputs, `executeL2` produces the same result. -/
theorem executeL2_oracle_ext
    (cardDB : CardName → CardDef)
    (oracle1 oracle2 : ShuffleOracle) (shIdx : Nat) (s : GameState) (trace : List Action)
    (h : ∀ n pile, oracle1 n pile = oracle2 n pile) :
    executeL2 cardDB oracle1 shIdx s trace = executeL2 cardDB oracle2 shIdx s trace := by
  have : oracle1 = oracle2 := funext (fun n => funext (fun pile => h n pile))
  subst this
  rfl

/-- If two oracles agree on (shIdx, s.discardPile), drawCardL2 gives the same result.
    This is the key building block for oracle bridge proofs: the oracle only appears
    once in drawCardL2, at `oracle shIdx s.discardPile`. -/
theorem drawCardL2_oracle_agree (oracle1 oracle2 : ShuffleOracle) (shIdx : Nat)
    (s : GameState) (cardId : CId)
    (h : oracle1 shIdx s.discardPile = oracle2 shIdx s.discardPile) :
    drawCardL2 oracle1 shIdx s cardId = drawCardL2 oracle2 shIdx s cardId := by
  unfold drawCardL2
  simp only [h]

/-- stepL2 agrees when oracles agree on (shIdx, s.discardPile). -/
theorem stepL2_oracle_agree (cardDB : CardName → CardDef)
    (oracle1 oracle2 : ShuffleOracle) (shIdx : Nat) (s : GameState) (a : Action)
    (h : oracle1 shIdx s.discardPile = oracle2 shIdx s.discardPile) :
    stepL2 cardDB oracle1 shIdx s a = stepL2 cardDB oracle2 shIdx s a := by
  unfold stepL2
  cases a with
  | draw c => exact drawCardL2_oracle_agree oracle1 oracle2 shIdx s c h
  | _ => rfl

/-- When drawPile is non-empty, drawCardL2 does not call the oracle,
    so the result is the same for any two oracles. -/
theorem drawCardL2_nonempty_irrel (oracle1 oracle2 : ShuffleOracle) (shIdx : Nat)
    (s : GameState) (cardId : CId) (h : s.drawPile ≠ []) :
    drawCardL2 oracle1 shIdx s cardId = drawCardL2 oracle2 shIdx s cardId := by
  unfold drawCardL2
  have h_cond : ¬ ((s.drawPile.length == 0 && decide (s.discardPile.length > 0)) = true) := by
    intro hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact h (List.length_eq_zero.mp hc.1)
  have h_ft : ¬ (false = true) := by decide
  simp only [if_neg h_cond, if_neg h_ft]

/-- stepL2 agrees when either (a) drawPile is non-empty (oracle irrelevant)
    or (b) oracles agree on (shIdx, s.discardPile). -/
theorem stepL2_oracle_cond (cardDB : CardName → CardDef)
    (oracle1 oracle2 : ShuffleOracle) (shIdx : Nat) (s : GameState) (a : Action)
    (h : s.drawPile ≠ [] ∨ oracle1 shIdx s.discardPile = oracle2 shIdx s.discardPile) :
    stepL2 cardDB oracle1 shIdx s a = stepL2 cardDB oracle2 shIdx s a := by
  unfold stepL2
  cases a with
  | draw c =>
    cases h with
    | inl h => exact drawCardL2_nonempty_irrel oracle1 oracle2 shIdx s c h
    | inr h => exact drawCardL2_oracle_agree oracle1 oracle2 shIdx s c h
  | _ => rfl

/-- Recursive condition: at each step along o1's execution, either
    drawPile is non-empty (oracle irrelevant) or the two oracles agree on discardPile.
    Used to prove oracle bridge lemmas. -/
def oraclesCond (cardDB : CardName → CardDef) (o1 o2 : ShuffleOracle)
    (si : Nat) (s : GameState) : List Action → Prop
  | [] => True
  | a :: rest =>
    let s_clean := resolveInUse cardDB (autoDrain cardDB s)
    (s_clean.drawPile ≠ [] ∨ o1 si s_clean.discardPile = o2 si s_clean.discardPile)
    ∧ match stepL2 cardDB o1 si s_clean a with
      | some (s', si') => oraclesCond cardDB o1 o2 si' s' rest
      | none => True

/-- If oraclesCond holds, executeL2 gives the same result for both oracles.
    This is the general oracle bridge: thread-by-thread simulation. -/
theorem executeL2_oraclesCond (cardDB : CardName → CardDef) (o1 o2 : ShuffleOracle)
    (si : Nat) (s : GameState) (trace : List Action)
    (h : oraclesCond cardDB o1 o2 si s trace) :
    executeL2 cardDB o1 si s trace = executeL2 cardDB o2 si s trace := by
  induction trace generalizing si s with
  | nil => rfl
  | cons a rest ih =>
    simp only [oraclesCond] at h
    obtain ⟨h_cond, h_rest⟩ := h
    have h_eq : stepL2 cardDB o1 si (resolveInUse cardDB (autoDrain cardDB s)) a =
                stepL2 cardDB o2 si (resolveInUse cardDB (autoDrain cardDB s)) a :=
      stepL2_oracle_cond cardDB o1 o2 si _ a h_cond
    change (let sc := resolveInUse cardDB (autoDrain cardDB s)
            match stepL2 cardDB o1 si sc a with
            | none => none | some (s', si') => executeL2 cardDB o1 si' s' rest) =
           (let sc := resolveInUse cardDB (autoDrain cardDB s)
            match stepL2 cardDB o2 si sc a with
            | none => none | some (s', si') => executeL2 cardDB o2 si' s' rest)
    simp only [h_eq]
    cases h_match : stepL2 cardDB o2 si (resolveInUse cardDB (autoDrain cardDB s)) a with
    | none => rfl
    | some p =>
      have h_o1 : stepL2 cardDB o1 si (resolveInUse cardDB (autoDrain cardDB s)) a = some p :=
        h_eq ▸ h_match
      simp only [h_o1] at h_rest
      exact ih p.2 p.1 h_rest
