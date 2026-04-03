/-
  Extended infinite combo proof targets beyond GuaranteedInfiniteCombo.

  These capture weaker notions of "infinite combo" with different quantifier orders,
  plus a realistic online model where the player can't see future shuffles.

  | Strength | Definition                 | Quantifier structure                         | Meaning                        |
  |----------|----------------------------|----------------------------------------------|--------------------------------|
  | Strongest| GuaranteedInfiniteCombo    | ∀oracle ∃trace, sameModAccum                 | Period-1 loop: exact state recurrence |
  | Strong   | RobustInfinite             | ∀oracle ∃strategy ∀N ∃K, damage > N          | Fixed strategy beats any HP    |
  | Medium   | UnboundedDamage            | ∀oracle ∀N ∃trace, damage > N                | Each HP target gets own trace  |
  | Realistic| OnlineUnboundedDamage      | ∃strategy(tree) ∀oracle ∀N, damage > N       | Blind to future shuffles       |

  The first three let the player see the oracle (offline optimization).
  OnlineUnboundedDamage is strictly harder: the strategy branches only at shuffle
  points, modeling a player who doesn't know future shuffle results.

  Implications:
    GuaranteedInfiniteCombo → RobustInfinite → UnboundedDamage
    OnlineUnboundedDamage → UnboundedDamage
-/
import StSVerify.Engine

/-! ## Offline targets (player sees the oracle) -/

/-- The player commits to a strategy (infinite action sequence) BEFORE knowing
    the damage target. For any N, running enough of the strategy exceeds N damage.
    Strategy depends on oracle but NOT on N. -/
def RobustInfinite (cardDB : CardName → CardDef)
    (cards : List (CardName × Nat)) (enemy : EnemyState) : Prop :=
  ∃ (setupTrace : List Action) (stateA : GameState),
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA
    ∧ ∀ (oracle : ShuffleOracle),
        validOracle oracle →
        ∃ (strategy : Nat → Action),
          ∀ (N : Nat),
            ∃ (K : Nat) (stateB : GameState) (finalIdx : Nat),
              executeL2 cardDB oracle 0 stateA ((List.range K).map strategy) = some (stateB, finalIdx)
              ∧ noEndTurn ((List.range K).map strategy) = true
              ∧ stateB.damage > stateA.damage + N

/-- For any damage target N, the player can exceed it.
    The trace may depend on both N and the oracle (player has full foreknowledge). -/
def UnboundedDamage (cardDB : CardName → CardDef)
    (cards : List (CardName × Nat)) (enemy : EnemyState) : Prop :=
  ∃ (setupTrace : List Action) (stateA : GameState),
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA
    ∧ ∀ (N : Nat) (oracle : ShuffleOracle),
        validOracle oracle →
        ∃ (trace : List Action) (stateB : GameState) (finalIdx : Nat),
          executeL2 cardDB oracle 0 stateA trace = some (stateB, finalIdx)
          ∧ noEndTurn trace = true
          ∧ stateB.damage > stateA.damage + N

/-! ## Online target (player blind to future shuffles) -/

/-- An adaptive strategy is a tree that branches at each shuffle point.
    Between shuffles, the player commits to a fixed action sequence.
    At each shuffle, the strategy observes the result (a permutation of the
    discard pile) and branches accordingly.

    This is a non-anticipatory (causal/adapted) strategy: the player's actions
    up to shuffle k depend only on shuffle results 0..k-1, never on future shuffles. -/
inductive AdaptiveStrategy where
  | done : AdaptiveStrategy
  | node (segment : List Action) (branch : List CardInstance → AdaptiveStrategy) : AdaptiveStrategy

/-- Execute an adaptive strategy against an oracle.
    Runs the segment actions, then on the next shuffle, uses the oracle result
    to pick the branch and continues recursively. -/
def executeAdaptive (cardDB : CardName → CardDef) (oracle : ShuffleOracle) (shIdx : Nat)
    (s : GameState) : AdaptiveStrategy → Option (GameState × Nat)
  | .done => some (autoDrain cardDB s, shIdx)
  | .node segment branch =>
    match executeL2 cardDB oracle shIdx s segment with
    | none => none
    | some (s', shIdx') =>
      let lastResult := if shIdx' > shIdx
        then oracle (shIdx' - 1) (autoDrain cardDB s').discardPile
        else []
      executeAdaptive cardDB oracle shIdx' s' (branch lastResult)

/-- The player has an adaptive strategy (tree branching at shuffles)
    that deals unbounded damage against ANY oracle. The strategy is non-anticipatory:
    actions before shuffle k depend only on results of shuffles 0..k-1.

    This models the real Slay the Spire game where the player doesn't know
    what cards will be drawn next. Strictly harder than UnboundedDamage, where
    the trace can depend on the entire oracle (offline optimization). -/
def OnlineUnboundedDamage (cardDB : CardName → CardDef)
    (cards : List (CardName × Nat)) (enemy : EnemyState) : Prop :=
  ∃ (setupTrace : List Action) (stateA : GameState),
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA
    ∧ ∃ (strategy : AdaptiveStrategy),
        ∀ (N : Nat) (oracle : ShuffleOracle),
          validOracle oracle →
          ∃ (stateB : GameState) (finalIdx : Nat),
            executeAdaptive cardDB oracle 0 stateA strategy = some (stateB, finalIdx)
            ∧ stateB.damage > stateA.damage + N

/-! ## Implications -/

/-- GuaranteedInfiniteCombo → RobustInfinite (sorry: requires loop iteration + strategy construction). -/
theorem guaranteed_implies_robust (cardDB : CardName → CardDef)
    (cards : List (CardName × Nat)) (enemy : EnemyState) :
    GuaranteedInfiniteCombo cardDB cards enemy → RobustInfinite cardDB cards enemy := by
  sorry

/-- RobustInfinite → UnboundedDamage (trivial: instantiate N before picking trace). -/
theorem robust_implies_unbounded (cardDB : CardName → CardDef)
    (cards : List (CardName × Nat)) (enemy : EnemyState) :
    RobustInfinite cardDB cards enemy → UnboundedDamage cardDB cards enemy := by
  intro ⟨setupTrace, stateA, h_setup, h_robust⟩
  exact ⟨setupTrace, stateA, h_setup, fun N oracle hValid => by
    obtain ⟨strategy, h_strat⟩ := h_robust oracle hValid
    obtain ⟨K, stateB, finalIdx, h_exec, h_noend, h_dmg⟩ := h_strat N
    exact ⟨(List.range K).map strategy, stateB, finalIdx, h_exec, h_noend, h_dmg⟩⟩

/-- OnlineUnboundedDamage → UnboundedDamage.
    An adaptive strategy that works against all oracles can be instantiated with
    any specific oracle to produce a concrete trace. -/
theorem online_implies_unbounded (cardDB : CardName → CardDef)
    (cards : List (CardName × Nat)) (enemy : EnemyState) :
    OnlineUnboundedDamage cardDB cards enemy → UnboundedDamage cardDB cards enemy := by
  sorry
