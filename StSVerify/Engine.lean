/-
  Core types, game state, and engine.  (v2: unified CardInstance system)
-/

import StSVerify.CardId

/-! ## Card Instance

  A CardInstance is a specific copy of a card in the game.
  Tokens (Shiv, Miracle, etc.) are also CardInstances, created dynamically.
  Cost and damage are mutable per-instance (for Madness, Streamline, Claw scaling).
-/

structure CardInstance where
  id     : Nat        -- unique identity (for trace references)
  name   : CardName   -- card type
  cost   : Nat        -- CURRENT cost (mutable, starts from CardDef.cost)
  damage : Nat        -- CURRENT base damage (mutable, for Claw scaling)
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev CId := Nat  -- shorthand for card instance IDs used in Action traces

/-! ## Stances & Orbs -/

inductive Stance where
  | Neutral | Calm | Wrath | Divine
  deriving Repr, DecidableEq, BEq, Inhabited

inductive Orb where
  | Lightning | Frost | Dark | Plasma
  deriving Repr, DecidableEq, BEq, Inhabited

/-! ## Enemy State (set by combo as parameters) -/

structure EnemyState where
  vulnerable : Nat
  weak       : Nat
  intending  : Bool   -- is enemy intending to attack?
  deriving Repr, DecidableEq, BEq, Inhabited

/-! ## Card Effect System -/

inductive CardEffect where
  -- Basic
  | dealDamage (n : Nat)
  | gainBlock (n : Nat)
  | drawCards (n : Nat)
  | discardCards (n : Nat)
  | gainEnergy (n : Nat)
  | exhaustSelf
  | shuffleSelf               -- card goes to draw pile instead of discard (Tantrum)
  -- Debuffs
  | applyVulnerable (n : Nat)
  | applyWeak (n : Nat)
  -- Conditional (flat)
  | ifVulnerableGainEnergy (n : Nat)
  | ifVulnerableDrawCards (n : Nat)
  | ifWeakGainEnergy (n : Nat)
  | ifWeakDrawCards (n : Nat)
  | ifEnemyAttackingEnterStance (s : Stance)
  | ifInStanceDrawCards (s : Stance) (n : Nat)
  | ifNotInStanceEnter (s : Stance)            -- InnerPeace else, Indignation
  | ifInStanceApplyVulnerable (s : Stance) (n : Nat)  -- Indignation in Wrath
  -- Stance (Watcher)
  | enterStance (s : Stance)
  | exitStance
  -- Orbs (Defect)
  | channelOrb (o : Orb)
  | gainFocus (n : Nat)       -- Defragment+, Biased Cognition+
  | gainOrbSlots (n : Nat)    -- Capacitor+
  -- Tokens
  | addTokensToHand (token : CardName) (n : Nat)
  | addTokenToDiscard (token : CardName)
  | addTokenToDrawPile (token : CardName)
  -- Special
  | clawScaling               -- +2 to all Claw instances' damage
  | allForOneRetrieve         -- retrieve all 0-cost from discard (choice in trace)
  | hologramRetrieve          -- retrieve 1 from discard (choice in trace)
  | exhaustFromHand (n : Nat) -- Burning Pact, True Grit: set toExhaust
  | discardAllHandAndDraw     -- Calculated Gamble: discard all hand, toDraw = count
  | shuffleHandIntoDraw       -- Reboot: move hand to draw pile
  | drawToFull (max : Nat)    -- Scrawl: toDraw = max - hand.length
  | setNoDraw                 -- Battle Trance: no more draws this turn
  | setCorruption             -- Corruption: all skills cost 0 and exhaust
  | costReduceSelf (n : Nat)  -- Streamline: reduce own cost after play
  | secondWind (blockPer : Nat) -- Second Wind: exhaust all non-attacks, gain block
  | requireEmptyDrawPile      -- Grand Finale: precondition, checked in playCard
  | stormOfSteel (token : CardName) -- Storm of Steel: discard hand, add 1 token per card
  deriving Repr, DecidableEq, BEq

/-! ## Queue System -/

/-- Priority for on-discard triggers in the action queue.
    top = fires before remaining discards (Tactician: energy gain)
    bottom = fires after all discards complete (Reflex: draw cards) -/
inductive QueuePriority where
  | top | bottom
  deriving Repr, DecidableEq, BEq

/-- Items in the action queue. Some need player input, some auto-resolve. -/
inductive QueueItem where
  | draw                      -- draw 1 card (player chooses which / top in L2)
  | discardChoice             -- player chooses which card to discard from hand
  | exhaustChoice             -- player chooses which card to exhaust from hand
  | discardSpecific (c : CId) -- auto: discard this specific card (Storm right-to-left)
  | resolveCard (c : CId)     -- auto: move played card from inUse to destination (discard/exhaust/drawPile)
  deriving Repr, DecidableEq, BEq

/-! ## Card Definition (static, looked up by CardName from cardDB) -/

structure CardDef where
  cost      : Nat
  playable  : Bool
  isAttack  : Bool
  isSkill   : Bool
  isPower   : Bool
  effects   : List CardEffect
  /-- Trigger when discarded from hand -/
  onDiscard : List CardEffect
  /-- Priority: where onDiscard effects are inserted in queue -/
  onDiscardPriority : QueuePriority
  /-- Trigger when drawn -/
  onDraw    : List CardEffect
  /-- Trigger when exhausted -/
  onExhaust : List CardEffect
  deriving Repr, DecidableEq, BEq

/-! ## Game State (v2: unified CardInstance system) -/

structure GameState where
  hand        : List CardInstance
  drawPile    : List CardInstance
  discardPile : List CardInstance
  exhaustPile : List CardInstance
  inUse       : List CardInstance   -- cards being played (replaces limbo)
  actionQueue : List QueueItem
  energy      : Nat
  damage      : Nat
  block       : Nat
  stance      : Stance
  orbs        : List Orb
  orbSlots    : Nat
  focus       : Int
  enemy       : EnemyState
  activePowers : List CardName
  nextId      : Nat                 -- for dynamic card creation (tokens)
  noDraw      : Bool
  corruptionActive : Bool
  deriving Repr, DecidableEq, BEq, Inhabited

/-! ## CardInstance Utilities -/

/-- Extract the base damage from a CardDef's effects (first dealDamage value, or 0) -/
def CardDef.dealsDamage (d : CardDef) : Nat :=
  match d.effects.find? (fun e => match e with | .dealDamage _ => true | _ => false) with
  | some (.dealDamage n) => n
  | _ => 0

/-- Create a CardInstance from a CardDef -/
def mkCardInstance (id : Nat) (name : CardName) (def_ : CardDef) : CardInstance :=
  { id := id, name := name, cost := def_.cost, damage := def_.dealsDamage }

/-- Card key for normalized comparison (ignoring id) -/
def cardKey (c : CardInstance) : (CardName × Nat × Nat) := (c.name, c.cost, c.damage)

/-! ## List Utilities -/

def List.remove1 [BEq α] (xs : List α) (x : α) : List α :=
  match xs with
  | [] => []
  | y :: ys => if x == y then ys else y :: List.remove1 ys x

def List.has [BEq α] (xs : List α) (x : α) : Bool :=
  xs.any (· == x)

/-! ## CardInstance pile operations -/

/-- Find a CardInstance by id in a pile -/
def findById (pile : List CardInstance) (id : Nat) : Option CardInstance :=
  pile.find? (fun c => c.id == id)

/-- Check if a pile contains a card with given id -/
def pileHas (pile : List CardInstance) (id : Nat) : Bool :=
  pile.any (fun c => c.id == id)

/-- Remove first card with given id from pile -/
def removeById (pile : List CardInstance) (id : Nat) : List CardInstance :=
  match pile with
  | [] => []
  | c :: cs => if c.id == id then cs else c :: removeById cs id

/-- Update all cards matching a predicate across a pile -/
def updateAll (pile : List CardInstance) (pred : CardInstance → Bool)
    (f : CardInstance → CardInstance) : List CardInstance :=
  pile.map (fun c => if pred c then f c else c)

/-- Update Claw damage across all piles: add 2 to every Claw instance -/
def updateClawsInPile (pile : List CardInstance) : List CardInstance :=
  pile.map (fun c => if c.name == CardName.ClawPlus then { c with damage := c.damage + 2 } else c)

/-! ## Token creation -/

/-- Create N token CardInstances starting at the given nextId -/
def mkTokens (cardDB : CardName → CardDef) (name : CardName) (n : Nat) (startId : Nat)
    : List CardInstance :=
  let def_ := cardDB name
  (List.range n).map fun i =>
    { id := startId + i, name := name, cost := def_.cost, damage := def_.dealsDamage }

/-! ## Resolve inUse: move a specific card from inUse to its destination -/

/-- Resolve a single card from inUse: move it to discard, exhaust, or drawPile.
    Called when `.resolveCard cardId` is processed from the action queue. -/
def resolveOneCard (cardDB : CardName → CardDef) (s : GameState) (cardId : CId)
    : GameState :=
  match findById s.inUse cardId with
  | none => s  -- card not found in inUse, no-op
  | some card =>
    let def_ := cardDB card.name
    let shouldExh := def_.effects.any (· == .exhaustSelf)
                     || (s.corruptionActive && def_.isSkill)
    let shouldShuffle := def_.effects.any (· == .shuffleSelf)
    let inUse' := removeById s.inUse cardId
    if shouldExh then
      { s with inUse := inUse', exhaustPile := card :: s.exhaustPile }
    else if shouldShuffle then
      { s with inUse := inUse', drawPile := card :: s.drawPile }
    else
      { s with inUse := inUse', discardPile := card :: s.discardPile }

/-! ## Queue helpers -/

/-- Convert card effects to queue items -/
def effectsToQueue (effects : List CardEffect) : List QueueItem :=
  effects.foldl (fun acc eff =>
    match eff with
    | .drawCards n => acc ++ List.replicate n .draw
    | .discardCards n => acc ++ List.replicate n .discardChoice
    | .exhaustFromHand n => acc ++ List.replicate n .exhaustChoice
    | _ => acc) []

/-- Insert items into queue at given priority position -/
def insertQueue (queue : List QueueItem) (items : List QueueItem)
    (priority : QueuePriority) : List QueueItem :=
  match priority with
  | .top => items ++ queue
  | .bottom => queue ++ items

/-! ## Power count -/

/-- Count active power copies -/
def powerCount (s : GameState) (p : CardName) : Nat :=
  s.activePowers.filter (· == p) |>.length

/-! ## Damage calculation -/

/-- Apply damage with multipliers -/
def applyDamage (s : GameState) (baseDmg : Nat) (isAttack : Bool) : Nat :=
  let stanceMult := match s.stance with
    | .Wrath => 2 | .Divine => 3 | _ => 1
  let vulnMult := if isAttack && s.enemy.vulnerable > 0 then 3 else 2  -- 3/2 = 1.5x
  let scaled := if isAttack then baseDmg * stanceMult * vulnMult / 2
                else baseDmg
  scaled

/-! ## Fire on-discard trigger -/

/-- Process a card entering the discard pile: fire onDiscard trigger. -/
def fireOnDiscard (cardDB : CardName → CardDef) (s : GameState) (card : CardInstance)
    : GameState :=
  let def_ := cardDB card.name
  if def_.onDiscard.length == 0 then s
  else
    -- Apply immediate effects (energy gain, etc.)
    let s' := def_.onDiscard.foldl (fun acc eff =>
      match eff with
      | .gainEnergy n => { acc with energy := acc.energy + n }
      | .gainBlock n => { acc with block := acc.block + n }
      | _ => acc) s
    -- Enqueue draw/discard items
    let queueItems := effectsToQueue def_.onDiscard
    { s' with actionQueue := insertQueue s'.actionQueue queueItems def_.onDiscardPriority }

/-! ## Auto-drain discardSpecific items -/

/-- Auto-drain discardSpecific items from front of queue.
    Each discard moves the card from hand to discard pile and fires triggers.
    Uses a fuel parameter for termination. -/
-- actionQueue is not decrease only, so we
def autoDrain (cardDB : CardName → CardDef) (s : GameState) (fuel : Nat := 100)
    : GameState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.actionQueue with
    | .discardSpecific cid :: rest =>
      match findById s.hand cid with
      | some card =>
        let s' := { s with
          hand := removeById s.hand cid
          discardPile := card :: s.discardPile
          actionQueue := rest }
        let s'' := fireOnDiscard cardDB s' card
        autoDrain cardDB s'' fuel'
      | none => s  -- card not found, stop
    | .resolveCard cid :: rest =>
      let s' := resolveOneCard cardDB { s with actionQueue := rest } cid
      autoDrain cardDB s' fuel'
    | _ => s

/-! ## Actions -/

inductive Action where
  /-- Play a card from hand -/
  | play (card : CId)
  /-- Draw a specific card from draw pile (auto-shuffles if needed) -/
  | draw (card : CId)
  /-- Skip remaining draws when both piles empty -/
  | failDraw
  /-- Discard a specific card from hand (resolves discardChoice in queue) -/
  | discard (card : CId)
  /-- Exhaust a specific card from hand (resolves exhaustChoice in queue) -/
  | exhaust (card : CId)
  /-- Resolve draw trigger for a card (Deus Ex Machina, Void) -/
  | resolveDrawTrigger (card : CId)
  /-- Change stance (Watcher) -/
  | changeStance (to : Stance)
  /-- Resolve Rushdown trigger -/
  | resolveRushdown
  /-- Auto-play Flurry of Blows from discard -/
  | autoPlayFlurry (card : CId)
  /-- Hologram: choose which card to retrieve from discard -/
  | hologramChoose (card : CId)
  /-- All for One: specify which 0-cost cards to retrieve -/
  | allForOneChoose (cards : List CId)
  /-- Recycle: choose which card to exhaust for energy -/
  | recycleChoose (card : CId)
  /-- Calculated Gamble: resolve (discard all, draw equal) -/
  | resolveGamble
  /-- End turn: discard hand, reset energy, draw 5 next turn -/
  | endTurn
  deriving Repr, DecidableEq, BEq

/-! ## Engine -/

/-- Get effective cost of a CardInstance (Corruption overrides skill cost to 0) -/
def effectiveCost (cardDB : CardName → CardDef) (s : GameState) (card : CardInstance) : Nat :=
  let def_ := cardDB card.name
  if s.corruptionActive && def_.isSkill then 0
  else card.cost

/-- Does a card exhaust on play? -/
def shouldExhaust (cardDB : CardName → CardDef) (s : GameState) (card : CardInstance) : Bool :=
  let def_ := cardDB card.name
  def_.effects.any (· == .exhaustSelf)
  || (s.corruptionActive && def_.isSkill)

/-- Does a card shuffle itself into draw pile? -/
def shouldShuffleSelf (cardDB : CardName → CardDef) (card : CardInstance) : Bool :=
  let def_ := cardDB card.name
  def_.effects.any (· == .shuffleSelf)

/-- Process a single CardEffect on the state -/
def processEffect (cardDB : CardName → CardDef) (s : GameState) (eff : CardEffect)
    (isAttack : Bool) : GameState :=
  match eff with
  | .dealDamage n =>
      let actual := applyDamage s n isAttack
      { s with damage := s.damage + actual }
  | .gainBlock n => { s with block := s.block + n }
  | .drawCards n => { s with actionQueue := s.actionQueue ++ List.replicate n .draw }
  | .discardCards n => { s with actionQueue := s.actionQueue ++ List.replicate n .discardChoice }
  | .gainEnergy n => { s with energy := s.energy + n }
  | .applyVulnerable n => { s with enemy := { s.enemy with vulnerable := s.enemy.vulnerable + n } }
  | .applyWeak n => { s with enemy := { s.enemy with weak := s.enemy.weak + n } }
  | .clawScaling =>
      -- Update ALL Claw instances in ALL piles: damage += 2
      { s with
        hand := updateClawsInPile s.hand
        drawPile := updateClawsInPile s.drawPile
        discardPile := updateClawsInPile s.discardPile
        exhaustPile := updateClawsInPile s.exhaustPile
        inUse := updateClawsInPile s.inUse }
  | .setNoDraw => { s with noDraw := true }
  | .channelOrb o =>
      if s.orbs.length >= s.orbSlots then
        { s with orbs := s.orbs.drop 1 ++ [o] }
      else
        { s with orbs := s.orbs ++ [o] }
  | .ifVulnerableGainEnergy n =>
      if s.enemy.vulnerable > 0 then { s with energy := s.energy + n } else s
  | .ifVulnerableDrawCards n =>
      if s.enemy.vulnerable > 0 then { s with actionQueue := s.actionQueue ++ List.replicate n .draw } else s
  | .ifWeakGainEnergy n =>
      if s.enemy.weak > 0 then { s with energy := s.energy + n } else s
  | .ifWeakDrawCards n =>
      if s.enemy.weak > 0 then { s with actionQueue := s.actionQueue ++ List.replicate n .draw } else s
  | .ifEnemyAttackingEnterStance st =>
      if s.enemy.intending && s.stance != st then
        let exitE := match s.stance with | .Calm => 2 | _ => 0
        let mfB := powerCount s CardName.MentalFortressPlus * 6
        { s with stance := st, energy := s.energy + exitE, block := s.block + mfB }
      else s
  | .ifInStanceDrawCards st n =>
      if s.stance == st then { s with actionQueue := s.actionQueue ++ List.replicate n .draw } else s
  | .ifNotInStanceEnter st =>
      if s.stance != st then
        let exitE := match s.stance with | .Calm => 2 | _ => 0
        let mfB := powerCount s CardName.MentalFortressPlus * 6
        { s with stance := st, energy := s.energy + exitE, block := s.block + mfB }
      else s
  | .ifInStanceApplyVulnerable st n =>
      if s.stance == st then { s with enemy := { s.enemy with vulnerable := s.enemy.vulnerable + n } } else s
  -- Stance (with exit effects)
  | .enterStance st =>
      if s.stance == st then s
      else
        let exitE := match s.stance with | .Calm => 2 | _ => 0
        let mfB := powerCount s CardName.MentalFortressPlus * 6
        { s with stance := st, energy := s.energy + exitE, block := s.block + mfB }
  | .exitStance =>
      if s.stance == .Neutral then s
      else
        let exitE := match s.stance with | .Calm => 2 | _ => 0
        let mfB := powerCount s CardName.MentalFortressPlus * 6
        { s with stance := .Neutral, energy := s.energy + exitE, block := s.block + mfB }
  -- Orbs / Focus
  | .gainFocus n => { s with focus := s.focus + Int.ofNat n }
  | .gainOrbSlots n => { s with orbSlots := s.orbSlots + n }
  -- Tokens: create CardInstances dynamically
  | .addTokensToHand name n =>
      let tokens := mkTokens cardDB name n s.nextId
      { s with hand := tokens ++ s.hand, nextId := s.nextId + n }
  | .addTokenToDiscard name =>
      let tok := mkCardInstance s.nextId name (cardDB name)
      { s with discardPile := tok :: s.discardPile, nextId := s.nextId + 1 }
  | .addTokenToDrawPile name =>
      let tok := mkCardInstance s.nextId name (cardDB name)
      { s with drawPile := tok :: s.drawPile, nextId := s.nextId + 1 }
  -- Calculated Gamble: enqueue right-to-left discards for each hand card, then draws
  | .discardAllHandAndDraw =>
      let count := s.hand.length
      let discards := s.hand.reverse.map (fun c => QueueItem.discardSpecific c.id)
      { s with
        actionQueue := s.actionQueue ++ discards ++ List.replicate count .draw }
  -- Reboot: shuffle hand into draw pile
  | .shuffleHandIntoDraw =>
      { s with
        drawPile := s.hand ++ s.drawPile
        hand := [] }
  -- Scrawl: draw until hand = max
  | .drawToFull max =>
      let needed := if max > s.hand.length then max - s.hand.length else 0
      { s with actionQueue := s.actionQueue ++ List.replicate needed .draw }
  -- Corruption: set flag
  | .setCorruption => { s with corruptionActive := true }
  -- Second Wind: exhaust all non-attacks, gain block per card
  | .secondWind blockPer =>
      let nonAttacks := s.hand.filter (fun c => !(cardDB c.name).isAttack)
      let attacks := s.hand.filter (fun c => (cardDB c.name).isAttack)
      let count := nonAttacks.length
      let darkDraws := count * powerCount s CardName.DarkEmbracePlus
      let fnpBlock := count * powerCount s CardName.FeelNoPainPlus * 4
      { s with
        hand := attacks
        exhaustPile := nonAttacks ++ s.exhaustPile
        block := s.block + blockPer * count + fnpBlock
        actionQueue := s.actionQueue ++ List.replicate darkDraws .draw }
  -- Storm of Steel: enqueue right-to-left discards, create tokens in hand
  | .stormOfSteel token =>
      let count := s.hand.length
      let discards := s.hand.reverse.map (fun c => QueueItem.discardSpecific c.id)
      let tokens := mkTokens cardDB token count s.nextId
      { s with
        hand := tokens ++ s.hand
        nextId := s.nextId + count
        actionQueue := s.actionQueue ++ discards }
  -- Effects handled elsewhere (playCard checks these)
  | .exhaustSelf | .shuffleSelf | .exhaustFromHand _
  | .allForOneRetrieve | .hologramRetrieve
  | .costReduceSelf _ | .requireEmptyDrawPile => s

/-- Play a card from hand -/
def playCard (cardDB : CardName → CardDef) (s : GameState) (cardId : CId)
    : Option GameState :=
  match findById s.hand cardId with
  | none => none
  | some card =>
    let def_ := cardDB card.name
    let cost := effectiveCost cardDB s card
    -- Grand Finale precondition
    let grandFinaleOk := if def_.effects.any (· == .requireEmptyDrawPile)
                          then s.drawPile.length == 0
                          else true
    if s.actionQueue.length == 0 && s.inUse.length == 0
       && def_.playable && s.energy >= cost && grandFinaleOk then
      -- Remove from hand, pay cost
      let s1 := { s with
        hand := removeById s.hand cardId
        energy := s.energy - cost
      }
      -- Adjust damage for this play: Accuracy bonus for Shivs
      let accuracyBonus := if card.name == CardName.Shiv
                            && s1.activePowers.has CardName.AccuracyPlus then 6 else 0
      -- Use the instance's current damage (includes Claw scaling already)
      let adjustedEffects := def_.effects.map fun eff =>
        match eff with
        | .dealDamage _ => .dealDamage (card.damage + accuracyBonus)
        | other => other
      -- Process effects
      let s2 := adjustedEffects.foldl
        (fun acc eff => processEffect cardDB acc eff def_.isAttack) s1
      -- Enqueue exhaustFromHand effects
      let exhaustCount := def_.effects.foldl (fun acc eff =>
        match eff with | .exhaustFromHand n => acc + n | _ => acc) 0
      let s2b := { s2 with actionQueue := s2.actionQueue ++ List.replicate exhaustCount QueueItem.exhaustChoice }
      -- Set noDraw flag
      let s2c := if def_.effects.any (· == .setNoDraw) then { s2b with noDraw := true } else s2b
      -- Card destination: powers go immediately, others go to inUse + queue resolveCard
      let s3 := if def_.isPower then
          { s2c with activePowers := card.name :: s2c.activePowers }
        else
          { s2c with inUse := card :: s2c.inUse,
                     actionQueue := s2c.actionQueue ++ [.resolveCard cardId] }
      -- Per-card-played hooks (After Image, A Thousand Cuts)
      let aiBlock := if s3.activePowers.has CardName.AfterImage then 1 else 0
      let atcDmg := if s3.activePowers.has CardName.AThousandCuts then 1 else 0
      let s4 := { s3 with block := s3.block + aiBlock, damage := s3.damage + atcDmg }
      -- Corruption: set flag when played
      let s5 := if card.name == CardName.Corruption then { s4 with corruptionActive := true } else s4
      -- Cost reduce self (Streamline): modify the instance's cost in inUse
      let s6 := def_.effects.foldl (fun acc eff =>
        match eff with
        | .costReduceSelf n =>
            let cur := card.cost
            let newCost := if cur >= n then cur - n else 0
            { acc with inUse := acc.inUse.map (fun c =>
                if c.id == cardId then { c with cost := newCost } else c) }
        | _ => acc) s5
      -- Dark Embrace / Feel No Pain for exhaust-self
      let s7 := if shouldExhaust cardDB s card then
          let deDraw := powerCount s6 CardName.DarkEmbracePlus
          let fnpBlock := powerCount s6 CardName.FeelNoPainPlus * 4
          { s6 with actionQueue := s6.actionQueue ++ List.replicate deDraw .draw, block := s6.block + fnpBlock }
        else s6
      some s7
    else
      none

/-- Draw a card (auto-shuffle if needed). -/
def drawCard (s : GameState) (cardId : CId) : Option GameState :=
  match s.actionQueue with
  | .draw :: rest =>
    if s.noDraw || s.hand.length >= 10 then none
    else
      -- Auto-shuffle if draw pile empty
      let s' := if s.drawPile.length == 0 && s.discardPile.length > 0 then
          { s with
            drawPile := s.discardPile, discardPile := [] }
        else s
      match findById s'.drawPile cardId with
      | some card =>
        some { s' with
          hand := card :: s'.hand
          drawPile := removeById s'.drawPile cardId
          actionQueue := rest
        }
      | none => none
  | _ => none

/-- Fail draw: skip remaining draws -/
def failDraw (s : GameState) : Option GameState :=
  match s.actionQueue with
  | .draw :: _ =>
    let handFull := s.hand.length >= 10
    let pilesEmpty := s.drawPile.length == 0 && s.discardPile.length == 0
    if pilesEmpty || handFull then
      let remaining := s.actionQueue.dropWhile (· == .draw)
      some { s with actionQueue := remaining }
    else none
  | _ => none

/-- Discard from hand (resolves discardChoice in queue).
    Fires onDiscard triggers automatically. -/
def discardFromHand (cardDB : CardName → CardDef) (s : GameState) (cardId : CId)
    : Option GameState :=
  match s.actionQueue with
  | .discardChoice :: rest =>
    match findById s.hand cardId with
    | some card =>
      let s' := { s with
        hand := removeById s.hand cardId
        discardPile := card :: s.discardPile
        actionQueue := rest }
      some (fireOnDiscard cardDB s' card)
    | none => none
  | _ => none

/-- Exhaust from hand (resolves exhaustChoice in queue) -/
def exhaustFromHand (s : GameState) (cardId : CId) : Option GameState :=
  match s.actionQueue with
  | .exhaustChoice :: rest =>
    match findById s.hand cardId with
    | some card =>
      let darkDraws := powerCount s CardName.DarkEmbracePlus
      let fnpBlock := powerCount s CardName.FeelNoPainPlus * 4
      some { s with
        hand := removeById s.hand cardId
        exhaustPile := card :: s.exhaustPile
        actionQueue := rest ++ List.replicate darkDraws .draw
        block := s.block + fnpBlock
      }
    | none => none
  | _ => none

/-- Resolve draw trigger (Deus Ex Machina, Void) -/
def resolveDrawTrigger (cardDB : CardName → CardDef) (s : GameState) (cardId : CId)
    : Option GameState :=
  match findById s.hand cardId with
  | some card =>
    let def_ := cardDB card.name
    if def_.onDraw.length > 0 then
      let s' := def_.onDraw.foldl (fun acc eff => processEffect cardDB acc eff false) s
      if def_.effects.any (· == .exhaustSelf) || card.name == CardName.DeusExMachina || card.name == CardName.Void then
        some { s' with hand := removeById s'.hand cardId, exhaustPile := card :: s'.exhaustPile }
      else
        some s'
    else
      none
  | none => none

/-- Change stance (Watcher) -/
def changeStance (s : GameState) (to : Stance) : Option GameState :=
  if s.stance == to then none
  else
    let exitEnergy := match s.stance with
      | .Calm => 2 | _ => 0
    let mentalBlock := powerCount s CardName.MentalFortressPlus * 6
    some { s with
      stance := to
      energy := s.energy + exitEnergy
      block := s.block + mentalBlock
    }

/-- Resolve Rushdown trigger -/
def resolveRushdown (s : GameState) : Option GameState :=
  let count := powerCount s CardName.Rushdown
  if count > 0 && s.stance == .Wrath then
    some { s with actionQueue := s.actionQueue ++ List.replicate (count * 2) .draw }
  else
    none

/-- Auto-play Flurry of Blows from discard -/
def autoPlayFlurry (s : GameState) (cardId : CId) : Option GameState :=
  match findById s.discardPile cardId with
  | some card =>
    if card.name == CardName.FlurryOfBlowsPlus then
      let baseDmg : Nat := 6
      let actual := applyDamage s baseDmg true
      some { s with damage := s.damage + actual }
    else none
  | none => none

/-- Execute one action -/
def step (cardDB : CardName → CardDef) (s : GameState) (a : Action)
    : Option GameState :=
  match a with
  | .play card              => playCard cardDB s card
  | .draw card              => drawCard s card
  | .failDraw               => failDraw s
  | .discard card           => discardFromHand cardDB s card
  | .exhaust card           => exhaustFromHand s card
  | .resolveDrawTrigger card    => resolveDrawTrigger cardDB s card
  | .changeStance to        => changeStance s to
  | .resolveRushdown        => resolveRushdown s
  | .autoPlayFlurry card    => autoPlayFlurry s card
  | .endTurn =>
      if s.actionQueue.length == 0 && s.inUse.length == 0 then
        some { s with
          discardPile := s.hand ++ s.discardPile
          hand := []
          energy := 3
          block := 0
          actionQueue := List.replicate 5 .draw
          noDraw := false }
      else none
  | .hologramChoose card    =>
      match findById s.discardPile card with
      | some c => some { s with hand := c :: s.hand, discardPile := removeById s.discardPile card }
      | none => none
  | .allForOneChoose cards  =>
      let found := cards.filterMap (findById s.discardPile)
      if found.length == cards.length then
        let dp := cards.foldl (fun acc cid => removeById acc cid) s.discardPile
        some { s with hand := found ++ s.hand, discardPile := dp }
      else none
  | .recycleChoose card     =>
      match findById s.hand card with
      | some c =>
        let refund := c.cost
        some { s with
          hand := removeById s.hand card
          exhaustPile := c :: s.exhaustPile
          energy := s.energy + refund
        }
      | none => none
  | .resolveGamble => none  -- TODO: complex

/-! ## Trace Execution -/

def execute (cardDB : CardName → CardDef) (s : GameState)
    (trace : List Action) : Option GameState :=
  -- Auto-drain: process discardSpecific and resolveCard items
  let s := autoDrain cardDB s
  match trace with
  | [] => some s
  | a :: rest =>
    match step cardDB s a with
    | none => none
    | some s' => execute cardDB s' rest

/-! ## Loop Check -/

/-- Sort a list for set comparison -/
def List.sorted [Ord α] [BEq α] (xs : List α) : List α :=
  xs.mergeSort (fun a b => compare a b |>.isLT)

/-- Normalize a pile by card keys (name, cost, damage), sorted.
    Cards with same properties are interchangeable; id is ignored. -/
def normPileV2 (pile : List CardInstance) : List (CardName × Nat × Nat) :=
  (pile.map cardKey).mergeSort (fun a b =>
    match compare a.1 b.1 with
    | .lt => true
    | .gt => false
    | .eq => match compare a.2.1 b.2.1 with
             | .lt => true
             | .gt => false
             | .eq => decide (a.2.2 < b.2.2))

/-- Two states are "same modulo accumulating fields, card order, and card identity."
    Cards with the same (name, cost, damage) are interchangeable. -/
def sameModAccum (a b : GameState) : Bool :=
  normPileV2 a.hand == normPileV2 b.hand
  && normPileV2 a.drawPile == normPileV2 b.drawPile
  && normPileV2 a.discardPile == normPileV2 b.discardPile
  && normPileV2 a.inUse == normPileV2 b.inUse
  && a.actionQueue == b.actionQueue
  && a.stance == b.stance
  && a.orbs == b.orbs
  && a.orbSlots == b.orbSlots
  && a.focus == b.focus
  && a.activePowers == b.activePowers
  && a.noDraw == b.noDraw
  && a.corruptionActive == b.corruptionActive
  && decide (b.energy ≥ a.energy)  -- energy must not decrease (otherwise loop eventually fails)
  -- damage, block, nextId, exhaustPile, enemy debuffs NOT compared (accumulate harmlessly)

/-- The loop trace dealt damage -/
def dealtDamage (before after : GameState) : Bool :=
  after.damage > before.damage

/-! ## Initial State Builder -/

/-- Create initial state from a list of (CardName x count) pairs.
    Creates CardInstances with sequential ids. -/
def mkInitialState (cardDB : CardName → CardDef)
    (cards : List (CardName × Nat)) (enemySt : EnemyState)
    (startEnergy : Nat := 3) (handSize : Nat := 5) : GameState :=
  let (instances, nextId) := cards.foldl (fun (acc, nid) (name, count) =>
    let def_ := cardDB name
    let newCards := (List.range count).map fun i =>
      mkCardInstance (nid + i) name def_
    (acc ++ newCards, nid + count)
  ) ([], 0)
  {
    hand := []
    drawPile := instances
    actionQueue := List.replicate handSize .draw
    discardPile := []
    exhaustPile := []
    inUse := []
    energy := startEnergy
    damage := 0
    block := 0
    stance := .Neutral
    orbs := []
    orbSlots := 3
    focus := 0
    enemy := enemySt
    activePowers := []
    nextId := nextId
    noDraw := false
    corruptionActive := false
  }

/-! ## Proof Obligation

  An infinite combo proof has two parts:
  1. Setup trace: from initial state, reach stateA
  2. Loop trace: from stateA, reach stateB where
     - stateB is identical to stateA except damage increased
     - this means the loop trace can repeat forever -> infinite damage
-/

/-- A loop trace must not contain endTurn — the loop must complete within a single turn.
    (endTurn lets the enemy act, so a combo requiring endTurn is not truly infinite.) -/
def noEndTurn : List Action → Bool
  | [] => true
  | .endTurn :: _ => false
  | _ :: rest => noEndTurn rest

def InfiniteCombo (cardDB : CardName → CardDef)
    (cards : List (CardName × Nat)) (enemy : EnemyState) : Prop :=
  ∃ (setupTrace loopTrace : List Action)
    (stateA stateB : GameState),
    -- Setup reaches stateA
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA
    -- Loop from stateA reaches stateB
    ∧ execute cardDB stateA loopTrace = some stateB
    -- Loop stays within a single turn (no endTurn)
    ∧ noEndTurn loopTrace = true
    -- stateB = stateA except more damage
    ∧ sameModAccum stateA stateB = true
    ∧ dealtDamage stateA stateB = true

/-! ## Level 2: Guaranteed Infinite (despite shuffle randomness) -/

/-- Shuffle oracle: given shuffle index and cards to shuffle, returns a permutation -/
abbrev ShuffleOracle := Nat → List CardInstance → List CardInstance

/-- Valid oracle: every returned list is a permutation of the input -/
def validOracle (oracle : ShuffleOracle) : Prop :=
  ∀ n pile, List.Perm (oracle n pile) pile

/-- Draw a card with oracle-controlled shuffle.
    Returns updated state and new shuffle index. -/
def drawCardL2 (oracle : ShuffleOracle) (shIdx : Nat) (s : GameState) (cardId : CId)
    : Option (GameState × Nat) :=
  match s.actionQueue with
  | .draw :: rest =>
    if s.noDraw || s.hand.length >= 10 then none
    else
      let (s', shIdx') :=
        if s.drawPile.length == 0 && s.discardPile.length > 0 then
          let newDraw := oracle shIdx s.discardPile
          ({ s with drawPile := newDraw, discardPile := [] }, shIdx + 1)
        else (s, shIdx)
      -- Player draws the TOP card of the pile
      match s'.drawPile with
      | top :: drawRest =>
        if top.id == cardId then
          some ({ s' with
            hand := top :: s'.hand
            drawPile := drawRest
            actionQueue := rest }, shIdx')
        else
          none
      | [] => none
  | _ => none

/-- Execute one action with oracle-controlled shuffles -/
def stepL2 (cardDB : CardName → CardDef)
    (oracle : ShuffleOracle) (shIdx : Nat) (s : GameState) (a : Action)
    : Option (GameState × Nat) :=
  match a with
  | .draw card => drawCardL2 oracle shIdx s card
  -- All other actions don't involve shuffle -- delegate to Level 1 step
  | other =>
      match step cardDB s other with
      | some s' => some (s', shIdx)
      | none => none

/-- Execute a full trace with oracle-controlled shuffles -/
def executeL2 (cardDB : CardName → CardDef)
    (oracle : ShuffleOracle) (shIdx : Nat) (s : GameState) (trace : List Action)
    : Option (GameState × Nat) :=
  let s := autoDrain cardDB s
  match trace with
  | [] => some (s, shIdx)
  | a :: rest =>
    match stepL2 cardDB oracle shIdx s a with
    | none => none
    | some (s', shIdx') => executeL2 cardDB oracle shIdx' s' rest


/-! ## L2 proof target -/

/-- Level 2 proof obligation: the combo has a single-iteration loop that returns the
    game state to sameModAccum-equivalence, dealing damage each time.
    Against any valid shuffle oracle, the loop works.

    Extended proof targets (RobustInfinite, UnboundedDamage, OnlineUnboundedDamage)
    are defined in ExtendedTargets.lean. -/
def GuaranteedInfiniteCombo (cardDB : CardName → CardDef)
    (cards : List (CardName × Nat)) (enemy : EnemyState) : Prop :=
  ∃ (setupTrace : List Action) (stateA : GameState),
    execute cardDB (mkInitialState cardDB cards enemy) setupTrace = some stateA
    ∧ ∀ (oracle : ShuffleOracle),
        validOracle oracle →
        ∃ (loopTrace : List Action) (stateB : GameState) (finalIdx : Nat),
          executeL2 cardDB oracle 0 stateA loopTrace = some (stateB, finalIdx)
          ∧ noEndTurn loopTrace = true
          ∧ sameModAccum stateA stateB = true
          ∧ dealtDamage stateA stateB = true
