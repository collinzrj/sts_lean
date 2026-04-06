/-
  AcrobaticsTactician — Level 2 Spec (READ-ONLY)
  Cards: 12 · Character: Silent

  Card reference (id, name, cost, type, effect):
    id= 0  杂技+ #1 (AcrobaticsPlus, 1E, Skill): Draw 4 cards. Discard 1 card.
    id= 1  杂技+ #2 (AcrobaticsPlus, 1E, Skill): Draw 4 cards. Discard 1 card.
    id= 2  战术大师+ (TacticianPlus, 0E, Skill): Cannot be played. On discard: gain 2 energy.
    id= 3  本能反应+ (ReflexPlus, 0E, Skill): Cannot be played. On discard: draw 3 cards.
    id= 4  后空翻+ #1 (BackflipPlus, 1E, Skill): Gain 8 Block. Draw 2 cards.
    id= 5  后空翻+ #2 (BackflipPlus, 1E, Skill): Gain 8 Block. Draw 2 cards.
    id= 6  中和+ (NeutralizePlus, 0E, Attack): Deal 4 damage. Apply 2 Weak.
    id= 7  残影 (AfterImage, 1E, Power): Whenever you play a card, gain 1 Block.
    id= 8  肾上腺素+ (AdrenalinePlus, 0E, Skill): Gain 2 energy. Draw 2 cards. Exhaust.
    id= 9  铁蒺藜+ (CaltropPlus, 1E, Power): Whenever you are attacked, deal 5 damage back.
    id=10  逃跑计划+ (EscapePlanPlus, 0E, Skill): Draw 1 card. If it's a Skill, gain 5 Block.
    id=11  终幕+ (GrandFinalePlus, 0E, Attack): Can only be played if draw pile is empty. Deal 60 damage.

  Initial state: all 12 cards in draw pile, 5 draws queued, 3 energy.
-/
import StSVerify.Engine
import StSVerify.CardDB

open CardName

namespace ComboAcrobaticsTactician_L2

def cards : List (CardName × Nat) :=
  [(AcrobaticsPlus, 2), (TacticianPlus, 1), (ReflexPlus, 1), (BackflipPlus, 2),
   (NeutralizePlus, 1), (AfterImage, 1), (AdrenalinePlus, 1), (CaltropPlus, 1),
   (EscapePlanPlus, 1), (GrandFinalePlus, 1)]

def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }

end ComboAcrobaticsTactician_L2
