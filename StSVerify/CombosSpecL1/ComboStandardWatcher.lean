import StSVerify.Engine
import StSVerify.CardDB
open CardName
namespace ComboStandardWatcher_L1
def cards : List (CardName × Nat) :=
  [(Rushdown, 2), (MentalFortressPlus, 1), (EruptionPlus, 1), (TantrumPlus, 1), (InnerPeacePlus, 1), (FearNoEvilPlus, 1), (FlurryOfBlowsPlus, 1), (Scrawl, 1), (VaultPlus, 1), (DeusExMachina, 1), (TalkToTheHandPlus, 1)]
def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := true }
end ComboStandardWatcher_L1
