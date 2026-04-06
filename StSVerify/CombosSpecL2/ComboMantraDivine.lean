import StSVerify.Engine
import StSVerify.CardDB
open CardName
namespace ComboMantraDivine_L2
def cards : List (CardName × Nat) :=
  [(Rushdown, 2), (MentalFortressPlus, 1), (EruptionPlus, 1), (InnerPeace, 1), (PrayPlus, 1), (ProstatePlus, 1), (EmptyMindPlus, 1), (FlurryOfBlowsPlus, 1), (Scrawl, 1), (VaultPlus, 1), (DeusExMachina, 1), (OmnisciencePlus, 1)]
def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }
end ComboMantraDivine_L2
