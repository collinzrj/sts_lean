import StSVerify.Engine
import StSVerify.CardDB
open CardName
namespace ComboTantrumFearNoEvil_L1
def cards : List (CardName × Nat) :=
  [(Rushdown, 2), (MentalFortressPlus, 1), (TantrumPlus, 1), (FearNoEvilPlus, 2), (FlurryOfBlowsPlus, 2), (Scrawl, 1), (VaultPlus, 1), (DeusExMachina, 1)]
def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := true }
end ComboTantrumFearNoEvil_L1
