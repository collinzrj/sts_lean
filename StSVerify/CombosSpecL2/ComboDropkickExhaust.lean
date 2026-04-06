import StSVerify.Engine
import StSVerify.CardDB
open CardName
namespace ComboDropkickExhaust_L2
def cards : List (CardName × Nat) :=
  [(BashPlus, 1), (Dropkick, 2), (TrueGritPlus, 2), (BurningPactPlus, 1), (ShrugItOffPlus, 1), (OfferingPlus, 1), (Purity, 1), (BattleCryPlus, 1), (PommelStrikePlus, 1)]
def enemy : EnemyState := { vulnerable := 3, weak := 0, intending := false }
end ComboDropkickExhaust_L2
