import StSVerify.Engine
import StSVerify.CardDB
open CardName
namespace ComboStormOfSteel2Prep_L1
def cards : List (CardName × Nat) :=
  [(StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1), (PreparedPlus, 2)]
def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }
end ComboStormOfSteel2Prep_L1
