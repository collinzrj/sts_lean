import StSVerify.Engine
import StSVerify.CardDB
open CardName
namespace ComboStormStrike_L2
def cards : List (CardName × Nat) :=
  [(StormOfSteelPlus, 1), (TacticianPlus, 1), (ReflexPlus, 1), (PreparedPlus, 1), (StrikeSilent, 1)]
def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }
end ComboStormStrike_L2
