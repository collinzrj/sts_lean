import StSVerify.Engine
import StSVerify.CardDB
open CardName
namespace ComboHeelHookExhaust_L1
def cards : List (CardName × Nat) :=
  [(HeelHookPlus, 2), (NeutralizePlus, 1), (MalaisePlus, 1), (PiercingWail, 1), (AdrenalinePlus, 1), (DieDieDiePlus, 1), (AfterImage, 1), (EscapePlanPlus, 1), (BackflipPlus, 1)]
def enemy : EnemyState := { vulnerable := 0, weak := 2, intending := false }
end ComboHeelHookExhaust_L1
