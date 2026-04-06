import StSVerify.Engine
import StSVerify.CardDB
open CardName
namespace ComboAcrobaticsTactician_L1
def cards : List (CardName × Nat) :=
  [(AcrobaticsPlus, 2), (TacticianPlus, 1), (ReflexPlus, 1), (BackflipPlus, 2), (NeutralizePlus, 1), (AfterImage, 1), (AdrenalinePlus, 1), (CaltropPlus, 1), (EscapePlanPlus, 1), (GrandFinalePlus, 1)]
def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }
end ComboAcrobaticsTactician_L1
