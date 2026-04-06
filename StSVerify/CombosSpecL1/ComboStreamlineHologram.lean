import StSVerify.Engine
import StSVerify.CardDB
open CardName
namespace ComboStreamlineHologram_L1
def cards : List (CardName × Nat) :=
  [(StreamlinePlus, 1), (HologramPlus, 2), (CoolheadedPlus, 1), (DefragmentPlus, 1), (BiasedCognitionPlus, 1), (CapacitorPlus, 1), (RecyclePlus, 1), (SkimPlus, 1), (TurboPlus, 1), (RebootPlus, 1)]
def enemy : EnemyState := { vulnerable := 0, weak := 0, intending := false }
end ComboStreamlineHologram_L1
