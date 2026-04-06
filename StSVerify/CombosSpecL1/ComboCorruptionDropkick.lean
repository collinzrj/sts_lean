import StSVerify.Engine
import StSVerify.CardDB
open CardName
namespace ComboCorruptionDropkick_L1
def cards : List (CardName × Nat) :=
  [(Corruption, 1), (DarkEmbracePlus, 1), (FeelNoPainPlus, 1), (BashPlus, 1), (Dropkick, 2), (ShrugItOff, 2), (TrueGritPlus, 1), (MetallicizePlus, 1), (ImperviousPlus, 1), (Offering, 1), (BattleTrancePlus, 1)]
def enemy : EnemyState := { vulnerable := 3, weak := 0, intending := false }
end ComboCorruptionDropkick_L1
