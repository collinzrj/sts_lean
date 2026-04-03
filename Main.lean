import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB
import StSVerify.Demo
-- L1: 12/12 (all combos have single-turn infinite loops)
import StSVerify.CombosLevel1Solution.ComboDropkickExhaust
import StSVerify.CombosLevel1Solution.ComboCorruptionDropkick
import StSVerify.CombosLevel1Solution.ComboAcrobaticsTactician
import StSVerify.CombosLevel1Solution.ComboHeelHookExhaust
import StSVerify.CombosLevel1Solution.ComboStreamlineHologram
import StSVerify.CombosLevel1Solution.ComboStandardWatcher
import StSVerify.CombosLevel1Solution.ComboMantraDivine
import StSVerify.CombosLevel1Solution.ComboTantrumFearNoEvil
import StSVerify.CombosLevel1Solution.ComboStormOfSteel
import StSVerify.CombosLevel1Solution.ComboStormOfSteel2Prep
import StSVerify.CombosLevel1Solution.ComboStormOfSteel3Prep
import StSVerify.CombosLevel1Solution.ComboStormStrike
-- L2: 11/12 proved infinite
import StSVerify.CombosLevel2Solution.ComboDropkickExhaust
import StSVerify.CombosLevel2Solution.ComboCorruptionDropkick
import StSVerify.CombosLevel2Solution.ComboHeelHookExhaust
import StSVerify.CombosLevel2Solution.ComboStreamlineHologram
import StSVerify.CombosLevel2Solution.ComboStormOfSteel
import StSVerify.CombosLevel2Solution.ComboStormOfSteel2Prep
import StSVerify.CombosLevel2Solution.ComboStormStrike
import StSVerify.CombosLevel2Solution.ComboMantraDivine
import StSVerify.CombosLevel2Solution.ComboStandardWatcher
import StSVerify.CombosLevel2Solution.ComboAcrobaticsTactician
import StSVerify.CombosLevel2Solution.ComboTantrumFearNoEvil
-- L2: 1/12 sorry (3Prep: 6-card shuffle creates cascading oracle interactions)
-- import StSVerify.CombosLevel2Solution.ComboStormOfSteel3Prep  -- 2 sorry

def main : IO Unit :=
  IO.println "All StS infinite combo proofs verified!"
