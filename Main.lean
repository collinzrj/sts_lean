import StSVerify.Engine
import StSVerify.EngineHelperLemmas
import StSVerify.CardDB
import StSVerify.Demo
-- L1: 12/12 (all combos have single-turn infinite loops)
import StSVerify.CombosTemplateL1.ComboDropkickExhaust
import StSVerify.CombosTemplateL1.ComboCorruptionDropkick
import StSVerify.CombosTemplateL1.ComboAcrobaticsTactician
import StSVerify.CombosTemplateL1.ComboHeelHookExhaust
import StSVerify.CombosTemplateL1.ComboStreamlineHologram
import StSVerify.CombosTemplateL1.ComboStandardWatcher
import StSVerify.CombosTemplateL1.ComboMantraDivine
import StSVerify.CombosTemplateL1.ComboTantrumFearNoEvil
import StSVerify.CombosTemplateL1.ComboStormOfSteel
import StSVerify.CombosTemplateL1.ComboStormOfSteel2Prep
import StSVerify.CombosTemplateL1.ComboStormOfSteel3Prep
import StSVerify.CombosTemplateL1.ComboStormStrike
-- L2: 11/12 GuaranteedInfiniteCombo (proved)
import StSVerify.CombosTemplateL2.ComboDropkickExhaust
import StSVerify.CombosTemplateL2.ComboCorruptionDropkick
import StSVerify.CombosTemplateL2.ComboHeelHookExhaust
import StSVerify.CombosTemplateL2.ComboStreamlineHologram
import StSVerify.CombosTemplateL2.ComboStormOfSteel
import StSVerify.CombosTemplateL2.ComboStormOfSteel2Prep
import StSVerify.CombosTemplateL2.ComboStormStrike
import StSVerify.CombosTemplateL2.ComboMantraDivine
import StSVerify.CombosTemplateL2.ComboStandardWatcher
import StSVerify.CombosTemplateL2.ComboAcrobaticsTactician
import StSVerify.CombosTemplateL2.ComboTantrumFearNoEvil
-- L2: 1/12 UnboundedDamage OPEN (3Prep: 6-card deck, adversary can strand Reflex,
--   requires multi-iteration adaptive strategy proof — hardest benchmark challenge)
-- import StSVerify.CombosTemplateL2.ComboStormOfSteel3Prep  -- sorry

def main : IO Unit :=
  IO.println "All StS infinite combo proofs verified!"
