import StSVerify.Engine
import StSVerify.CardId
import StSVerify.Cards.BashPlus
import StSVerify.Cards.Dropkick
import StSVerify.Cards.TrueGritPlus
import StSVerify.Cards.BurningPactPlus
import StSVerify.Cards.PommelStrikePlus
import StSVerify.Cards.ShrugItOff
import StSVerify.Cards.ShrugItOffPlus
import StSVerify.Cards.Offering
import StSVerify.Cards.OfferingPlus
import StSVerify.Cards.Purity
import StSVerify.Cards.BattleCryPlus
import StSVerify.Cards.BattleTrancePlus
import StSVerify.Cards.Corruption
import StSVerify.Cards.DarkEmbracePlus
import StSVerify.Cards.FeelNoPainPlus
import StSVerify.Cards.MetallicizePlus
import StSVerify.Cards.JuggernautPlus
import StSVerify.Cards.ImperviousPlus
import StSVerify.Cards.SecondWindPlus
import StSVerify.Cards.PowerThroughPlus
import StSVerify.Cards.Anger
import StSVerify.Cards.NeutralizePlus
import StSVerify.Cards.PreparedPlus
import StSVerify.Cards.ReflexPlus
import StSVerify.Cards.TacticianPlus
import StSVerify.Cards.AcrobaticsPlus
import StSVerify.Cards.BackflipPlus
import StSVerify.Cards.CalculatedGamblePlus
import StSVerify.Cards.HeelHookPlus
import StSVerify.Cards.BladeDancePlus
import StSVerify.Cards.EscapePlan
import StSVerify.Cards.EscapePlanPlus
import StSVerify.Cards.AfterImage
import StSVerify.Cards.AccuracyPlus
import StSVerify.Cards.AThousandCuts
import StSVerify.Cards.CaltropPlus
import StSVerify.Cards.WraithFormPlus
import StSVerify.Cards.AdrenalinePlus
import StSVerify.Cards.BurstPlus
import StSVerify.Cards.BackstabPlus
import StSVerify.Cards.DieDieDiePlus
import StSVerify.Cards.MalaisePlus
import StSVerify.Cards.PiercingWail
import StSVerify.Cards.GrandFinalePlus
import StSVerify.Cards.EvisceratePlus
import StSVerify.Cards.StormOfSteelPlus
import StSVerify.Cards.StrikeSilent
import StSVerify.Cards.ZapPlus
import StSVerify.Cards.ClawPlus
import StSVerify.Cards.BeamCellPlus
import StSVerify.Cards.CoolheadedPlus
import StSVerify.Cards.SkimPlus
import StSVerify.Cards.HologramPlus
import StSVerify.Cards.AllForOnePlus
import StSVerify.Cards.TurboPlus
import StSVerify.Cards.RecyclePlus
import StSVerify.Cards.StreamlinePlus
import StSVerify.Cards.GlacierPlus
import StSVerify.Cards.DefragmentPlus
import StSVerify.Cards.BiasedCognitionPlus
import StSVerify.Cards.CapacitorPlus
import StSVerify.Cards.SelfRepairPlus
import StSVerify.Cards.CreativeAIPlus
import StSVerify.Cards.Buffer
import StSVerify.Cards.BufferPlus
import StSVerify.Cards.RebootPlus
import StSVerify.Cards.Madness
import StSVerify.Cards.EruptionPlus
import StSVerify.Cards.TantrumPlus
import StSVerify.Cards.InnerPeace
import StSVerify.Cards.InnerPeacePlus
import StSVerify.Cards.FearNoEvilPlus
import StSVerify.Cards.VigilancePlus
import StSVerify.Cards.IndignationPlus
import StSVerify.Cards.EmptyMindPlus
import StSVerify.Cards.MeditatePlus
import StSVerify.Cards.FlurryOfBlowsPlus
import StSVerify.Cards.Rushdown
import StSVerify.Cards.MentalFortressPlus
import StSVerify.Cards.EstablishmentPlus
import StSVerify.Cards.PrayPlus
import StSVerify.Cards.ProstatePlus
import StSVerify.Cards.Scrawl
import StSVerify.Cards.VaultPlus
import StSVerify.Cards.TalkToTheHandPlus
import StSVerify.Cards.OmnisciencePlus
import StSVerify.Cards.Finesse
import StSVerify.Cards.FlashOfSteel
import StSVerify.Cards.Shiv
import StSVerify.Cards.Wound
import StSVerify.Cards.Void
import StSVerify.Cards.Miracle
import StSVerify.Cards.Insight
import StSVerify.Cards.Necronomicurse
import StSVerify.Cards.DeusExMachina

open CardName

def cardDB (name : CardName) : CardDef :=
  match name with
  | .BashPlus => cardBashPlus
  | .Dropkick => cardDropkick
  | .TrueGritPlus => cardTrueGritPlus
  | .BurningPactPlus => cardBurningPactPlus
  | .PommelStrikePlus => cardPommelStrikePlus
  | .ShrugItOff => cardShrugItOff
  | .ShrugItOffPlus => cardShrugItOffPlus
  | .Offering => cardOffering
  | .OfferingPlus => cardOfferingPlus
  | .Purity => cardPurity
  | .BattleCryPlus => cardBattleCryPlus
  | .BattleTrancePlus => cardBattleTrancePlus
  | .Corruption => cardCorruption
  | .DarkEmbracePlus => cardDarkEmbracePlus
  | .FeelNoPainPlus => cardFeelNoPainPlus
  | .MetallicizePlus => cardMetallicizePlus
  | .JuggernautPlus => cardJuggernautPlus
  | .ImperviousPlus => cardImperviousPlus
  | .SecondWindPlus => cardSecondWindPlus
  | .PowerThroughPlus => cardPowerThroughPlus
  | .Anger => cardAnger
  | .NeutralizePlus => cardNeutralizePlus
  | .PreparedPlus => cardPreparedPlus
  | .ReflexPlus => cardReflexPlus
  | .TacticianPlus => cardTacticianPlus
  | .AcrobaticsPlus => cardAcrobaticsPlus
  | .BackflipPlus => cardBackflipPlus
  | .CalculatedGamblePlus => cardCalculatedGamblePlus
  | .HeelHookPlus => cardHeelHookPlus
  | .BladeDancePlus => cardBladeDancePlus
  | .EscapePlan => cardEscapePlan
  | .EscapePlanPlus => cardEscapePlanPlus
  | .AfterImage => cardAfterImage
  | .AccuracyPlus => cardAccuracyPlus
  | .AThousandCuts => cardAThousandCuts
  | .CaltropPlus => cardCaltropPlus
  | .WraithFormPlus => cardWraithFormPlus
  | .AdrenalinePlus => cardAdrenalinePlus
  | .BurstPlus => cardBurstPlus
  | .BackstabPlus => cardBackstabPlus
  | .DieDieDiePlus => cardDieDieDiePlus
  | .MalaisePlus => cardMalaisePlus
  | .PiercingWail => cardPiercingWail
  | .GrandFinalePlus => cardGrandFinalePlus
  | .EvisceratePlus => cardEvisceratePlus
  | .StormOfSteelPlus => cardStormOfSteelPlus
  | .StrikeSilent => cardStrikeSilent
  | .ZapPlus => cardZapPlus
  | .ClawPlus => cardClawPlus
  | .BeamCellPlus => cardBeamCellPlus
  | .CoolheadedPlus => cardCoolheadedPlus
  | .SkimPlus => cardSkimPlus
  | .HologramPlus => cardHologramPlus
  | .AllForOnePlus => cardAllForOnePlus
  | .TurboPlus => cardTurboPlus
  | .RecyclePlus => cardRecyclePlus
  | .StreamlinePlus => cardStreamlinePlus
  | .GlacierPlus => cardGlacierPlus
  | .DefragmentPlus => cardDefragmentPlus
  | .BiasedCognitionPlus => cardBiasedCognitionPlus
  | .CapacitorPlus => cardCapacitorPlus
  | .SelfRepairPlus => cardSelfRepairPlus
  | .CreativeAIPlus => cardCreativeAIPlus
  | .Buffer => cardBuffer
  | .BufferPlus => cardBufferPlus
  | .RebootPlus => cardRebootPlus
  | .Madness => cardMadness
  | .EruptionPlus => cardEruptionPlus
  | .TantrumPlus => cardTantrumPlus
  | .InnerPeace => cardInnerPeace
  | .InnerPeacePlus => cardInnerPeacePlus
  | .FearNoEvilPlus => cardFearNoEvilPlus
  | .VigilancePlus => cardVigilancePlus
  | .IndignationPlus => cardIndignationPlus
  | .EmptyMindPlus => cardEmptyMindPlus
  | .MeditatePlus => cardMeditatePlus
  | .FlurryOfBlowsPlus => cardFlurryOfBlowsPlus
  | .Rushdown => cardRushdown
  | .MentalFortressPlus => cardMentalFortressPlus
  | .EstablishmentPlus => cardEstablishmentPlus
  | .PrayPlus => cardPrayPlus
  | .ProstatePlus => cardProstatePlus
  | .Scrawl => cardScrawl
  | .VaultPlus => cardVaultPlus
  | .TalkToTheHandPlus => cardTalkToTheHandPlus
  | .OmnisciencePlus => cardOmnisciencePlus
  | .Finesse => cardFinesse
  | .FlashOfSteel => cardFlashOfSteel
  | .Shiv => cardShiv
  | .Wound => cardWound
  | .Void => cardVoid
  | .Miracle => cardMiracle
  | .Insight => cardInsight
  | .Necronomicurse => cardNecronomicurse
  | .DeusExMachina => cardDeusExMachina
