#!/usr/bin/env python3
"""Generate individual Lean card definition files from card data."""

import os

CARDS_DIR = "StSVerify/Cards"
os.makedirs(CARDS_DIR, exist_ok=True)

# (LeanName, CardName enum value, CardDef fields)
# effects is a Lean List CardEffect literal
CARDS = [
    # === Ironclad ===
    ("BashPlus", "BashPlus", 2, True, True, False, False,
     "[.dealDamage 10, .applyVulnerable 3]", "[]", "[]", "[]"),
    ("Dropkick", "Dropkick", 1, True, True, False, False,
     "[.dealDamage 5, .ifVulnerableGainEnergy 1, .ifVulnerableDrawCards 1]", "[]", "[]", "[]"),
    ("TrueGritPlus", "TrueGritPlus", 1, True, False, True, False,
     "[.gainBlock 9, .exhaustFromHand 1]", "[]", "[]", "[]"),
    ("BurningPactPlus", "BurningPactPlus", 1, True, False, True, False,
     "[.exhaustFromHand 1, .drawCards 3]", "[]", "[]", "[]"),
    ("PommelStrikePlus", "PommelStrikePlus", 1, True, True, False, False,
     "[.dealDamage 10, .drawCards 2]", "[]", "[]", "[]"),
    ("ShrugItOff", "ShrugItOff", 1, True, False, True, False,
     "[.gainBlock 8, .drawCards 1]", "[]", "[]", "[]"),
    ("ShrugItOffPlus", "ShrugItOffPlus", 1, True, False, True, False,
     "[.gainBlock 11, .drawCards 1]", "[]", "[]", "[]"),
    ("Offering", "Offering", 0, True, False, True, False,
     "[.gainEnergy 2, .drawCards 3, .exhaustSelf]", "[]", "[]", "[]"),
    ("OfferingPlus", "OfferingPlus", 0, True, False, True, False,
     "[.gainEnergy 2, .drawCards 5, .exhaustSelf]", "[]", "[]", "[]"),
    ("Purity", "Purity", 0, True, False, True, False,
     "[.exhaustFromHand 3, .exhaustSelf]", "[]", "[]", "[]"),
    ("BattleCryPlus", "BattleCryPlus", 0, True, False, True, False,
     "[.exhaustSelf]", "[]", "[]", "[]"),  # simplified: putting card on top modeled via action
    ("BattleTrancePlus", "BattleTrancePlus", 0, True, False, True, False,
     "[.drawCards 4, .setNoDraw]", "[]", "[]", "[]"),
    ("Corruption", "Corruption", 3, True, False, False, True,
     "[.setCorruption]", "[]", "[]", "[]"),
    ("DarkEmbracePlus", "DarkEmbracePlus", 1, True, False, False, True,
     "[]", "[]", "[]", "[]"),  # effect handled via powerCount
    ("FeelNoPainPlus", "FeelNoPainPlus", 1, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("MetallicizePlus", "MetallicizePlus", 1, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("JuggernautPlus", "JuggernautPlus", 2, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("ImperviousPlus", "ImperviousPlus", 2, True, False, True, False,
     "[.gainBlock 40, .exhaustSelf]", "[]", "[]", "[]"),
    ("SecondWindPlus", "SecondWindPlus", 2, True, False, True, False,
     "[.secondWind 7]", "[]", "[]", "[]"),
    ("PowerThroughPlus", "PowerThroughPlus", 1, True, False, True, False,
     "[.gainBlock 20, .addTokensToHand CardName.Wound 2]", "[]", "[]", "[]"),
    ("Anger", "Anger", 0, True, True, False, False,
     "[.dealDamage 6]", "[]", "[]", "[]"),  # copy-self effect modeled separately

    # === Silent ===
    ("NeutralizePlus", "NeutralizePlus", 0, True, True, False, False,
     "[.dealDamage 4, .applyWeak 2]", "[]", "[]", "[]"),
    ("PreparedPlus", "PreparedPlus", 0, True, False, True, False,
     "[.drawCards 2, .discardCards 1]", "[]", "[]", "[]"),
    ("ReflexPlus", "ReflexPlus", 0, False, False, True, False,
     "[]", "[.drawCards 3]", "[]", "[]"),
    ("TacticianPlus", "TacticianPlus", 0, False, False, True, False,
     "[]", "[.gainEnergy 2]", "[]", "[]"),
    ("AcrobaticsPlus", "AcrobaticsPlus", 1, True, False, True, False,
     "[.drawCards 4, .discardCards 1]", "[]", "[]", "[]"),
    ("BackflipPlus", "BackflipPlus", 1, True, False, True, False,
     "[.gainBlock 8, .drawCards 2]", "[]", "[]", "[]"),
    ("CalculatedGamblePlus", "CalculatedGamblePlus", 0, True, False, True, False,
     "[.discardAllHandAndDraw]", "[]", "[]", "[]"),
    ("HeelHookPlus", "HeelHookPlus", 1, True, True, False, False,
     "[.dealDamage 8, .ifWeakGainEnergy 1, .ifWeakDrawCards 1]", "[]", "[]", "[]"),
    ("BladeDancePlus", "BladeDancePlus", 1, True, False, True, False,
     "[.addTokensToHand CardName.Shiv 4]", "[]", "[]", "[]"),
    ("EscapePlan", "EscapePlan", 0, True, False, True, False,
     "[.drawCards 1]", "[]", "[]", "[]"),
    ("EscapePlanPlus", "EscapePlanPlus", 0, True, False, True, False,
     "[.drawCards 1]", "[]", "[]", "[]"),
    ("AfterImage", "AfterImage", 1, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("AccuracyPlus", "AccuracyPlus", 1, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("AThousandCuts", "AThousandCuts", 2, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("CaltropPlus", "CaltropPlus", 1, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("WraithFormPlus", "WraithFormPlus", 3, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("AdrenalinePlus", "AdrenalinePlus", 0, True, False, True, False,
     "[.gainEnergy 2, .drawCards 2, .exhaustSelf]", "[]", "[]", "[]"),
    ("BurstPlus", "BurstPlus", 1, True, False, True, False,
     "[.exhaustSelf]", "[]", "[]", "[]"),
    ("BackstabPlus", "BackstabPlus", 0, True, True, False, False,
     "[.dealDamage 15, .exhaustSelf]", "[]", "[]", "[]"),
    ("DieDieDiePlus", "DieDieDiePlus", 1, True, True, False, False,
     "[.dealDamage 17, .exhaustSelf]", "[]", "[]", "[]"),
    ("MalaisePlus", "MalaisePlus", 0, True, False, True, False,
     "[.exhaustSelf]", "[]", "[]", "[]"),  # X-cost, simplified
    ("PiercingWail", "PiercingWail", 1, True, False, True, False,
     "[.exhaustSelf]", "[]", "[]", "[]"),
    ("GrandFinalePlus", "GrandFinalePlus", 0, True, True, False, False,
     "[.requireEmptyDrawPile, .dealDamage 60, .exhaustSelf]", "[]", "[]", "[]"),
    ("EvisceratePlus", "EvisceratePlus", 3, True, True, False, False,
     "[.dealDamage 27]", "[]", "[]", "[]"),  # 9x3, cost reduction modeled via override
    ("StormOfSteelPlus", "StormOfSteelPlus", 1, True, False, True, False,
     "[.stormOfSteel CardName.Shiv]", "[]", "[]", "[]"),
    ("StrikeSilent", "StrikeSilent", 1, True, True, False, False,
     "[.dealDamage 6]", "[]", "[]", "[]"),

    # === Defect ===
    ("ZapPlus", "ZapPlus", 0, True, False, True, False,
     "[.channelOrb .Lightning]", "[]", "[]", "[]"),
    ("ClawPlus", "ClawPlus", 0, True, True, False, False,
     "[.dealDamage 5, .clawScaling]", "[]", "[]", "[]"),
    ("BeamCellPlus", "BeamCellPlus", 0, True, True, False, False,
     "[.dealDamage 4, .applyVulnerable 2]", "[]", "[]", "[]"),
    ("CoolheadedPlus", "CoolheadedPlus", 1, True, False, True, False,
     "[.channelOrb .Frost, .drawCards 2]", "[]", "[]", "[]"),
    ("SkimPlus", "SkimPlus", 1, True, False, True, False,
     "[.drawCards 4]", "[]", "[]", "[]"),
    ("HologramPlus", "HologramPlus", 0, True, False, True, False,
     "[.gainBlock 5, .hologramRetrieve]", "[]", "[]", "[]"),
    ("AllForOnePlus", "AllForOnePlus", 2, True, True, False, False,
     "[.dealDamage 14, .allForOneRetrieve]", "[]", "[]", "[]"),
    ("TurboPlus", "TurboPlus", 0, True, False, True, False,
     "[.gainEnergy 2, .addTokenToDiscard CardName.Void]", "[]", "[]", "[]"),
    ("RecyclePlus", "RecyclePlus", 0, True, False, True, False,
     "[]", "[]", "[]", "[]"),  # choice handled via recycleChoose action
    ("StreamlinePlus", "StreamlinePlus", 2, True, True, False, False,
     "[.dealDamage 20, .costReduceSelf 1]", "[]", "[]", "[]"),
    ("GlacierPlus", "GlacierPlus", 2, True, False, True, False,
     "[.gainBlock 10, .channelOrb .Frost, .channelOrb .Frost]", "[]", "[]", "[]"),
    ("DefragmentPlus", "DefragmentPlus", 1, True, False, False, True,
     "[.gainFocus 1]", "[]", "[]", "[]"),
    ("BiasedCognitionPlus", "BiasedCognitionPlus", 1, True, False, False, True,
     "[.gainFocus 4]", "[]", "[]", "[]"),
    ("CapacitorPlus", "CapacitorPlus", 1, True, False, False, True,
     "[.gainOrbSlots 3]", "[]", "[]", "[]"),
    ("SelfRepairPlus", "SelfRepairPlus", 1, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("CreativeAIPlus", "CreativeAIPlus", 2, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("Buffer", "Buffer", 2, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("BufferPlus", "BufferPlus", 2, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("RebootPlus", "RebootPlus", 0, True, False, True, False,
     "[.shuffleHandIntoDraw, .drawCards 5, .exhaustSelf]", "[]", "[]", "[]"),
    ("Madness", "Madness", 0, True, False, True, False,
     "[.exhaustSelf]", "[]", "[]", "[]"),  # random cost reduction modeled via override

    # === Watcher ===
    ("EruptionPlus", "EruptionPlus", 1, True, True, False, False,
     "[.dealDamage 9, .enterStance .Wrath]", "[]", "[]", "[]"),
    ("TantrumPlus", "TantrumPlus", 1, True, True, False, False,
     "[.dealDamage 12, .enterStance .Wrath, .shuffleSelf]", "[]", "[]", "[]"),
    ("InnerPeace", "InnerPeace", 1, True, False, True, False,
     "[.ifInStanceDrawCards .Calm 3, .ifNotInStanceEnter .Calm]", "[]", "[]", "[]"),
    ("InnerPeacePlus", "InnerPeacePlus", 1, True, False, True, False,
     "[.ifInStanceDrawCards .Calm 3, .ifNotInStanceEnter .Calm]", "[]", "[]", "[]"),
    ("FearNoEvilPlus", "FearNoEvilPlus", 1, True, True, False, False,
     "[.dealDamage 11, .ifEnemyAttackingEnterStance .Calm]", "[]", "[]", "[]"),
    ("VigilancePlus", "VigilancePlus", 2, True, False, True, False,
     "[.gainBlock 12, .enterStance .Calm]", "[]", "[]", "[]"),
    ("IndignationPlus", "IndignationPlus", 1, True, False, True, False,
     "[.ifNotInStanceEnter .Wrath, .ifInStanceApplyVulnerable .Wrath 4]", "[]", "[]", "[]"),
    ("EmptyMindPlus", "EmptyMindPlus", 1, True, False, True, False,
     "[.drawCards 3, .exitStance]", "[]", "[]", "[]"),
    ("MeditatePlus", "MeditatePlus", 1, True, False, True, False,
     "[]", "[]", "[]", "[]"),  # ends turn, complex
    ("FlurryOfBlowsPlus", "FlurryOfBlowsPlus", 0, True, True, False, False,
     "[.dealDamage 6]", "[]", "[]", "[]"),
    ("Rushdown", "Rushdown", 1, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("MentalFortressPlus", "MentalFortressPlus", 1, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("EstablishmentPlus", "EstablishmentPlus", 1, True, False, False, True,
     "[]", "[]", "[]", "[]"),
    ("PrayPlus", "PrayPlus", 1, True, False, True, False,
     "[.addTokenToDrawPile CardName.Insight]", "[]", "[]", "[]"),  # mantra not modeled
    ("ProstatePlus", "ProstatePlus", 0, True, False, True, False,
     "[.gainBlock 5]", "[]", "[]", "[]"),  # mantra not modeled
    ("Scrawl", "Scrawl", 1, True, False, True, False,
     "[.drawToFull 10, .exhaustSelf]", "[]", "[]", "[]"),
    ("VaultPlus", "VaultPlus", 2, True, False, True, False,
     "[.exhaustSelf]", "[]", "[]", "[]"),  # ends turn
    ("TalkToTheHandPlus", "TalkToTheHandPlus", 1, True, True, False, False,
     "[.dealDamage 7, .exhaustSelf]", "[]", "[]", "[]"),
    ("OmnisciencePlus", "OmnisciencePlus", 3, True, False, True, False,
     "[.exhaustSelf]", "[]", "[]", "[]"),  # complex: play from draw pile twice

    # === Colorless ===
    ("Finesse", "Finesse", 0, True, False, True, False,
     "[.gainBlock 2, .drawCards 1]", "[]", "[]", "[]"),
    ("FlashOfSteel", "FlashOfSteel", 0, True, True, False, False,
     "[.dealDamage 3, .drawCards 1]", "[]", "[]", "[]"),

    # === Tokens / Status / Curse ===
    ("Shiv", "Shiv", 0, True, True, False, False,
     "[.dealDamage 4, .exhaustSelf]", "[]", "[]", "[]"),
    ("Wound", "Wound", 0, False, False, False, False,
     "[]", "[]", "[]", "[]"),
    ("Void", "Void", 0, False, False, False, False,
     "[.exhaustSelf]", "[]", "[]", "[]"),  # on draw: lose 1 energy + exhaust, handled via resolveDrawTrigger
    ("Miracle", "Miracle", 0, True, False, True, False,
     "[.gainEnergy 1, .exhaustSelf]", "[]", "[]", "[]"),
    ("Insight", "Insight", 0, True, False, True, False,
     "[.drawCards 2, .exhaustSelf]", "[]", "[]", "[]"),
    ("Necronomicurse", "Necronomicurse", 0, False, False, False, False,
     "[]", "[]", "[]", "[]"),
    ("DeusExMachina", "DeusExMachina", 0, False, False, False, False,
     "[]", "[]", "[.addTokensToHand CardName.Miracle 2, .exhaustSelf]", "[]"),
]

TEMPLATE = '''import StSVerify.CardId
import StSVerify.Basic

def card{name} : CardDef := {{
  cost := {cost}
  playable := {playable}
  isAttack := {is_attack}
  isSkill := {is_skill}
  isPower := {is_power}
  effects := {effects}
  onDiscard := {on_discard}
  onDiscardPriority := {on_discard_priority}
  onDraw := {on_draw}
  onExhaust := {on_exhaust}
}}
'''

# On-discard priority overrides (default is .bottom)
DISCARD_PRIORITY = {
    "TacticianPlus": ".top",   # energy before remaining discards
}

# Generate imports file
imports = []

for (name, enum_val, cost, playable, is_attack, is_skill, is_power,
     effects, on_discard, on_draw, on_exhaust) in CARDS:
    priority = DISCARD_PRIORITY.get(name, ".bottom")
    content = TEMPLATE.format(
        name=name,
        cost=cost,
        playable=str(playable).lower(),
        is_attack=str(is_attack).lower(),
        is_skill=str(is_skill).lower(),
        is_power=str(is_power).lower(),
        effects=effects,
        on_discard=on_discard,
        on_discard_priority=priority,
        on_draw=on_draw,
        on_exhaust=on_exhaust,
    )
    filepath = os.path.join(CARDS_DIR, f"{name}.lean")
    with open(filepath, "w") as f:
        f.write(content)
    imports.append(f"import StSVerify.Cards.{name}")
    print(f"Generated: {filepath}")

# Generate CardDB.lean
db_lines = ["import StSVerify.Basic", "import StSVerify.CardId"]
db_lines += imports
db_lines.append("")
db_lines.append("open CardName")
db_lines.append("")
db_lines.append("def cardDB (name : CardName) : CardDef :=")
db_lines.append("  match name with")
for (name, enum_val, *_) in CARDS:
    db_lines.append(f"  | .{enum_val} => card{name}")

with open("StSVerify/CardDB.lean", "w") as f:
    f.write("\n".join(db_lines) + "\n")
print(f"Generated: StSVerify/CardDB.lean")

print(f"\nTotal: {len(CARDS)} cards generated")
