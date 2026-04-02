import StSVerify.CardId
import StSVerify.Engine

def cardStormOfSteelPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.stormOfSteel CardName.Shiv]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
