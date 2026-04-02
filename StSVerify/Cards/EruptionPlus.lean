import StSVerify.CardId
import StSVerify.Engine

def cardEruptionPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 9, .enterStance .Wrath]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
