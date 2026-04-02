import StSVerify.CardId
import StSVerify.Engine

def cardTantrumPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 12, .enterStance .Wrath, .shuffleSelf]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
