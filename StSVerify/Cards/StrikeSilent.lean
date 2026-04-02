import StSVerify.CardId
import StSVerify.Engine

def cardStrikeSilent : CardDef := {
  cost := 1
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 6]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
