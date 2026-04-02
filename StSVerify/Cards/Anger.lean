import StSVerify.CardId
import StSVerify.Engine

def cardAnger : CardDef := {
  cost := 0
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
