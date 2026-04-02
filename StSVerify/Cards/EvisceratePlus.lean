import StSVerify.CardId
import StSVerify.Engine

def cardEvisceratePlus : CardDef := {
  cost := 3
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 27]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
