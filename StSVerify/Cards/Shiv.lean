import StSVerify.CardId
import StSVerify.Engine

def cardShiv : CardDef := {
  cost := 0
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 4, .exhaustSelf]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
