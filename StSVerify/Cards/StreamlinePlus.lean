import StSVerify.CardId
import StSVerify.Engine

def cardStreamlinePlus : CardDef := {
  cost := 2
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 20, .costReduceSelf 1]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
