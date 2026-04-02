import StSVerify.CardId
import StSVerify.Engine

def cardFlashOfSteel : CardDef := {
  cost := 0
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 3, .drawCards 1]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
