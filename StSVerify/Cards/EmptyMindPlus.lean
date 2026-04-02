import StSVerify.CardId
import StSVerify.Engine

def cardEmptyMindPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.drawCards 3, .exitStance]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
