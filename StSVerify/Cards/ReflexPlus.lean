import StSVerify.CardId
import StSVerify.Engine

def cardReflexPlus : CardDef := {
  cost := 0
  playable := false
  isAttack := false
  isSkill := true
  isPower := false
  effects := []
  onDiscard := [.drawCards 3]
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
