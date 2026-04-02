import StSVerify.CardId
import StSVerify.Engine

def cardDefragmentPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := false
  isPower := true
  effects := [.gainFocus 1]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
