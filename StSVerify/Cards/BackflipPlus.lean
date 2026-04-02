import StSVerify.CardId
import StSVerify.Engine

def cardBackflipPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.gainBlock 8, .drawCards 2]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
