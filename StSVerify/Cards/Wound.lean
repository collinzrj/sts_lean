import StSVerify.CardId
import StSVerify.Engine

def cardWound : CardDef := {
  cost := 0
  playable := false
  isAttack := false
  isSkill := false
  isPower := false
  effects := []
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
