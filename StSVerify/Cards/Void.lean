import StSVerify.CardId
import StSVerify.Engine

def cardVoid : CardDef := {
  cost := 0
  playable := false
  isAttack := false
  isSkill := false
  isPower := false
  effects := [.exhaustSelf]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
