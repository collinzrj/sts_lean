import StSVerify.CardId
import StSVerify.Engine

def cardWraithFormPlus : CardDef := {
  cost := 3
  playable := true
  isAttack := false
  isSkill := false
  isPower := true
  effects := []
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
