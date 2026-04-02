import StSVerify.CardId
import StSVerify.Engine

def cardCaltropPlus : CardDef := {
  cost := 1
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
