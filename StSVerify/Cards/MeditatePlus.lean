import StSVerify.CardId
import StSVerify.Engine

def cardMeditatePlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := []
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
