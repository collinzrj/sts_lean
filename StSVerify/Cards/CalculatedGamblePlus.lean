import StSVerify.CardId
import StSVerify.Engine

def cardCalculatedGamblePlus : CardDef := {
  cost := 0
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.discardAllHandAndDraw]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
