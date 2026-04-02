import StSVerify.CardId
import StSVerify.Engine

def cardCorruption : CardDef := {
  cost := 3
  playable := true
  isAttack := false
  isSkill := false
  isPower := true
  effects := [.setCorruption]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
