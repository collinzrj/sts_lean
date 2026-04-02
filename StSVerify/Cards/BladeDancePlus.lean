import StSVerify.CardId
import StSVerify.Engine

def cardBladeDancePlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.addTokensToHand CardName.Shiv 4]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
