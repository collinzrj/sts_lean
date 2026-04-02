import StSVerify.CardId
import StSVerify.Engine

def cardPowerThroughPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.gainBlock 20, .addTokensToHand CardName.Wound 2]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
