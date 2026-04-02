import StSVerify.CardId
import StSVerify.Engine

def cardPrayPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.addTokenToDrawPile CardName.Insight]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
