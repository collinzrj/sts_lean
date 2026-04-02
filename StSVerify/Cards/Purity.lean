import StSVerify.CardId
import StSVerify.Engine

def cardPurity : CardDef := {
  cost := 0
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.exhaustFromHand 3, .exhaustSelf]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
