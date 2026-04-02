import StSVerify.CardId
import StSVerify.Engine

def cardTrueGritPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.gainBlock 9, .exhaustFromHand 1]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
