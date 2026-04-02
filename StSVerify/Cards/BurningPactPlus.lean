import StSVerify.CardId
import StSVerify.Engine

def cardBurningPactPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.exhaustFromHand 1, .drawCards 3]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
