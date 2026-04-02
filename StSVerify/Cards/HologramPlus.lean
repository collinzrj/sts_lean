import StSVerify.CardId
import StSVerify.Engine

def cardHologramPlus : CardDef := {
  cost := 0
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.gainBlock 5, .hologramRetrieve]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
