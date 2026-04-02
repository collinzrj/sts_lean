import StSVerify.CardId
import StSVerify.Engine

def cardCapacitorPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := false
  isPower := true
  effects := [.gainOrbSlots 3]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
