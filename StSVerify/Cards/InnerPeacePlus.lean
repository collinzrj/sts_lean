import StSVerify.CardId
import StSVerify.Engine

def cardInnerPeacePlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.ifInStanceDrawCards .Calm 3, .ifNotInStanceEnter .Calm]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
