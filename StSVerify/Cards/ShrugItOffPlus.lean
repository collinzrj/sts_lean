import StSVerify.CardId
import StSVerify.Engine

def cardShrugItOffPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.gainBlock 11, .drawCards 1]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
