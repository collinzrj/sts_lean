import StSVerify.CardId
import StSVerify.Engine

def cardImperviousPlus : CardDef := {
  cost := 2
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.gainBlock 40, .exhaustSelf]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
