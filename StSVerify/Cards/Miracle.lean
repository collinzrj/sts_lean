import StSVerify.CardId
import StSVerify.Engine

def cardMiracle : CardDef := {
  cost := 0
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.gainEnergy 1, .exhaustSelf]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
