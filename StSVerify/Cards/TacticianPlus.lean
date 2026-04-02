import StSVerify.CardId
import StSVerify.Engine

def cardTacticianPlus : CardDef := {
  cost := 0
  playable := false
  isAttack := false
  isSkill := true
  isPower := false
  effects := []
  onDiscard := [.gainEnergy 2]
  onDiscardPriority := .top
  onDraw := []
  onExhaust := []
}
