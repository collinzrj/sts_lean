import StSVerify.CardId
import StSVerify.Engine

def cardTurboPlus : CardDef := {
  cost := 0
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.gainEnergy 2, .addTokenToDiscard CardName.Void]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
