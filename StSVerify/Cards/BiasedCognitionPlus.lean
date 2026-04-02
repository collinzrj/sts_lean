import StSVerify.CardId
import StSVerify.Engine

def cardBiasedCognitionPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := false
  isPower := true
  effects := [.gainFocus 4]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
