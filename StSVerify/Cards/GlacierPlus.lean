import StSVerify.CardId
import StSVerify.Engine

def cardGlacierPlus : CardDef := {
  cost := 2
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.gainBlock 10, .channelOrb .Frost, .channelOrb .Frost]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
