import StSVerify.CardId
import StSVerify.Engine

def cardZapPlus : CardDef := {
  cost := 0
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.channelOrb .Lightning]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
