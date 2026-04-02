import StSVerify.CardId
import StSVerify.Engine

def cardCoolheadedPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.channelOrb .Frost, .drawCards 2]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
