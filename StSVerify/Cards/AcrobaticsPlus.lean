import StSVerify.CardId
import StSVerify.Engine

def cardAcrobaticsPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.drawCards 4, .discardCards 1]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
