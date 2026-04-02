import StSVerify.CardId
import StSVerify.Engine

def cardRebootPlus : CardDef := {
  cost := 0
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.shuffleHandIntoDraw, .drawCards 5, .exhaustSelf]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
