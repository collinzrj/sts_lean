import StSVerify.CardId
import StSVerify.Engine

def cardSecondWindPlus : CardDef := {
  cost := 2
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.secondWind 7]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
