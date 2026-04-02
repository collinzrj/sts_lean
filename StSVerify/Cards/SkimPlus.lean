import StSVerify.CardId
import StSVerify.Engine

def cardSkimPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.drawCards 4]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
