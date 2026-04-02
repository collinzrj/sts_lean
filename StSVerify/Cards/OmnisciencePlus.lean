import StSVerify.CardId
import StSVerify.Engine

def cardOmnisciencePlus : CardDef := {
  cost := 3
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.exhaustSelf]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
