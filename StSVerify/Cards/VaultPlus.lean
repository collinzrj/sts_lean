import StSVerify.CardId
import StSVerify.Engine

def cardVaultPlus : CardDef := {
  cost := 2
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
