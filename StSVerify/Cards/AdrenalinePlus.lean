import StSVerify.CardId
import StSVerify.Engine

def cardAdrenalinePlus : CardDef := {
  cost := 0
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.gainEnergy 2, .drawCards 2, .exhaustSelf]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
