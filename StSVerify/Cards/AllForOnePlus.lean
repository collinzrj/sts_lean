import StSVerify.CardId
import StSVerify.Engine

def cardAllForOnePlus : CardDef := {
  cost := 2
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 14, .allForOneRetrieve]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
