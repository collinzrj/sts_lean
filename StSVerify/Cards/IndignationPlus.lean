import StSVerify.CardId
import StSVerify.Engine

def cardIndignationPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.ifNotInStanceEnter .Wrath, .ifInStanceApplyVulnerable .Wrath 4]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
