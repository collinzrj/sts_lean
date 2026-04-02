import StSVerify.CardId
import StSVerify.Engine

def cardBeamCellPlus : CardDef := {
  cost := 0
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 4, .applyVulnerable 2]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
