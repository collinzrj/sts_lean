import StSVerify.CardId
import StSVerify.Engine

def cardBashPlus : CardDef := {
  cost := 2
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 10, .applyVulnerable 3]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
