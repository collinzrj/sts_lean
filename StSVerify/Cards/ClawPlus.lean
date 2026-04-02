import StSVerify.CardId
import StSVerify.Engine

def cardClawPlus : CardDef := {
  cost := 0
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 5, .clawScaling]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
