import StSVerify.CardId
import StSVerify.Engine

def cardTalkToTheHandPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 7, .exhaustSelf]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
