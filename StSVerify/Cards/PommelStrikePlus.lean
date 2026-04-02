import StSVerify.CardId
import StSVerify.Engine

def cardPommelStrikePlus : CardDef := {
  cost := 1
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 10, .drawCards 2]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
