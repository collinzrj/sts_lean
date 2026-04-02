import StSVerify.CardId
import StSVerify.Engine

def cardGrandFinalePlus : CardDef := {
  cost := 0
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.requireEmptyDrawPile, .dealDamage 60, .exhaustSelf]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
