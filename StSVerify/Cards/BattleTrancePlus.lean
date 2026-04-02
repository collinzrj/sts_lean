import StSVerify.CardId
import StSVerify.Engine

def cardBattleTrancePlus : CardDef := {
  cost := 0
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.drawCards 4, .setNoDraw]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
