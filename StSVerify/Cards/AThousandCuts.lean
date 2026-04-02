import StSVerify.CardId
import StSVerify.Engine

def cardAThousandCuts : CardDef := {
  cost := 2
  playable := true
  isAttack := false
  isSkill := false
  isPower := true
  effects := []
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
