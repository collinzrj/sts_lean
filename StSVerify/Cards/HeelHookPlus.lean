import StSVerify.CardId
import StSVerify.Engine

def cardHeelHookPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 8, .ifWeakGainEnergy 1, .ifWeakDrawCards 1]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
