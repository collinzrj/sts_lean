import StSVerify.CardId
import StSVerify.Engine

def cardDropkick : CardDef := {
  cost := 1
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 5, .ifVulnerableGainEnergy 1, .ifVulnerableDrawCards 1]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
