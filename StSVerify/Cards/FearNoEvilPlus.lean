import StSVerify.CardId
import StSVerify.Engine

def cardFearNoEvilPlus : CardDef := {
  cost := 1
  playable := true
  isAttack := true
  isSkill := false
  isPower := false
  effects := [.dealDamage 11, .ifEnemyAttackingEnterStance .Calm]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
