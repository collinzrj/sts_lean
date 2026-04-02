import StSVerify.CardId
import StSVerify.Engine

def cardDeusExMachina : CardDef := {
  cost := 0
  playable := false
  isAttack := false
  isSkill := false
  isPower := false
  effects := []
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := [.addTokensToHand CardName.Miracle 2, .exhaustSelf]
  onExhaust := []
}
