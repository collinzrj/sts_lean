import StSVerify.CardId
import StSVerify.Engine

def cardVigilancePlus : CardDef := {
  cost := 2
  playable := true
  isAttack := false
  isSkill := true
  isPower := false
  effects := [.gainBlock 12, .enterStance .Calm]
  onDiscard := []
  onDiscardPriority := .bottom
  onDraw := []
  onExhaust := []
}
