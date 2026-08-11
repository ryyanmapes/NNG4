import Game.MyNat.PeanoAxioms
import Game.Tactic.Decide -- modified decide tactic

namespace MyNat

private theorem succ_ne_zero' (a : MyNat) : succ a ≠ 0 := by
  intro h
  cases h

private theorem succ_ne_succ' (m n : MyNat) (h : m ≠ n) : succ m ≠ succ n := by
  intro hsucc
  exact h (succ_inj m n hsucc)

instance instDecidableEq : DecidableEq MyNat
| 0, 0 => isTrue <| by
  show 0 = 0
  rfl
| succ m, 0 => isFalse <| by
  show succ m ≠ 0
  exact succ_ne_zero' m
| 0, succ n => isFalse <| by
  show 0 ≠ succ n
  exact zero_ne_succ n
| succ m, succ n =>
  match instDecidableEq m n with
  | isTrue (h : m = n) => isTrue <| by
    show succ m = succ n
    rw [h]
  | isFalse (h : m ≠ n) => isFalse <| by
    show succ m ≠ succ n
    exact succ_ne_succ' m n h
