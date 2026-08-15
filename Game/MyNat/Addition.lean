import Game.MyNat.Definition

namespace MyNat

opaque add : MyNat → MyNat → MyNat

instance instAdd : Add MyNat where
  add := MyNat.add

/--
`add_zero n` is a proof of `n + 0 = n`.

`add_zero` is a `simp` lemma, because if you see `n + 0`
you usually want to simplify it to `n`.
-/
@[simp, MyNat_decide]
axiom add_zero (n : MyNat) : n + 0 = n

/--
If `a` and `b` are natural numbers, then `add_succ a b` is the proof that
`a + succ b = succ (a + b)`.
-/
@[MyNat_decide]
axiom add_succ (a b : MyNat) : a + (succ b) = succ (a + b)
