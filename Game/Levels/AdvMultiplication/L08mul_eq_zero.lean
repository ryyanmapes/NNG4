import Game.Levels.AdvMultiplication.L07mul_ne_zero

World "AdvMultiplication"
Level 8
Title "`mul_eq_zero`"

TheoremTab "*"

namespace MyNat

/-- `mul_eq_zero a b` is a proof that if `a * b = 0` then `a = 0` or `b = 0`. -/
TheoremDoc MyNat.mul_eq_zero as "mul_eq_zero" in "*"

Introduction
"
This level proves that if `a * b = 0` then `a = 0` or `b = 0`. It is
logically equivalent to the last level, so there is a very short proof.
"

Statement mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  Hint "Do a case split on `b` with `cases b with e`. If `b = 0` then the right hand side
  of the goal is already true."
  cases b with e
  · right
    rfl
  · Hint (hidden := true) "Now `b` is `succ e`, so it is the left hand side you can prove.
    Choose it, then rewrite `{h}` with `mul_succ` and finish it off with `add_left_eq_zero`."
    left
    rw [mul_succ] at h
    apply add_left_eq_zero at h
    exact h

Conclusion "Splitting on `b` does all the work. If `b` is a successor then `a * b` is
`a * e + a`, so `a * b = 0` forces `a = 0` and the left hand side is the true one.
"
