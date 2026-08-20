import Game.Levels.AdvMultiplication.L08mul_eq_zero

World "AdvMultiplication"
Level 9
Title "`mul_left_cancel` 🌶️🌶️"

TheoremTab "*"

namespace MyNat

/-- `mul_left_cancel a b c` is a proof that if `a ≠ 0` and `a * b = a * c` then `b = c`. -/
TheoremDoc MyNat.mul_left_cancel as "mul_left_cancel" in "*"

-- The order matters here: inducting on `b` while `c` is still bound in the goal
-- is what makes the inductive hypothesis general enough. Keep the reminder up
-- through every goal state before that induction, and let it go once the split
-- has happened.
VisualGoalInfoOnGoal below false "∀ (a : ℕ), ∀ (b : ℕ), ∀ (c : ℕ), a ≠ 0 → a * b = a * c → b = c" show "Perform induction on 'b' as soon as it is introduced."
VisualGoalInfoOnGoal below false "∀ (b c : ℕ), a ≠ 0 → a * b = a * c → b = c" show "Perform induction on 'b' as soon as it is introduced."
VisualGoalInfoOnGoal below false "∀ (c : ℕ), a ≠ 0 → a * b = a * c → b = c" show "Perform induction on 'b' as soon as it is introduced."

Introduction
"
In this level we prove that if `a * b = a * c` and `a ≠ 0` then `b = c`. It is tricky, for
several reasons. One of these is that
we need to introduce a new idea: we will need to understand the concept of
mathematical induction a little better.

Starting with `induction b with d hd` is too naive, because in the inductive step
the hypothesis is `a * d = a * c → d = c` but what we know is `a * succ d = a * c`,
so the induction hypothesis does not apply!

Assume `a ≠ 0` is fixed. The actual statement we want to prove by induction on `b` is
\"for all `c`, if `a * b = a * c` then `b = c`\". This *can* be proved by induction,
because we now have the flexibility to change `c`.
"

Statement mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  Hint "The way to start this proof is `induction b with d hd generalizing c`."
  induction b with d hd generalizing c
  · Hint (hidden := true) "Use `mul_eq_zero`. When you have both `a = 0` and `ha : a ≠ 0`, use
  `exfalso` and then `apply ha`."
    rw [mul_zero] at h
    symm at h
    apply mul_eq_zero at h
    cases h with h1 h2
    · exfalso
      apply ha
      exact h1
    · rw [h2]
      rfl
  · Hint "The inductive hypothesis `hd` is \"For all natural numbers `c`, `a * d = a * c → d = c`\".
    You can `apply` it `at` any hypothesis of the form `a * d = a * ?`."
    Hint (hidden := true) "Split into cases `c = 0` and `c = succ e` with `cases c with e`."
    cases c with e
    · rw [mul_succ, mul_zero] at h
      apply add_left_eq_zero at h
      exfalso
      apply ha
      exact h
    · Hint (hidden := true) "Give `hd` the number `{e}` first. Only once its `∀` is gone
      can you apply the implication that remains to `{ha}` and then to `{h}`."
      rw [mul_succ, mul_succ] at h
      apply add_right_cancel at h
      have hde := hd e
      have hde2 := hde ha
      have h2 := hde2 h
      rw [h2]
      rfl
