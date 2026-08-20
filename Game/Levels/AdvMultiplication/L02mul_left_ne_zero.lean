import Game.Levels.AdvMultiplication.L01mul_le_mul_right

World "AdvMultiplication"
Level 2
Title "`mul_left_ne_zero`"

TheoremTab "*"

namespace MyNat

/-- `mul_left_ne_zero a b` is a proof that `a * b ≠ 0 → b ≠ 0`. -/
TheoremDoc MyNat.mul_left_ne_zero as "mul_left_ne_zero" in "*"

/-- `peano_cases a` is a proof that `a = 0 ∨ ∃ b, a = succ b`: every number is
either zero or a successor. -/
TheoremDoc MyNat.peano_cases as "peano_cases" in "Peano"

NewTheorem MyNat.peano_cases

VisualGoalInfo below false "Two new fundamental theorems have been added to a new Peano tab. You may need to use them throughout this world."

Introduction
"You can use the `contrapose!` tactic here, or follow the manual approach."

Statement mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  Hint "We want to reduce this to a hypothesis `b = 0` and a goal `a * b = 0`,
  which is logically equivalent but much easier to prove. Remember that `X ≠ 0`
  is notation for `X = 0 → False`. Click on `Show more help!` if you need hints."
  Hint (hidden := true) "Start with `intro hb`."
  intro hb
  Hint (hidden := true) "Now `apply h` and you can probably take it from here."
  apply h
  rw [hb, mul_zero]
  rfl
