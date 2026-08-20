import Game.Levels.LessOrEqual
import Game.Levels.Multiplication

World "AdvMultiplication"
Level 1
Title "`mul_le_mul_right`"

TheoremTab "*"

namespace MyNat

/-- `mul_le_mul_right a b t` is a proof that `a ≤ b → a * t ≤ b * t`. -/
TheoremDoc MyNat.mul_le_mul_right as "mul_le_mul_right" in "*"

/-- `peano_cases a` is a proof that `a = 0 ∨ ∃ b, a = succ b`: every number is
either zero or a successor. -/
TheoremDoc MyNat.peano_cases as "peano_cases" in "Peano"

NewTheorem MyNat.peano_cases

VisualGoalInfo below false "Two new fundamental theorems have been added to a new Peano tab. \n You may need to use them throughout this world."

Introduction
"Let's warm up with an easy one, which works even if `t = 0`."

Statement mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  cases h with d hd
  use d * t
  rw [hd, add_mul]
  rfl

Conclusion
"My proof:
```
cases h with d hd
use d * t
rw [hd, add_mul]
rfl
```
"
