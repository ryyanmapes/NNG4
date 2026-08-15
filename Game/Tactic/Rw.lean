import Mathlib.Lean.Expr.Basic
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Rewrite

/-!
# Modified `rw`

Modify `rw` to work like `rewrite`.

This is mainly a copy of the implementation of `rewrite` in Lean core.
-/

namespace MyNat

open Lean.Meta Lean.Elab.Tactic Lean.Parser.Tactic

/--
Modified `rw` tactic. For this game, `rw` works exactly like `rewrite`.
-/
syntax (name := rewriteSeq) "rw" (config)? rwRuleSeq (location)? : tactic

@[tactic MyNat.rewriteSeq] def evalRewriteSeq : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (rewriteLocalDecl term symm · cfg)
      (rewriteTarget term symm cfg)
      (throwTacticEx `rewrite · "did not find instance of the pattern in the current goal")

/-- Rewrite only the nth matching occurrence while retaining this game's
weakened `rw` behaviour (in particular, do not close a reflexive goal). */
syntax (name := rwNth) "rw_nth " num rwRuleSeq (location)? : tactic

macro_rules
  | `(tactic| rw_nth $n:num $rules:rwRuleSeq $[$loc:location]?) =>
      `(tactic| rw (occs := .pos [$n]) $rules:rwRuleSeq $[$loc:location]?)
