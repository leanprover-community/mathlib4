/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.well_founded_tactics
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Default
import Leanbin.Init.Data.Sigma.Lex
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Data.List.Instances
import Leanbin.Init.Data.List.Qsort

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer. 
-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.lt_add_of_zero_lt_left (a b : Nat) (h : 0 < b) : a < a + b :=
  show a + 0 < a + b by
    apply Nat.add_lt_add_left
    assumption
#align nat.lt_add_of_zero_lt_left Nat.lt_add_of_zero_lt_left

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.zero_lt_one_add (a : Nat) : 0 < 1 + a :=
  suffices 0 < a + 1 by
    simp [Nat.add_comm]
    assumption
  Nat.zero_lt_succ _
#align nat.zero_lt_one_add Nat.zero_lt_one_add

#print Nat.lt_add_right /-
-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.lt_add_right (a b c : Nat) : a < b → a < b + c := fun h =>
  lt_of_lt_of_le h (Nat.le_add_right _ _)
#align nat.lt_add_right Nat.lt_add_right
-/

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.lt_add_left (a b c : Nat) : a < b → a < c + b := fun h =>
  lt_of_lt_of_le h (Nat.le_add_left _ _)
#align nat.lt_add_left Nat.lt_add_left

protected def PSum.Alt.sizeof.{u, v} {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] : PSum α β → ℕ
  | PSum.inl a => SizeOf.sizeOf a
  | PSum.inr b => SizeOf.sizeOf b
#align psum.alt.sizeof PSum.Alt.sizeof

@[reducible]
protected def PSum.hasSizeofAlt.{u, v} (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] :
    SizeOf (PSum α β) :=
  ⟨PSum.Alt.sizeof⟩
#align psum.has_sizeof_alt PSum.hasSizeofAlt

namespace WellFoundedTactics

open Tactic

def IdTag.wf : Unit :=
  ()
#align well_founded_tactics.id_tag.wf WellFoundedTactics.IdTag.wf

unsafe def mk_alt_sizeof : expr → expr
  | expr.app (expr.app (expr.app (expr.app (expr.const `` PSum.hasSizeof l) α) β) iα) iβ =>
    (expr.const `` PSum.hasSizeofAlt l : expr) α β iα (mk_alt_sizeof iβ)
  | e => e
#align well_founded_tactics.mk_alt_sizeof well_founded_tactics.mk_alt_sizeof

unsafe def default_rel_tac (e : expr) (eqns : List expr) : tactic Unit := do
  let tgt ← target
  let rel ← mk_instance tgt
  exact <|
      match e, Rel with
      | expr.local_const _ (Name.mk_string "_mutual" _) _ _,
        expr.app (e@q(@hasWellFoundedOfHasSizeof _)) sz => e (mk_alt_sizeof sz)
      | _, _ => Rel
#align well_founded_tactics.default_rel_tac well_founded_tactics.default_rel_tac

private unsafe def clear_wf_rec_goal_aux : List expr → tactic Unit
  | [] => return ()
  | h :: hs =>
    clear_wf_rec_goal_aux hs >>
      try (guard (h.local_pp_name.is_internal || h.is_aux_decl) >> clear h)
#align well_founded_tactics.clear_wf_rec_goal_aux well_founded_tactics.clear_wf_rec_goal_aux

unsafe def clear_internals : tactic Unit :=
  local_context >>= clear_wf_rec_goal_aux
#align well_founded_tactics.clear_internals well_founded_tactics.clear_internals

unsafe def unfold_wf_rel : tactic Unit :=
  dunfold_target [`` WellFoundedRelation.R] { failIfUnchanged := false }
#align well_founded_tactics.unfold_wf_rel well_founded_tactics.unfold_wf_rel

unsafe def is_psigma_mk : expr → tactic (expr × expr)
  | q(PSigma.mk $(a) $(b)) => return (a, b)
  | _ => failed
#align well_founded_tactics.is_psigma_mk well_founded_tactics.is_psigma_mk

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
unsafe def process_lex : tactic Unit → tactic Unit
  | tac => do
    let t ← target >>= whnf
    if t `psigma.lex 6 then
        let a := t
        let b := t
        do
        let (a₁, a₂) ← is_psigma_mk a
        let (b₁, b₂) ← is_psigma_mk b
        (is_def_eq a₁ b₁ >> sorry) >> process_lex tac <|> sorry >> tac
      else tac
#align well_founded_tactics.process_lex well_founded_tactics.process_lex

private unsafe def unfold_sizeof_measure : tactic Unit :=
  dunfold_target [`` SizeofMeasure, `` Measure, `` InvImage] { failIfUnchanged := false }
#align well_founded_tactics.unfold_sizeof_measure well_founded_tactics.unfold_sizeof_measure

private unsafe def add_simps : simp_lemmas → List Name → tactic simp_lemmas
  | s, [] => return s
  | s, n :: ns => do
    let s' ← s.add_simp n false
    add_simps s' ns
#align well_founded_tactics.add_simps well_founded_tactics.add_simps

private unsafe def collect_sizeof_lemmas (e : expr) : tactic simp_lemmas :=
  (e.mfold simp_lemmas.mk) fun c d s =>
    if c.is_constant then
      match c.const_name with
      | Name.mk_string "sizeof" p => do
        let eqns ← get_eqn_lemmas_for true c.const_name
        add_simps s eqns
      | _ => return s
    else return s
#align well_founded_tactics.collect_sizeof_lemmas well_founded_tactics.collect_sizeof_lemmas

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def unfold_sizeof_loop : tactic Unit := do
  dunfold_target [`` SizeOf.sizeOf, `` SizeOf.sizeOf] { failIfUnchanged := ff }
  let S ← target >>= collect_sizeof_lemmas
  simp_target S >> unfold_sizeof_loop <|> try sorry
#align well_founded_tactics.unfold_sizeof_loop well_founded_tactics.unfold_sizeof_loop

unsafe def unfold_sizeof : tactic Unit :=
  unfold_sizeof_measure >> unfold_sizeof_loop
#align well_founded_tactics.unfold_sizeof well_founded_tactics.unfold_sizeof

/- The following section should be removed as soon as we implement the
   algebraic normalizer. -/
section SimpleDecTac

open Tactic Expr

-- failed to format: unknown constant 'term.pseudo.antiquot'
private unsafe
  def
    collect_add_args
    : expr → List expr
    | q( $ ( a ) + $ ( b ) ) => collect_add_args a ++ collect_add_args b | e => [ e ]
#align well_founded_tactics.collect_add_args well_founded_tactics.collect_add_args

-- failed to format: unknown constant 'term.pseudo.antiquot'
private unsafe
  def
    mk_nat_add
    : List expr → tactic expr
    | [ ] => to_expr ` `( 0 )
      | [ a ] => return a
      | a :: as => do let rs ← mk_nat_add as to_expr ` `( $ ( a ) + $ ( rs ) )
#align well_founded_tactics.mk_nat_add well_founded_tactics.mk_nat_add

-- failed to format: unknown constant 'term.pseudo.antiquot'
private unsafe
  def
    mk_nat_add_add
    : List expr → List expr → tactic expr
    | [ ] , b => mk_nat_add b
      | a , [ ] => mk_nat_add a
      | a , b => do let t ← mk_nat_add a let s ← mk_nat_add b to_expr ` `( $ ( t ) + $ ( s ) )
#align well_founded_tactics.mk_nat_add_add well_founded_tactics.mk_nat_add_add

private unsafe def get_add_fn (e : expr) : expr :=
  if is_napp_of e `has_add.add 4 then e.app_fn.app_fn else e
#align well_founded_tactics.get_add_fn well_founded_tactics.get_add_fn

private unsafe def prove_eq_by_perm (a b : expr) : tactic expr :=
  is_def_eq a b >> to_expr ``(Eq.refl $(a)) <|>
    perm_ac (get_add_fn a) q(Nat.add_assoc) q(Nat.add_comm) a b
#align well_founded_tactics.prove_eq_by_perm well_founded_tactics.prove_eq_by_perm

private unsafe def num_small_lt (a b : expr) : Bool :=
  if a = b then false
  else
    if is_napp_of a `has_one.one 2 then true
    else if is_napp_of b `has_one.one 2 then false else a.lt b
#align well_founded_tactics.num_small_lt well_founded_tactics.num_small_lt

private unsafe def sort_args (args : List expr) : List expr :=
  args.qsort num_small_lt
#align well_founded_tactics.sort_args well_founded_tactics.sort_args

private def tagged_proof.wf : Unit :=
  ()
#align well_founded_tactics.tagged_proof.wf well_founded_tactics.tagged_proof.wf

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
-- failed to format: unknown constant 'term.pseudo.antiquot'
unsafe
  def
    cancel_nat_add_lt
    : tactic Unit
    :=
      do
        let q( $ ( lhs ) < $ ( rhs ) ) ← target
          let ty ← infer_type lhs >>= whnf
          guard ( ty = q( Nat ) )
          let lhs_args := collect_add_args lhs
          let rhs_args := collect_add_args rhs
          let common := lhs_args . bagInter rhs_args
          if
            common = [ ]
            then
            return ( )
            else
            do
              let lhs_rest := lhs_args common
                let rhs_rest := rhs_args common
                let new_lhs ← mk_nat_add_add common ( sort_args lhs_rest )
                let new_rhs ← mk_nat_add_add common ( sort_args rhs_rest )
                let lhs_pr ← prove_eq_by_perm lhs new_lhs
                let rhs_pr ← prove_eq_by_perm rhs new_rhs
                let
                  target_pr ← to_expr ` `( congr ( congr_arg ( · < · ) $ ( lhs_pr ) ) $ ( rhs_pr ) )
                let new_target ← to_expr ` `( $ ( new_lhs ) < $ ( new_rhs ) )
                replace_target new_target target_pr ` ` id_tag.wf
                sorry <|> sorry
#align well_founded_tactics.cancel_nat_add_lt well_founded_tactics.cancel_nat_add_lt

-- failed to format: unknown constant 'term.pseudo.antiquot'
unsafe
  def check_target_is_value_lt : tactic Unit := do let q( $ ( lhs ) < $ ( rhs ) ) ← target guard lhs
#align well_founded_tactics.check_target_is_value_lt well_founded_tactics.check_target_is_value_lt

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
unsafe def trivial_nat_lt : tactic Unit :=
  comp_val <|>
    sorry <|>
      sorry <|>
        assumption <|>
          (do
              check_target_is_value_lt
              sorry >> trivial_nat_lt <|> sorry >> trivial_nat_lt) <|>
            failed
#align well_founded_tactics.trivial_nat_lt well_founded_tactics.trivial_nat_lt

end SimpleDecTac

unsafe def default_dec_tac : tactic Unit :=
  abstract do
    clear_internals
    unfold_wf_rel
    -- The next line was adapted from code in mathlib by Scott Morrison.
          -- Because `unfold_sizeof` could actually discharge the goal, add a test
          -- using `done` to detect this.
          process_lex
          (unfold_sizeof >>
            (done <|>
              cancel_nat_add_lt >>
                trivial_nat_lt)) <|>-- Clean up the goal state but not too much before printing the error
          unfold_sizeof >>
          fail "default_dec_tac failed"
#align well_founded_tactics.default_dec_tac well_founded_tactics.default_dec_tac

end WellFoundedTactics

/-- Argument for using_well_founded

  The tactic `rel_tac` has to synthesize an element of type (has_well_founded A).
  The two arguments are: a local representing the function being defined by well
  founded recursion, and a list of recursive equations.
  The equations can be used to decide which well founded relation should be used.

  The tactic `dec_tac` has to synthesize decreasing proofs.
-/
unsafe structure well_founded_tactics where
  rel_tac : expr → List expr → tactic Unit := well_founded_tactics.default_rel_tac
  dec_tac : tactic Unit := well_founded_tactics.default_dec_tac
#align well_founded_tactics well_founded_tactics

unsafe def well_founded_tactics.default : well_founded_tactics where
#align well_founded_tactics.default well_founded_tactics.default

