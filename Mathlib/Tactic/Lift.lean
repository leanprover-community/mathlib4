/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Tactic.Cases
import Mathlib.Init.Data.Int.Order

/-!
# lift tactic

This file defines the `lift` tactic, allowing the user to lift elements from one type to another
under a specified condition.

## Tags

lift, tactic
-/


/-- A class specifying that you can lift elements from `α` to `β` assuming `cond` is true.
  Used by the tactic `lift`. -/
class CanLift (α β : Sort _) (coe : outParam <| β → α) (cond : outParam <| α → Prop) where
  prf : ∀ x : α, cond x → ∃ y : β, coe y = x
#align can_lift CanLift

instance : CanLift ℤ ℕ (fun n : ℕ ↦ n) ((· ≤ ·) 0) :=
  ⟨fun n hn ↦ ⟨n.natAbs, Int.natAbs_of_nonneg hn⟩⟩

/-- Enable automatic handling of pi types in `can_lift`. -/
instance Pi.canLift (ι : Sort _) (α β : ι → Sort _) (coe : ∀ i, β i → α i) (P : ∀ i, α i → Prop)
    [∀ i, CanLift (α i) (β i) (coe i) (P i)] :
    CanLift (∀ i, α i) (∀ i, β i) (fun f i ↦ coe i (f i)) fun f ↦ ∀ i, P i (f i) where
  prf f hf := ⟨fun i => Classical.choose (CanLift.prf (f i) (hf i)),
    funext fun i => Classical.choose_spec (CanLift.prf (f i) (hf i))⟩
#align pi.can_lift Pi.canLift

theorem Subtype.exists_pi_extension {ι : Sort _} {α : ι → Sort _} [ne : ∀ i, Nonempty (α i)]
    {p : ι → Prop} (f : ∀ i : Subtype p, α i) :
    ∃ g : ∀ i : ι, α i, (fun i : Subtype p => g i) = f := by
  haveI : DecidablePred p := fun i ↦ Classical.propDecidable (p i)
  exact ⟨fun i => if hi : p i then f ⟨i, hi⟩ else Classical.choice (ne i),
    funext fun i ↦ dif_pos i.2⟩
#align subtype.exists_pi_extension Subtype.exists_pi_extension

instance PiSubtype.canLift (ι : Sort _) (α : ι → Sort _) [∀ i, Nonempty (α i)] (p : ι → Prop) :
    CanLift (∀ i : Subtype p, α i) (∀ i, α i) (fun f i => f i) fun _ => True where
  prf f _ := Subtype.exists_pi_extension f
#align pi_subtype.can_lift PiSubtype.canLift

-- TODO: test if we need this instance in Lean 4
instance PiSubtype.canLift' (ι : Sort _) (α : Sort _) [Nonempty α] (p : ι → Prop) :
    CanLift (Subtype p → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι (fun _ => α) p
#align pi_subtype.can_lift' PiSubtype.canLift'

instance Subtype.canLift {α : Sort _} (p : α → Prop) :
    CanLift α { x // p x } Subtype.val p where prf a ha :=
  ⟨⟨a, ha⟩, rfl⟩
#align subtype.can_lift Subtype.canLift

open Tactic

namespace Tactic

/-- Construct the proof of `cond x` in the lift tactic.
*  `e` is the expression being lifted and `h` is the specified proof of `can_lift.cond e`.
*  `old_tp` and `new_tp` are the arguments to `can_lift` and `inst` is the `can_lift`-instance.
*  `s` and `to_unfold` contain the information of the simp set used to simplify.

If the proof was specified, we check whether it has the correct type.
If it doesn't have the correct type, we display an error message.

If the proof was not specified, we create assert it as a local constant.
(The name of this local constant doesn't matter, since `lift` will remove it from the context.)
-/
unsafe def get_lift_prf (h : Option pexpr) (e P : expr) : tactic (expr × Bool) := do
  let expected_prf_ty := P.app e
  let expected_prf_ty ← simp_lemmas.mk.dsimplify [] expected_prf_ty { failIfUnchanged := false }
  match h with
    | some h => do
      let e ← decorate_error "lift tactic failed." (i_to_expr ``(($(h) : $(expected_prf_ty))))
      return (e, tt)
    | none => do
      let prf_nm ← get_unused_name
      let prf ← assert prf_nm expected_prf_ty
      swap
      return (prf, ff)
#align tactic.get_lift_prf tactic.get_lift_prf

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Lift the expression `p` to the type `t`, with proof obligation given by `h`.
        The list `n` is used for the two newly generated names, and to specify whether `h` should
        remain in the local context. See the doc string of `tactic.interactive.lift` for more information.
        -/
    unsafe
  def
    lift
    ( p : pexpr ) ( t : pexpr ) ( h : Option pexpr ) ( n : List Name ) : tactic Unit
    :=
      do
        propositional_goal <|> fail "lift tactic failed. Tactic is only applicable when the target is a proposition."
          let e ← i_to_expr p
          let old_tp ← infer_type e
          let new_tp ← i_to_expr ` `( ( $ ( t ) : Sort _ ) )
          let coe ← i_to_expr ` `( $ ( new_tp ) → $ ( old_tp ) ) >>= mk_meta_var
          let P ← i_to_expr ` `( $ ( old_tp ) → Prop ) >>= mk_meta_var
          let inst_type ← mk_app ` ` CanLift [ old_tp , new_tp , coe , P ]
          let
            inst
              ←
              mk_instance inst_type
                <|>
                (
                    f!
                      "Failed to find a lift from {
                        ( ← old_tp )
                        } to {
                        ( ← new_tp )
                        }. Provide an instance of
                          { ← inst_type }"
                    )
                  >>=
                  fail
          let inst ← instantiate_mvars inst
          let coe ← instantiate_mvars coe
          let P ← instantiate_mvars P
          let ( prf_cond , b ) ← get_lift_prf h e P
          let prf_nm := if prf_cond . is_local_constant then some prf_cond . local_pp_name else none
          let prf_ex0 ← mk_mapp `can_lift.prf [ old_tp , new_tp , coe , P , inst , e ]
          let prf_ex := prf_ex0 prf_cond
          let
            new_nm
              ←
              if
                n ≠ [ ]
                then
                return n . head
                else
                if e . is_local_constant then return e . local_pp_name else get_unused_name
          let
            eq_nm
              ←
              if
                hn
                :
                1 < n . length
                then
                return ( n . nthLe 1 hn )
                else
                if e . is_local_constant then return `rfl else get_unused_name `h
          let temp_nm ← get_unused_name
          let temp_e ← note temp_nm none prf_ex
          dsimp_hyp temp_e none [ ] { failIfUnchanged := ff }
          rcases none ( pexpr.of_expr temp_e ) <| rcases_patt.tuple ( [ new_nm , eq_nm ] . map rcases_patt.one )
          when
            ( ¬ e )
              (
                get_local eq_nm
                  >>=
                  fun e => interactive.rw ⟨ [ ⟨ ⟨ 0 , 0 ⟩ , tt , pexpr.of_expr e ⟩ ] , none ⟩ Interactive.Loc.wildcard
                )
          if h_prf_nm : prf_nm ∧ n 2 ≠ prf_nm then get_local ( Option.get h_prf_nm . 1 ) >>= clear else skip
          if b then skip else swap
#align tactic.lift tactic.lift

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.optional -/
/-- Parses an optional token "using" followed by a trailing `pexpr`. -/
unsafe def using_texpr :=
  parser.optional (tk "using" *> texpr)
#align tactic.using_texpr tactic.using_texpr

/-- Parses a token "to" followed by a trailing `pexpr`. -/
unsafe def to_texpr :=
  tk "to" *> texpr
#align tactic.to_texpr tactic.to_texpr

namespace Interactive

/-- Lift an expression to another type.
* Usage: `'lift' expr 'to' expr ('using' expr)? ('with' id (id id?)?)?`.
* If `n : ℤ` and `hn : n ≥ 0` then the tactic `lift n to ℕ using hn` creates a new
  constant of type `ℕ`, also named `n` and replaces all occurrences of the old variable `(n : ℤ)`
  with `↑n` (where `n` in the new variable). It will remove `n` and `hn` from the context.
  + So for example the tactic `lift n to ℕ using hn` transforms the goal
    `n : ℤ, hn : n ≥ 0, h : P n ⊢ n = 3` to `n : ℕ, h : P ↑n ⊢ ↑n = 3`
    (here `P` is some term of type `ℤ → Prop`).
* The argument `using hn` is optional, the tactic `lift n to ℕ` does the same, but also creates a
  new subgoal that `n ≥ 0` (where `n` is the old variable).
  This subgoal will be placed at the top of the goal list.
  + So for example the tactic `lift n to ℕ` transforms the goal
    `n : ℤ, h : P n ⊢ n = 3` to two goals
    `n : ℤ, h : P n ⊢ n ≥ 0` and `n : ℕ, h : P ↑n ⊢ ↑n = 3`.
* You can also use `lift n to ℕ using e` where `e` is any expression of type `n ≥ 0`.
* Use `lift n to ℕ with k` to specify the name of the new variable.
* Use `lift n to ℕ with k hk` to also specify the name of the equality `↑k = n`. In this case, `n`
  will remain in the context. You can use `rfl` for the name of `hk` to substitute `n` away
  (i.e. the default behavior).
* You can also use `lift e to ℕ with k hk` where `e` is any expression of type `ℤ`.
  In this case, the `hk` will always stay in the context, but it will be used to rewrite `e` in
  all hypotheses and the target.
  + So for example the tactic `lift n + 3 to ℕ using hn with k hk` transforms the goal
    `n : ℤ, hn : n + 3 ≥ 0, h : P (n + 3) ⊢ n + 3 = 2 * n` to the goal
    `n : ℤ, k : ℕ, hk : ↑k = n + 3, h : P ↑k ⊢ ↑k = 2 * n`.
* The tactic `lift n to ℕ using h` will remove `h` from the context. If you want to keep it,
  specify it again as the third argument to `with`, like this: `lift n to ℕ using h with n rfl h`.
* More generally, this can lift an expression from `α` to `β` assuming that there is an instance
  of `can_lift α β`. In this case the proof obligation is specified by `can_lift.cond`.
* Given an instance `can_lift β γ`, it can also lift `α → β` to `α → γ`; more generally, given
  `β : Π a : α, Type*`, `γ : Π a : α, Type*`, and `[Π a : α, can_lift (β a) (γ a)]`, it
  automatically generates an instance `can_lift (Π a, β a) (Π a, γ a)`.

`lift` is in some sense dual to the `zify` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.
-/
unsafe def lift (p : parse texpr) (t : parse to_texpr) (h : parse using_texpr) (n : parse with_ident_list) :
    tactic Unit :=
  tactic.lift p t h n
#align tactic.interactive.lift tactic.interactive.lift

add_tactic_doc
  { Name := "lift", category := DocCategory.tactic, declNames := [`tactic.interactive.lift], tags := ["coercions"] }

end Interactive

end Tactic
