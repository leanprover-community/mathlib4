import Mathlib.Tactic.Simps.Generalized
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Tests for `simps!!` with `to_dual`

`@[to_dual (attr := simps_proj …)]` registers a declaration and its dual, exchanging `comp` and
`precomp`; `initialize_simps_projections!!` also declares the dual replacements; and
`@[to_dual (attr := simps!!)]` generates the lemmas of a declaration and of its dual, as
translations of each other.

The registrations below use `to_dual existing` on Mathlib declarations that already have a
`to_dual` translation; in Mathlib, `(attr := simps_proj …)` goes in the `to_dual` attribute of the
declaration itself.
-/

open CategoryTheory Limits

namespace SimpsGenToDualTest

set_option linter.translate.overwrite false

/-! ### Registration -/

attribute [to_dual existing (attr := simps_proj) PushoutCocone.inl] PullbackCone.fst
attribute [to_dual existing (attr := simps_proj) PushoutCocone.inr] PullbackCone.snd

-- this also declares that `PushoutCocone.inl` and `PushoutCocone.inr` replace `Cocone.ι`
initialize_simps_projections!! PullbackCone (π → fst snd)

attribute [to_dual existing (attr := simps_proj comp (attr := reassoc (attr := simp))) pushout.inl]
  pullback.fst
attribute [to_dual existing (attr := simps_proj comp (attr := reassoc (attr := simp))) pushout.inr]
  pullback.snd
attribute [to_dual existing (attr := simps_proj precomp noRecurse (attr := reassoc (attr := simp)))
  pushout.desc] pullback.lift

-- registering a declaration again is an error
/-- error: `simps_proj`: pullback.fst is already registered -/
#guard_msgs in
attribute [local simps_proj comp (attr := reassoc (attr := simp))] pullback.fst

-- but stating the replacements again (here, their duals) is harmless
initialize_simps_projections!! PushoutCocone (ι → inl inr)

variable {C : Type*} [Category* C]

/-- The η-rule for morphisms into a pullback. -/
@[to_dual (attr := simps_eta) /-- The η-rule for morphisms out of a pushout. -/]
theorem pullback_eta {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {W : C}
    (h : W ⟶ pullback f g) :
    h = pullback.lift (h ≫ pullback.fst f g) (h ≫ pullback.snd f g)
      (by simp [pullback.condition]) := by
  ext <;> simp

/-- error: `simps_eta`: pullback_eta is already registered -/
#guard_msgs in
attribute [simps_eta] pullback_eta

-- the dual registrations have the dual kinds
open Lean in
run_meta do
  let m := (Simps.Gen.projExt.getState (← getEnv)).2
  for (n, k) in [(``pullback.fst, Simps.Gen.ProjKind.comp), (``pushout.inl, .precomp),
      (``pullback.lift, .precomp), (``pushout.desc, .comp),
      (``PullbackCone.fst, .direct), (``PushoutCocone.inl, .direct)] do
    let some g := m.find? n | throwError "{n} is not registered"
    unless g.kind == k do throwError "{n} has the wrong kind"
  let h := Simps.Gen.hideExt.getState (← getEnv)
  unless h.getD ``PushoutCocone.inr #[] == #[`ι] do throwError "`ι` is not replaced"

/-! ### Definitions -/

variable {X Y Z : C}

/-- A pullback cone, and its dual. -/
@[to_dual (attr := simps!!) /-- A pushout cocone. -/]
def cone {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ g) :
    PullbackCone f g :=
  PullbackCone.mk a b w

/-- An isomorphism between pullbacks, and its dual. -/
@[to_dual (attr := simps!!) pushoutSwap /-- An isomorphism between pushouts. -/]
noncomputable def swap {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [HasPullback g f] :
    pullback f g ≅ pullback g f :=
  pullbackSymmetry f g

/-! ### The generated lemmas -/

section
variable {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ g)

example : (cone a b w).fst = a := cone_fst a b w
#guard_msgs (drop error) in #check cone_π_app

variable [HasPullback f g] [HasPullback g f]

example : swap.hom ≫ pullback.fst g f = pullback.snd f g := swap_hom_fst
example : pullback.lift a b w ≫ swap.hom = pullback.lift b a w.symm := swap_lift_hom a b w
end

section
variable {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (a : Y ⟶ W) (b : Z ⟶ W) (w : f ≫ a = g ≫ b)

example : (cocone a b w).inl = a := cocone_inl a b w
#guard_msgs (drop error) in #check cocone_ι_app

variable [HasPushout f g] [HasPushout g f]

example : pushout.inl f g ≫ pushoutSwap.hom = pushout.inr g f := pushoutSwap_inl_hom
example : pushoutSwap.hom ≫ pushout.desc b a w.symm = pushout.desc a b w :=
  pushoutSwap_hom_desc b a w.symm
end

/-! ### The translations -/

open Lean in
run_meta do
  for (src, tgt) in [(``cone_fst, ``cocone_inl), (``cone_pt, ``cocone_pt),
      (``swap_hom_fst, ``pushoutSwap_inl_inv), (``swap_lift_hom, ``pushoutSwap_inv_desc)] do
    let some tgt' := Mathlib.Tactic.Translate.findTranslationName? (← getEnv)
      Mathlib.Tactic.ToDual.data src | throwError "{src} has no translation"
    unless tgt' == tgt do throwError "{src} is translated to {tgt'}, not {tgt}"

end SimpsGenToDualTest
