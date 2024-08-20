import Mathlib.CategoryTheory.SubobjectClassifier.Basic
import Mathlib.CategoryTheory.Types

open CategoryTheory

def prop_map : ⊤_ Type ⟶ Prop := fun _ => True

def prop_c {U X : Type} (f : U ⟶ X) [Mono f] : X ⟶ Prop := fun x =>
  match Classical.propDecidable (∃ u, f u = x) with
    | isTrue _ => True
    | isFalse _ => False

@[simp]
lemma terminal_prop_c_eq_true {U X : Type} (f : U ⟶ X) (u : U) :
  (Limits.terminal.from U ≫ prop_map) u = True := by

    sorry


def prop_isPullback {U X : Type} (f : U ⟶ X) [Mono f] :
  CategoryTheory.IsPullback (Limits.terminal.from U) f prop_map (prop_c f) where
    w := by
      ext u
      dsimp [prop_map, prop_c]
      simp only [true_iff]
      cases Classical.propDecidable (∃ v, f v = f u) with
      | isTrue _ => trivial
      | isFalse _ =>
        letI : (∃ v, f v = f u) := exists_apply_eq_apply f u
        contradiction
    isLimit' := by
      constructor
      constructor
      · intro c j
        ext x
        simp only [types_comp_apply, id_eq, eq_mpr_eq_cast, Limits.PullbackCone.mk_pt,
          Limits.PullbackCone.mk_π_app, Functor.const_obj_obj, Limits.cospan_one]

        sorry
      · intro c m j
        simp only [types_comp_apply, id_eq, eq_mpr_eq_cast, Limits.PullbackCone.mk_pt]
        simp only [Limits.PullbackCone.mk_pt] at m
        simp only [types_comp_apply, id_eq, eq_mpr_eq_cast, Limits.PullbackCone.mk_pt,
          Limits.PullbackCone.mk_π_app, Functor.const_obj_obj, Limits.cospan_one] at j

        sorry
      · sorry

instance prop : SubobjectClassifier Type where
  Ω := Prop
  map := fun _ => True
  c U X f _ x :=
    match Classical.propDecidable (∃ u, f u = x) with
    | isTrue _ => True
    | isFalse _ => False
  isPullback U X f _ := by
    constructor
    ·
      sorry
    · sorry
  isUnique := sorry
