import Mathlib

open AlgebraicGeometry CategoryTheory Limits Opposite CommRingCat
open scoped TensorProduct

noncomputable section

universe u v

variable (A B : CommRingCat)

@[simps! pt]
def tensorProductCocone : BinaryCofan A B :=
BinaryCofan.mk 
  (ofHom (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom : A ⟶  of (A ⊗[ℤ] B))
  (ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom : B ⟶  of (A ⊗[ℤ] B))

@[simps]
def tensorProductColimit : IsColimit (tensorProductCocone A B) where
  desc (s : BinaryCofan A B) := (Algebra.TensorProduct.lift s.inl.toIntAlgHom s.inr.toIntAlgHom 
    (fun _ _ => by apply Commute.all)).toRingHom
  fac (s : BinaryCofan A B) := by
    rintro ⟨j⟩
    cases j <;> ext a
    · simp only [forget_obj, pair_obj_left, tensorProductCocone_pt, Functor.const_obj_obj,
        BinaryCofan.ι_app_left, pair_obj_right, AlgHom.toRingHom_eq_coe, CommRingCat.comp_apply,
        coe_of]
      erw [Algebra.TensorProduct.lift_tmul (hfg := fun _ _ => by apply Commute.all)]
      rw [map_one, mul_one]
      rfl
    · simp only [forget_obj, pair_obj_right, tensorProductCocone_pt, Functor.const_obj_obj,
        BinaryCofan.ι_app_right, pair_obj_left, AlgHom.toRingHom_eq_coe, CommRingCat.comp_apply,
        coe_of]
      erw [Algebra.TensorProduct.lift_tmul (hfg := fun _ _ => by apply Commute.all)]
      rw [map_one, one_mul]
      rfl
  uniq := sorry

def tensorProductColimitCocone : Limits.ColimitCocone (pair A B) :=
⟨_, tensorProductColimit A B⟩


example : IsLimit <| Scheme.Spec.mapCone (Limits.Cocone.op (tensorProductCocone A B)) := by
  exact isLimitOfPreserves Scheme.Spec (IsColimit.op (tensorProductColimit A B))


example : IsLimit (asEmptyCone (Spec (of ℤ))) := by 
  exact specZIsTerminal

example : ChosenFiniteProducts AffineScheme where
  product := by
    sorry
  terminal := ⟨_,AffineScheme.specZIsTerminal⟩

