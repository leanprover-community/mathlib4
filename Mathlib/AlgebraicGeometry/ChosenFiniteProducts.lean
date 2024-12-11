import Mathlib

open AlgebraicGeometry CategoryTheory Limits Opposite CommRingCat
open scoped TensorProduct

noncomputable section

universe u

variable (A B : CommRingCat.{u})

@[simps! pt ι]
def tensorProductCocone : BinaryCofan A B :=
BinaryCofan.mk 
  (ofHom (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom : A ⟶  of (A ⊗[ℤ] B))
  (ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom : B ⟶  of (A ⊗[ℤ] B))

@[simp]
theorem tensorProductCocone_inl : (tensorProductCocone A B).inl =
  (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom := rfl

@[simp]
theorem tensorProductCocone_inr : (tensorProductCocone A B).inr =
  (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom := rfl

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
  uniq (s : BinaryCofan A B) (m : A ⊗[ℤ] B →+* s.pt) := by
    intro hm
    apply RingHom.toIntAlgHom_injective
    apply Algebra.TensorProduct.liftEquiv.symm.injective
    apply Subtype.ext
    rw [Algebra.TensorProduct.liftEquiv_symm_apply_coe, Prod.mk.injEq]
    constructor
    · ext a
      dsimp
      rw [map_one, mul_one]
      exact congrFun (congrArg DFunLike.coe (hm (Discrete.mk WalkingPair.left))) a
    · ext b
      dsimp
      rw [map_one, one_mul]
      exact congrFun (congrArg DFunLike.coe (hm (Discrete.mk WalkingPair.right))) b

def tensorProductColimitCocone : Limits.ColimitCocone (pair A B) :=
⟨_, tensorProductColimit A B⟩

example :(AffineScheme.Spec.mapCone (Limits.Cocone.op (tensorProductCocone A B))).pt =
  AffineScheme.Spec.obj (op (of (A ⊗[ℤ] B))) := by
  rfl

example : IsLimit <| AffineScheme.Spec.mapCone (Limits.Cocone.op (tensorProductCocone A B)) := by
  exact isLimitOfPreserves AffineScheme.Spec (IsColimit.op (tensorProductColimit A B))

example : IsLimit (asEmptyCone (Spec (of ℤ))) := by 
  exact specZIsTerminal

example : ChosenFiniteProducts AffineScheme where
  product (X Y : AffineScheme) :=
    let A := AffineScheme.Γ.obj (op X)
    let B := AffineScheme.Γ.obj (op Y)
    ⟨_,isLimitOfPreserves AffineScheme.Spec (IsColimit.op (tensorProductColimit A B))⟩

  terminal := ⟨_,AffineScheme.specZIsTerminal⟩

