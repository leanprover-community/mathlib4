import Mathlib

open CategoryTheory Limits Opposite CommRingCat

noncomputable section

section TensorProduct
open scoped TensorProduct

universe u

variable (A B : CommRingCat.{u})

@[simps! pt ι]
def tensorProductCocone : BinaryCofan A B :=
BinaryCofan.mk 
  (ofHom (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom : A ⟶  of (A ⊗[ℤ] B))
  (ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom : B ⟶  of (A ⊗[ℤ] B))

@[simp]
theorem tensorProductCocone_inl : (tensorProductCocone A B).inl =
  ofHom (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom := rfl

@[simp]
theorem tensorProductCocone_inr : (tensorProductCocone A B).inr =
  ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom := rfl

@[simps]
def tensorProductColimit : IsColimit (tensorProductCocone A B) where
  desc (s : BinaryCofan A B) :=
    ofHom (Algebra.TensorProduct.lift s.inl.hom.toIntAlgHom s.inr.hom.toIntAlgHom 
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
  uniq (s : BinaryCofan A B) := by
    rintro ⟨m : A ⊗[ℤ] B →+* s.pt⟩ hm
    apply CommRingCat.hom_ext
    apply RingHom.toIntAlgHom_injective
    apply Algebra.TensorProduct.liftEquiv.symm.injective
    apply Subtype.ext
    rw [Algebra.TensorProduct.liftEquiv_symm_apply_coe, Prod.mk.injEq]
    constructor
    · ext a
      dsimp
      rw [map_one, mul_one]
      have : _ = s.inl := hm (Discrete.mk WalkingPair.left)
      rw [←this]
      rfl
    · ext b
      dsimp
      rw [map_one, one_mul]
      have : _ = s.inr := hm (Discrete.mk WalkingPair.right)
      rw [←this]
      rfl

def tensorProductColimitCocone : Limits.ColimitCocone (pair A B) :=
⟨_, tensorProductColimit A B⟩

end TensorProduct

section AffineScheme

open AlgebraicGeometry hiding Spec 
open AffineScheme

universe u

variable (X Y : AffineScheme.{u})

def chosen_finite_products_aux : Cone ((pair (Γ.obj (op X)) (Γ.obj (op Y))).op ⋙ Spec) ≌
  Cone (pair X Y) := 
  (Cones.whiskeringEquivalence (Discrete.opposite _)).symm.trans <| Cones.postcomposeEquivalence <|
    isoWhiskerLeft (Discrete.opposite WalkingPair).inverse 
      (isoWhiskerRight (NatIso.op (pairComp (Γ.obj (op X)) (Γ.obj (op Y)) Spec.rightOp)).symm 
        (unopUnop _)) ≪≫
    Discrete.natIso (fun ⟨j⟩ => by cases j <;> rfl) ≪≫
    mapPairIso X.isoSpec.symm Y.isoSpec.symm

instance AffineScheme.ChosenFiniteProducts : ChosenFiniteProducts AffineScheme.{u} where
  product (X Y : AffineScheme) := ⟨_, IsLimit.ofPreservesConeTerminal
    (chosen_finite_products_aux X Y).functor <|
    isLimitOfPreserves Spec <| IsColimit.op <| tensorProductColimit (Γ.obj (op X)) (Γ.obj (op Y))⟩
  terminal := ⟨_,AffineScheme.isTerminal⟩

open scoped MonoidalCategory
example : X ⊗ Y = Spec.obj (op (of (TensorProduct ℤ (Γ.obj (op X)) (Γ.obj (op Y))))) := rfl

end AffineScheme
