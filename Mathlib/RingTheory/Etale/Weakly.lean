/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat

/-!
# Weakly étale algebras

In this file we define weakly étale algebras. An `R`-algebra `S` is weakly étale if
`S` is `R`-flat and the multiplication map `S ⊗[R] S → S` is flat.

## TODOs

- Show that a weakly étale algebra is formally unramified and in particular that
  a weakly étale algebra of finite presentation is étale (@chrisflav).
-/

universe u u₁ u₂ u₃ u₄ u₅

open TensorProduct

@[instance_reducible]
def ULift.algebra' (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    Algebra (ULift.{u} R) A where
  __ := ULift.module
  algebraMap := (algebraMap R A).comp ULift.ringEquiv.toRingHom
  commutes' _ _ := Algebra.commutes ..
  smul_def' _ _ := Algebra.smul_def' ..

def RingHom.ulift {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) :
    ULift.{u₁} R →+* ULift.{u₂} S :=
  RingHom.comp ULift.ringEquiv.symm.toRingHom (f.comp ULift.ringEquiv.toRingHom)

@[simp]
lemma RingHom.down_ulift_apply {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : ULift.{u₁} R) :
    (f.ulift x).down = f x.down :=
  rfl

lemma RingHom.comp_ulift_eq {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) :
    ULift.ringEquiv.toRingHom.comp ((ulift.{u₁, u₂} f).comp ULift.ringEquiv.symm.toRingHom) = f :=
  rfl

attribute [local instance] ULift.algebra' in
def AlgHom.ulift {R S T : Type*} [CommSemiring R] [Semiring S]
    [Semiring T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) :
    ULift.{u₁} S →ₐ[ULift.{u₂} R] ULift.{u₃} T where
  __ := AlgHom.comp ULift.algEquiv.symm.toAlgHom (f.comp ULift.algEquiv.toAlgHom)
  commutes' _ := by simp

@[simp]
lemma AlgHom.down_ulift_apply {R S T : Type*} [CommSemiring R] [Semiring S]
    [Semiring T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (x : ULift S) :
    (f.ulift x).down = f x.down :=
  rfl

lemma AlgHom.ulift_apply {R S T : Type*} [CommSemiring R] [Semiring S]
    [Semiring T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (x : ULift S) :
    f.ulift x = ⟨f x.down⟩ :=
  rfl

lemma RingHom.Flat.iff_ringEquiv_comp {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S}
    {e : S ≃+* T} :
    (e.toRingHom.comp f).Flat ↔ f.Flat := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ .comp hf (.of_bijective e.bijective)⟩
  have : f = e.symm.toRingHom.comp (e.toRingHom.comp f) := by ext; simp
  rw [this]
  exact .comp hf (.of_bijective e.symm.bijective)

lemma RingHom.Flat.iff_comp_ringEquiv {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S}
    {e : T ≃+* R} :
    (f.comp e.toRingHom).Flat ↔ f.Flat := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ .comp (.of_bijective e.bijective) hf⟩
  have : f = (f.comp e.toRingHom).comp e.symm.toRingHom := by ext; simp
  rw [this]
  exact .comp (.of_bijective e.symm.bijective) hf

@[simp]
lemma RingHom.Flat.ulift_iff {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} :
    (ulift.{u₁, u₂} f).Flat ↔ f.Flat := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · rw [← RingHom.comp_ulift_eq.{u₁, u₂} f]
    erw [RingHom.Flat.iff_ringEquiv_comp]
    erw [RingHom.Flat.iff_comp_ringEquiv]
    assumption
  · exact .comp (.comp (.of_bijective <| Equiv.bijective _) hf)
      (.of_bijective <| Equiv.bijective _)

def TensorProduct.congrRing
    {R S : Type*} (M N : Type*) [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] [Module S M] [Module S N]
    [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) :
    M ⊗[R] N ≃ₗ[S] M ⊗[S] N :=
  letI f : M ⊗[R] N →ₗ[S] M ⊗[S] N :=
    { __ := lift ((TensorProduct.mk S M N).restrictScalars₁₂ R R)
      map_smul' s x := by obtain ⟨r, rfl⟩ := h s; simp }
  letI b : M →ₗ[S] N →ₗ[S] M ⊗[R] N := --TensorProduct.mk R M N
    { toFun m :=
        { __ := TensorProduct.mk R M N m
          map_smul' s x := by obtain ⟨r, rfl⟩ := h s; simp }
      map_add' _ _ := by ext; simp
      map_smul' s x := by ext; obtain ⟨r, rfl⟩ := h s; simp }
  .ofLinear f (lift b) (by ext; rfl) (by ext; rfl)

@[simp]
lemma TensorProduct.congrRing_tmul
    {R S M N : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) (m : M) (n : N) :
    TensorProduct.congrRing M N h (m ⊗ₜ[R] n) = m ⊗ₜ[S] n :=
  rfl

@[simp]
lemma TensorProduct.congrRing_symm_tmul
    {R S M N : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) (m : M) (n : N) :
    (TensorProduct.congrRing M N h).symm (m ⊗ₜ[S] n) = m ⊗ₜ[R] n :=
  rfl

def Algebra.TensorProduct.congrRing
    {R S : Type*} (T A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
    [Algebra R S] [IsScalarTower R S A] [IsScalarTower R S B] [Algebra T A]
    (h : Function.Surjective (algebraMap R S)) :
    A ⊗[R] B ≃ₐ[T] A ⊗[S] B where
  __ := _root_.TensorProduct.congrRing A B h
  map_mul' := LinearMap.map_mul_of_map_mul_tmul (by simp)
  commutes' _ := rfl

@[simp]
lemma Algebra.TensorProduct.congrRing_tmul
    {R S : Type*} (T A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
    [Algebra R S] [IsScalarTower R S A] [IsScalarTower R S B] [Algebra T A]
    (h : Function.Surjective (algebraMap R S)) (a : A) (b : B) :
    Algebra.TensorProduct.congrRing T A B h (a ⊗ₜ b) = a ⊗ₜ b :=
  rfl

@[simp]
lemma Algebra.TensorProduct.congrRing_symm_tmul
    {R S : Type*} (T A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
    [Algebra R S] [IsScalarTower R S A] [IsScalarTower R S B] [Algebra T A]
    (h : Function.Surjective (algebraMap R S)) (a : A) (b : B) :
    (Algebra.TensorProduct.congrRing T A B h).symm (a ⊗ₜ b) = a ⊗ₜ b :=
  rfl

def TensorProduct.uliftEquiv
    (R M N : Type*) [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] :
    ULift.{u₁} (M ⊗[R] N) ≃ₗ[R] ULift.{u₂} M ⊗[ULift.{u₃} R] ULift.{u₄} N :=
  ULift.moduleEquiv ≪≫ₗ
    TensorProduct.congr ULift.moduleEquiv.symm ULift.moduleEquiv.symm ≪≫ₗ
    ((TensorProduct.congrRing (R := R) _ _ (by exact ULift.up_surjective)).restrictScalars R)

@[simp]
lemma TensorProduct.down_uliftEquiv_symm_tmul
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (m : ULift M) (n : ULift N) :
    ((TensorProduct.uliftEquiv R M N).symm (m ⊗ₜ n)).down = m.down ⊗ₜ n.down :=
  rfl

@[simp]
lemma TensorProduct.uliftEquiv_tmul
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (m : M) (n : N) :
    TensorProduct.uliftEquiv R M N ⟨m ⊗ₜ n⟩ = ⟨m⟩ ⊗ₜ ⟨n⟩ :=
  rfl

attribute [local instance] ULift.algebra' in
def Algebra.TensorProduct.uliftEquiv
    (R S A B : Type*) [CommSemiring R]
    [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [Semiring B] [Algebra R B] :
    ULift.{u₁} (A ⊗[R] B) ≃ₐ[ULift S] ULift.{u₂} A ⊗[ULift.{u₃} R] ULift.{u₄} B :=
  AlgEquiv.trans ULift.algEquiv
    (.trans (congr ULift.algEquiv.symm ULift.algEquiv.symm) <|
      (congrRing _ _ _ (by exact ULift.up_surjective)))

@[simp]
lemma Algebra.TensorProduct.uliftEquiv_tmul
    (R S A B : Type*) [CommSemiring R]
    [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [Semiring B] [Algebra R B] (a : A) (b : B) :
    uliftEquiv R S A B ⟨a ⊗ₜ b⟩ = ⟨a⟩ ⊗ₜ ⟨b⟩ :=
  rfl

attribute [local instance] ULift.algebra' in
@[simp]
lemma Algebra.TensorProduct.down_uliftEquiv_symm_tmul
    (R S A B : Type*) [CommSemiring R]
    [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [Semiring B] [Algebra R B] (a : ULift A) (b : ULift B) :
    ((uliftEquiv R S A B).symm (a ⊗ₜ b)).down = a.down ⊗ₜ b.down :=
  rfl

attribute [local instance] ULift.algebra' in
lemma Algebra.TensorProduct.uliftEquiv_symm_tmul
    (R S A B : Type*) [CommSemiring R]
    [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [Semiring B] [Algebra R B] (a : ULift A) (b : ULift B) :
    (uliftEquiv R S A B).symm (a ⊗ₜ b) = ⟨a.down ⊗ₜ b.down⟩ :=
  rfl

lemma ULift.algEquiv_symm_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (a : A) :
    ULift.algEquiv (R := R).symm a = ⟨a⟩ := rfl

@[simp]
lemma ULift.down_algEquiv_symm_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (a : A) :
    (ULift.algEquiv (R := R).symm a).down = a := rfl

open CategoryTheory Limits

-- `(S ⊗[R] S) (T ⊗[R] A) S (T ⊗[S] A)`
lemma RingHom.Flat.lift_includeLeft_includeRight {R S : Type u} (T A : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [CommRing A] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    (h : (Algebra.TensorProduct.lmul' (S := S) R).Flat) :
    (Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft)
      (Algebra.TensorProduct.includeRight.restrictScalars R)
      (fun _ _ ↦ .all _ _) : T ⊗[R] A →ₐ[T] T ⊗[S] A).Flat := by
  rw [← CommRingCat.flat_ofHom_iff] at h ⊢
  apply MorphismProperty.of_isPushout _ h
  · exact CommRingCat.ofHom
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T)
      (IsScalarTower.toAlgHom R S A)).toRingHom
  · exact CommRingCat.ofHom
      (RingHom.comp (Algebra.TensorProduct.includeLeft (S := R)).toRingHom (algebraMap S T))
  · refine .of_iso
      (isPushout_map_codiagonal (CommRingCat.ofHom <| algebraMap S T)
        (CommRingCat.ofHom <| algebraMap S A) (CommRingCat.ofHom <| algebraMap R S))
      ?_ ?_ (.refl _) ?_ ?_ ?_ ?_ ?_
    · exact (CommRingCat.isPushout_tensorProduct R S S).isoPushout.symm
    · exact pushout.congrHom (by simp [IsScalarTower.algebraMap_eq R S T])
          (by simp [IsScalarTower.algebraMap_eq R S A]) ≪≫
        (CommRingCat.isPushout_tensorProduct R T A).isoPushout.symm
    · exact (CommRingCat.isPushout_tensorProduct S T A).isoPushout.symm
    all_goals ext <;> simp

namespace Algebra

section

variable (R S A B : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
variable (C : Type*) [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]

noncomputable def IsPushout.cancelBaseChangeAlg : B ⊗[A] C ≃ₐ[S] S ⊗[R] C := by
  refine AlgEquiv.symm
    (AlgEquiv.ofLinearEquiv (IsPushout.cancelBaseChange R S A B C).symm ?_ ?_)
  · simp [TensorProduct.one_def]
  · apply LinearMap.map_mul_of_map_mul_tmul
    simp

@[simp]
lemma IsPushout.toLinearEquiv_cancelBaseChangeAlg :
    (IsPushout.cancelBaseChangeAlg R S A B C).toLinearEquiv =
      IsPushout.cancelBaseChange R S A B C := by
  rfl

@[simp]
lemma IsPushout.cancelBaseChangeAlg_tmul (c : C) :
    IsPushout.cancelBaseChangeAlg R S A B C (1 ⊗ₜ c) = 1 ⊗ₜ c := by
  simp [cancelBaseChangeAlg]

@[simp]
lemma IsPushout.cancelBaseChangeAlg_symm_tmul (s : S) (c : C) :
    (IsPushout.cancelBaseChangeAlg R S A B C).symm (s ⊗ₜ c) = algebraMap S B s ⊗ₜ c := by
  simp [cancelBaseChangeAlg]

variable (D : Type*) [CommRing D] [Algebra R D] [Algebra A D] [IsScalarTower R A D]

attribute [local instance] TensorProduct.rightAlgebra in
lemma IsPushout.cancelBaseChange_symm_comp_lTensor :
    AlgHom.comp (IsPushout.cancelBaseChangeAlg R S A (S ⊗[R] A) C).symm.toAlgHom
      (TensorProduct.lTensor _ (IsScalarTower.toAlgHom R A C)) =
      TensorProduct.includeLeft := by
  ext
  simp [← TensorProduct.one_def, ← TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]

end

section

attribute [local instance] TensorProduct.rightAlgebra in
lemma TensorProduct.flat_lTensor {R S : Type*} (A : Type*) {B D : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]
    {f : B →ₐ[R] D} (hf : f.Flat) :
    (TensorProduct.lTensor (S := S) A f).Flat := by
  algebraize [f.toRingHom, (lTensor (S := A) A f).toRingHom]
  let e : A ⊗[R] D ≃ₐ[A ⊗[R] B] (A ⊗[R] B) ⊗[B] D :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(IsPushout.cancelBaseChange_symm_comp_lTensor R A B D) x) }
  exact .of_linearEquiv e.toLinearEquiv

lemma TensorProduct.flat_map {R S A B C D : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    [Algebra S C] [IsScalarTower R S C] [CommRing D] [Algebra R D]
    {f : A →ₐ[S] C} {g : B →ₐ[R] D}
    (hf : f.Flat) (hg : g.Flat) :
    (TensorProduct.map f g).Flat := by
  have heq : TensorProduct.map f g =
      (TensorProduct.map f (.id R D)).comp (TensorProduct.map (.id _ _) g) := by
    ext <;> simp
  rw [heq]
  refine RingHom.Flat.comp ?_ ?_
  · exact TensorProduct.flat_lTensor _ hg
  · have : (map f (AlgHom.id R D)).restrictScalars R =
        (TensorProduct.comm _ _ _).toAlgHom.comp
          ((lTensor _ (f.restrictScalars R)).comp
            (TensorProduct.comm _ _ _).toAlgHom) := by
      ext <;> simp
    change ((map f (AlgHom.id R D)).restrictScalars R).Flat
    rw [this]
    refine RingHom.Flat.comp ?_ (.of_bijective <| AlgEquiv.bijective _)
    change RingHom.Flat (RingHom.comp (lTensor D (AlgHom.restrictScalars R f)).toRingHom _)
    exact RingHom.Flat.comp (.of_bijective <| (TensorProduct.comm R A D).bijective)
      (TensorProduct.flat_lTensor D hf)

end

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

instance [Etale R S] : Smooth R S where

lemma Etale.of_restrictScalars (R S T : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Etale R S] [Etale R T] :
    Etale S T where
  finitePresentation := .of_restrict_scalars_finitePresentation R S T
  formallyEtale := .of_restrictScalars (R := R)

end

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- `S` is a weakly-étale `R`-algebra if both `R → S` and `S ⊗[R] S → R` are flat. -/
@[stacks 092B, mk_iff]
class WeaklyEtale (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] where
  flat : Module.Flat R S := by infer_instance
  flat_lmul' (R S) : (Algebra.TensorProduct.lmul' R (S := S)).Flat

attribute [instance] WeaklyEtale.flat

attribute [local instance] ULift.algebra' in
lemma Module.Flat.ulift_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat (ULift.{u₁} R) (ULift.{u₂} M) ↔ Module.Flat R M := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : Module.Flat R (ULift.{u₂} M) := .trans _ (ULift.{u₁} R) _
    exact .of_ulift
  · have : Module.Flat (ULift.{u₁} R) R := by
      rw [← RingHom.flat_algebraMap_iff]
      exact .of_bijective ULift.down_bijective
    have : Module.Flat (ULift.{u₁} R) M := .trans _ R _
    exact .ulift

attribute [local instance] ULift.algebra' in
lemma TensorProduct.lmul'_ulift (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] :
    TensorProduct.lmul' (S := ULift.{u₂} S) (ULift.{u₁} R) =
      AlgHom.comp (TensorProduct.lmul' (S := S) R).ulift
        (uliftEquiv R R S S).symm.toAlgHom := by
  ext <;> simp

namespace WeaklyEtale

attribute [local instance] ULift.algebra' in
lemma ulift_iff : WeaklyEtale (ULift.{u₁} R) (ULift.{u₂} S) ↔ WeaklyEtale R S := by
  rw [weaklyEtale_iff, weaklyEtale_iff, Module.Flat.ulift_iff]
  congr!
  conv_rhs => rw [← RingHom.Flat.ulift_iff.{u₁, u₂}]
  rw [TensorProduct.lmul'_ulift, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  exact RingHom.Flat.iff_comp_ringEquiv

@[stacks 092N "(2)"]
instance (priority := low) [Etale R S] : WeaklyEtale R S where
  flat_lmul' := by
    algebraize [Algebra.TensorProduct.lmul' R (S := S) |>.toRingHom]
    have : IsScalarTower R (S ⊗[R] S) S := .of_algHom (Algebra.TensorProduct.lmul' R (S := S))
    have : Etale R (S ⊗[R] S) := .comp _ S _
    have : Etale (S ⊗[R] S) S := .of_restrictScalars R _ _
    exact Smooth.flat (S ⊗[R] S) S

@[stacks 092H]
instance {T : Type*} [CommRing T] [Algebra R T] [WeaklyEtale R S] :
    WeaklyEtale T (T ⊗[R] S) where
  flat_lmul' := by
    let f : (T ⊗[R] S) ⊗[T] (T ⊗[R] S) →ₐ[T] T ⊗[R] S :=
      TensorProduct.lmul' T (S := T ⊗[R] S)
    change RingHom.Flat (R := (T ⊗[R] S) ⊗[T] (T ⊗[R] S)) (S := T ⊗[R] S) f.toRingHom
    let e : T ⊗[R] S ⊗[T] (T ⊗[R] S) ≃ₐ[T] T ⊗[R] (S ⊗[R] S) :=
      ((Algebra.TensorProduct.cancelBaseChange _ _ T _ _)).trans
        (TensorProduct.assoc _ _ _ _ _ _)
    have : f = (TensorProduct.map (.id T T) (TensorProduct.lmul' R)).comp e.toAlgHom := by
      ext <;> simp [e, f, TensorProduct.one_def]
    rw [this]
    refine RingHom.Flat.comp ?_ ?_
    · exact .of_bijective e.bijective
    · refine TensorProduct.flat_map ?_ ?_
      · exact .of_bijective Function.bijective_id
      · exact WeaklyEtale.flat_lmul' R S

attribute [local instance] TensorProduct.rightAlgebra ULift.algebra' in
@[stacks 092J]
lemma trans (R : Type u₁) (S : Type u₂) [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u₃) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [WeaklyEtale R S] [WeaklyEtale S T] : WeaklyEtale R T := by
  rw [← ulift_iff.{max u₁ u₂ u₃, max u₁ u₂ u₃}] at *
  refine ⟨.trans _ (ULift.{max u₁ u₂ u₃} S) _, ?_⟩
  · have heq : TensorProduct.lmul' (S := ULift.{max u₁ u₂ u₃} T) (ULift R) =
        AlgHom.comp ((TensorProduct.lmul' (S := ULift.{max u₁ u₂ u₃} T)
          (ULift.{max u₁ u₂ u₃} S)).restrictScalars (ULift.{max u₁ u₂ u₃} R))
          (TensorProduct.lift
            (TensorProduct.includeLeft)
            (TensorProduct.includeRight.restrictScalars (ULift.{max u₁ u₂ u₃} R))
            fun _ _ ↦ .all _ _) := by
      ext <;> simp
    rw [heq]
    refine .comp ?_ ?_
    · exact (flat_lmul' (ULift R) (ULift S)).lift_includeLeft_includeRight
        (ULift.{max u₁ u₂ u₃} T) (ULift.{max u₁ u₂ u₃} T)
    · exact WeaklyEtale.flat_lmul' (ULift S) (ULift T)

end WeaklyEtale

end Algebra
