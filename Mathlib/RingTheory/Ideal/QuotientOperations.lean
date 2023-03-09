/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module ring_theory.ideal.quotient_operations
! leanprover-community/mathlib commit e7f0ddbf65bd7181a85edb74b64bdc35ba4bdc74
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.RingTheory.Ideal.Quotient

/-!
# More operations on modules and ideals related to quotients
-/


universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)

/-- The induced map from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_equiv_of_right_inverse`) /
is surjective (`quotient_ker_equiv_of_surjective`).
-/
def kerLift (f : R →+* S) : R ⧸ f.ker →+* S :=
  Ideal.Quotient.lift _ f fun r => f.mem_ker.mp
#align ring_hom.ker_lift RingHom.kerLift

@[simp]
theorem kerLift_mk (f : R →+* S) (r : R) : kerLift f (Ideal.Quotient.mk f.ker r) = f r :=
  Ideal.Quotient.lift_mk _ _ _
#align ring_hom.ker_lift_mk RingHom.kerLift_mk

/-- The induced map from the quotient by the kernel is injective. -/
theorem kerLift_injective (f : R →+* S) : Function.Injective (kerLift f) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : f a = f b) =>
    Ideal.Quotient.eq.2 <| show a - b ∈ ker f by rw [mem_ker, map_sub, h, sub_self]
#align ring_hom.ker_lift_injective RingHom.kerLift_injective

theorem lift_injective_of_ker_le_ideal (I : Ideal R) {f : R →+* S} (H : ∀ a : R, a ∈ I → f a = 0)
    (hI : f.ker ≤ I) : Function.Injective (Ideal.Quotient.lift I f H) :=
  by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro u hu
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [Ideal.Quotient.lift_mk] at hu
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI ((RingHom.mem_ker f).mpr hu)
#align ring_hom.lift_injective_of_ker_le_ideal RingHom.lift_injective_of_ker_le_ideal

variable {f}

/-- The **first isomorphism theorem** for commutative rings, computable version. -/
def quotientKerEquivOfRightInverse {g : S → R} (hf : Function.RightInverse g f) : R ⧸ f.ker ≃+* S :=
  { kerLift f with
    toFun := kerLift f
    invFun := Ideal.Quotient.mk f.ker ∘ g
    left_inv := by
      rintro ⟨x⟩
      apply ker_lift_injective
      simp [hf (f x)]
    right_inv := hf }
#align ring_hom.quotient_ker_equiv_of_right_inverse RingHom.quotientKerEquivOfRightInverse

@[simp]
theorem quotientKerEquivOfRightInverse.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : R ⧸ f.ker) : quotientKerEquivOfRightInverse hf x = kerLift f x :=
  rfl
#align ring_hom.quotient_ker_equiv_of_right_inverse.apply RingHom.quotientKerEquivOfRightInverse.apply

@[simp]
theorem quotientKerEquivOfRightInverse.Symm.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : S) : (quotientKerEquivOfRightInverse hf).symm x = Ideal.Quotient.mk f.ker (g x) :=
  rfl
#align ring_hom.quotient_ker_equiv_of_right_inverse.symm.apply RingHom.quotientKerEquivOfRightInverse.Symm.apply

/-- The **first isomorphism theorem** for commutative rings. -/
noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ f.ker ≃+* S :=
  quotientKerEquivOfRightInverse (Classical.choose_spec hf.HasRightInverse)
#align ring_hom.quotient_ker_equiv_of_surjective RingHom.quotientKerEquivOfSurjective

end RingHom

namespace Ideal

variable {R : Type u} {S : Type v} {F : Type w} [CommRing R] [CommRing S]

@[simp]
theorem map_quotient_self (I : Ideal R) : map (Quotient.mk I) I = ⊥ :=
  eq_bot_iff.2 <|
    Ideal.map_le_iff_le_comap.2 fun x hx =>
      (Submodule.mem_bot (R ⧸ I)).2 <| Ideal.Quotient.eq_zero_iff_mem.2 hx
#align ideal.map_quotient_self Ideal.map_quotient_self

@[simp]
theorem mk_ker {I : Ideal R} : (Quotient.mk I).ker = I := by
  ext <;> rw [RingHom.ker, mem_comap, Submodule.mem_bot, quotient.eq_zero_iff_mem]
#align ideal.mk_ker Ideal.mk_ker

theorem map_mk_eq_bot_of_le {I J : Ideal R} (h : I ≤ J) : I.map J.Quotient.mk = ⊥ :=
  by
  rw [map_eq_bot_iff_le_ker, mk_ker]
  exact h
#align ideal.map_mk_eq_bot_of_le Ideal.map_mk_eq_bot_of_le

theorem ker_quotient_lift {S : Type v} [CommRing S] {I : Ideal R} (f : R →+* S) (H : I ≤ f.ker) :
    (Ideal.Quotient.lift I f H).ker = f.ker.map I.Quotient.mk :=
  by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := quotient.mk_surjective x
    rw [RingHom.mem_ker, ← hy, Ideal.Quotient.lift_mk, ← RingHom.mem_ker] at hx
    rw [← hy, mem_map_iff_of_surjective I.Quotient.mk quotient.mk_surjective]
    exact ⟨y, hx, rfl⟩
  · intro hx
    rw [mem_map_iff_of_surjective I.Quotient.mk quotient.mk_surjective] at hx
    obtain ⟨y, hy⟩ := hx
    rw [RingHom.mem_ker, ← hy.right, Ideal.Quotient.lift_mk, ← RingHom.mem_ker f]
    exact hy.left
#align ideal.ker_quotient_lift Ideal.ker_quotient_lift

@[simp]
theorem bot_quotient_isMaximal_iff (I : Ideal R) : (⊥ : Ideal (R ⧸ I)).IsMaximal ↔ I.IsMaximal :=
  ⟨fun hI =>
    @mk_ker _ _ I ▸
      @comap_isMaximal_of_surjective _ _ _ _ _ _ (Quotient.mk I) Quotient.mk_surjective ⊥ hI,
    fun hI => by
    skip
    letI := quotient.field I
    exact bot_is_maximal⟩
#align ideal.bot_quotient_is_maximal_iff Ideal.bot_quotient_isMaximal_iff

/-- See also `ideal.mem_quotient_iff_mem` in case `I ≤ J`. -/
@[simp]
theorem mem_quotient_iff_mem_sup {I J : Ideal R} {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J ⊔ I := by
  rw [← mem_comap, comap_map_of_surjective (Quotient.mk' I) quotient.mk_surjective, ←
    RingHom.ker_eq_comap_bot, mk_ker]
#align ideal.mem_quotient_iff_mem_sup Ideal.mem_quotient_iff_mem_sup

/-- See also `ideal.mem_quotient_iff_mem_sup` if the assumption `I ≤ J` is not available. -/
theorem mem_quotient_iff_mem {I J : Ideal R} (hIJ : I ≤ J) {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J := by
  rw [mem_quotient_iff_mem_sup, sup_eq_left.mpr hIJ]
#align ideal.mem_quotient_iff_mem Ideal.mem_quotient_iff_mem

section QuotientAlgebra

variable (R₁ R₂ : Type _) {A B : Type _}

variable [CommSemiring R₁] [CommSemiring R₂] [CommRing A] [CommRing B]

variable [Algebra R₁ A] [Algebra R₂ A] [Algebra R₁ B]

/-- The `R₁`-algebra structure on `A/I` for an `R₁`-algebra `A` -/
instance Quotient.algebra {I : Ideal A} : Algebra R₁ (A ⧸ I) :=
  {
    RingHom.comp (Ideal.Quotient.mk I)
      (algebraMap R₁
        A) with
    toFun := fun x => Ideal.Quotient.mk I (algebraMap R₁ A x)
    smul := (· • ·)
    smul_def' := fun r x =>
      Quotient.inductionOn' x fun x =>
        ((Quotient.mk I).congr_arg <| Algebra.smul_def _ _).trans (RingHom.map_mul _ _ _)
    commutes' := fun _ _ => mul_comm _ _ }
#align ideal.quotient.algebra Ideal.Quotient.algebra

-- Lean can struggle to find this instance later if we don't provide this shortcut
instance Quotient.isScalarTower [SMul R₁ R₂] [IsScalarTower R₁ R₂ A] (I : Ideal A) :
    IsScalarTower R₁ R₂ (A ⧸ I) := by infer_instance
#align ideal.quotient.is_scalar_tower Ideal.Quotient.isScalarTower

/-- The canonical morphism `A →ₐ[R₁] A ⧸ I` as morphism of `R₁`-algebras, for `I` an ideal of
`A`, where `A` is an `R₁`-algebra. -/
def Quotient.mkₐ (I : Ideal A) : A →ₐ[R₁] A ⧸ I :=
  ⟨fun a => Submodule.Quotient.mk a, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩
#align ideal.quotient.mkₐ Ideal.Quotient.mkₐ

theorem Quotient.algHom_ext {I : Ideal A} {S} [Semiring S] [Algebra R₁ S] ⦃f g : A ⧸ I →ₐ[R₁] S⦄
    (h : f.comp (Quotient.mkₐ R₁ I) = g.comp (Quotient.mkₐ R₁ I)) : f = g :=
  AlgHom.ext fun x => Quotient.inductionOn' x <| AlgHom.congr_fun h
#align ideal.quotient.alg_hom_ext Ideal.Quotient.algHom_ext

theorem Quotient.alg_map_eq (I : Ideal A) :
    algebraMap R₁ (A ⧸ I) = (algebraMap A (A ⧸ I)).comp (algebraMap R₁ A) :=
  rfl
#align ideal.quotient.alg_map_eq Ideal.Quotient.alg_map_eq

theorem Quotient.mkₐ_toRingHom (I : Ideal A) :
    (Quotient.mkₐ R₁ I).toRingHom = Ideal.Quotient.mk I :=
  rfl
#align ideal.quotient.mkₐ_to_ring_hom Ideal.Quotient.mkₐ_toRingHom

@[simp]
theorem Quotient.mkₐ_eq_mk (I : Ideal A) : ⇑(Quotient.mkₐ R₁ I) = Ideal.Quotient.mk I :=
  rfl
#align ideal.quotient.mkₐ_eq_mk Ideal.Quotient.mkₐ_eq_mk

@[simp]
theorem Quotient.algebraMap_eq (I : Ideal R) : algebraMap R (R ⧸ I) = I.Quotient.mk :=
  rfl
#align ideal.quotient.algebra_map_eq Ideal.Quotient.algebraMap_eq

@[simp]
theorem Quotient.mk_comp_algebraMap (I : Ideal A) :
    (Quotient.mk I).comp (algebraMap R₁ A) = algebraMap R₁ (A ⧸ I) :=
  rfl
#align ideal.quotient.mk_comp_algebra_map Ideal.Quotient.mk_comp_algebraMap

@[simp]
theorem Quotient.mk_algebraMap (I : Ideal A) (x : R₁) :
    Quotient.mk I (algebraMap R₁ A x) = algebraMap R₁ (A ⧸ I) x :=
  rfl
#align ideal.quotient.mk_algebra_map Ideal.Quotient.mk_algebraMap

/-- The canonical morphism `A →ₐ[R₁] I.quotient` is surjective. -/
theorem Quotient.mkₐ_surjective (I : Ideal A) : Function.Surjective (Quotient.mkₐ R₁ I) :=
  surjective_quot_mk _
#align ideal.quotient.mkₐ_surjective Ideal.Quotient.mkₐ_surjective

/-- The kernel of `A →ₐ[R₁] I.quotient` is `I`. -/
@[simp]
theorem Quotient.mkₐ_ker (I : Ideal A) : (Quotient.mkₐ R₁ I : A →+* A ⧸ I).ker = I :=
  Ideal.mk_ker
#align ideal.quotient.mkₐ_ker Ideal.Quotient.mkₐ_ker

variable {R₁}

/-- `ideal.quotient.lift` as an `alg_hom`. -/
def Quotient.liftₐ (I : Ideal A) (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    A ⧸ I →ₐ[R₁] B :=
  {-- this is is_scalar_tower.algebra_map_apply R₁ A (A ⧸ I) but the file `algebra.algebra.tower`
      -- imports this file.
      Ideal.Quotient.lift
      I (f : A →+* B) hI with
    commutes' := fun r =>
      by
      have : algebraMap R₁ (A ⧸ I) r = algebraMap A (A ⧸ I) (algebraMap R₁ A r) := by
        simp_rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
      rw [this, Ideal.Quotient.algebraMap_eq, RingHom.toFun_eq_coe, Ideal.Quotient.lift_mk,
        AlgHom.coe_toRingHom, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        map_smul, map_one] }
#align ideal.quotient.liftₐ Ideal.Quotient.liftₐ

@[simp]
theorem Quotient.liftₐ_apply (I : Ideal A) (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) (x) :
    Ideal.Quotient.liftₐ I f hI x = Ideal.Quotient.lift I (f : A →+* B) hI x :=
  rfl
#align ideal.quotient.liftₐ_apply Ideal.Quotient.liftₐ_apply

theorem Quotient.liftₐ_comp (I : Ideal A) (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    (Ideal.Quotient.liftₐ I f hI).comp (Ideal.Quotient.mkₐ R₁ I) = f :=
  AlgHom.ext fun x => (Ideal.Quotient.lift_mk I (f : A →+* B) hI : _)
#align ideal.quotient.liftₐ_comp Ideal.Quotient.liftₐ_comp

theorem KerLift.map_smul (f : A →ₐ[R₁] B) (r : R₁) (x : A ⧸ f.toRingHom.ker) :
    f.toRingHom.kerLift (r • x) = r • f.toRingHom.kerLift x :=
  by
  obtain ⟨a, rfl⟩ := quotient.mkₐ_surjective R₁ _ x
  rw [← AlgHom.map_smul, quotient.mkₐ_eq_mk, RingHom.kerLift_mk]
  exact f.map_smul _ _
#align ideal.ker_lift.map_smul Ideal.KerLift.map_smul

/-- The induced algebras morphism from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_alg_equiv_of_right_inverse`) /
is surjective (`quotient_ker_alg_equiv_of_surjective`).
-/
def kerLiftAlg (f : A →ₐ[R₁] B) : A ⧸ f.toRingHom.ker →ₐ[R₁] B :=
  AlgHom.mk' f.toRingHom.kerLift fun _ _ => KerLift.map_smul f _ _
#align ideal.ker_lift_alg Ideal.kerLiftAlg

@[simp]
theorem kerLiftAlg_mk (f : A →ₐ[R₁] B) (a : A) :
    kerLiftAlg f (Quotient.mk f.toRingHom.ker a) = f a :=
  rfl
#align ideal.ker_lift_alg_mk Ideal.kerLiftAlg_mk

@[simp]
theorem kerLiftAlg_toRingHom (f : A →ₐ[R₁] B) : (kerLiftAlg f).toRingHom = RingHom.kerLift f :=
  rfl
#align ideal.ker_lift_alg_to_ring_hom Ideal.kerLiftAlg_toRingHom

/-- The induced algebra morphism from the quotient by the kernel is injective. -/
theorem kerLiftAlg_injective (f : A →ₐ[R₁] B) : Function.Injective (kerLiftAlg f) :=
  RingHom.kerLift_injective f
#align ideal.ker_lift_alg_injective Ideal.kerLiftAlg_injective

/-- The **first isomorphism** theorem for algebras, computable version. -/
def quotientKerAlgEquivOfRightInverse {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) : (A ⧸ f.toRingHom.ker) ≃ₐ[R₁] B :=
  { RingHom.quotientKerEquivOfRightInverse fun x => show f.toRingHom (g x) = x from hf x,
    kerLiftAlg f with }
#align ideal.quotient_ker_alg_equiv_of_right_inverse Ideal.quotientKerAlgEquivOfRightInverse

@[simp]
theorem quotientKerAlgEquivOfRightInverse.apply {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) (x : A ⧸ f.toRingHom.ker) :
    quotientKerAlgEquivOfRightInverse hf x = kerLiftAlg f x :=
  rfl
#align ideal.quotient_ker_alg_equiv_of_right_inverse.apply Ideal.quotientKerAlgEquivOfRightInverse.apply

@[simp]
theorem QuotientKerAlgEquivOfRightInverseSymm.apply {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) (x : B) :
    (quotientKerAlgEquivOfRightInverse hf).symm x = Quotient.mkₐ R₁ f.toRingHom.ker (g x) :=
  rfl
#align ideal.quotient_ker_alg_equiv_of_right_inverse_symm.apply Ideal.QuotientKerAlgEquivOfRightInverseSymm.apply

/-- The **first isomorphism theorem** for algebras. -/
noncomputable def quotientKerAlgEquivOfSurjective {f : A →ₐ[R₁] B} (hf : Function.Surjective f) :
    (A ⧸ f.toRingHom.ker) ≃ₐ[R₁] B :=
  quotientKerAlgEquivOfRightInverse (Classical.choose_spec hf.HasRightInverse)
#align ideal.quotient_ker_alg_equiv_of_surjective Ideal.quotientKerAlgEquivOfSurjective

/-- The ring hom `R/I →+* S/J` induced by a ring hom `f : R →+* S` with `I ≤ f⁻¹(J)` -/
def quotientMap {I : Ideal R} (J : Ideal S) (f : R →+* S) (hIJ : I ≤ J.comap f) : R ⧸ I →+* S ⧸ J :=
  Quotient.lift I ((Quotient.mk J).comp f) fun _ ha => by
    simpa [Function.comp_apply, RingHom.coe_comp, quotient.eq_zero_iff_mem] using hIJ ha
#align ideal.quotient_map Ideal.quotientMap

@[simp]
theorem quotientMap_mk {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f} {x : R} :
    quotientMap I f H (Quotient.mk J x) = Quotient.mk I (f x) :=
  Quotient.lift_mk J _ _
#align ideal.quotient_map_mk Ideal.quotientMap_mk

@[simp]
theorem quotientMap_algebraMap {J : Ideal A} {I : Ideal S} {f : A →+* S} {H : J ≤ I.comap f}
    {x : R₁} : quotientMap I f H (algebraMap R₁ (A ⧸ J) x) = Quotient.mk I (f (algebraMap _ _ x)) :=
  Quotient.lift_mk J _ _
#align ideal.quotient_map_algebra_map Ideal.quotientMap_algebraMap

theorem quotientMap_comp_mk {J : Ideal R} {I : Ideal S} {f : R →+* S} (H : J ≤ I.comap f) :
    (quotientMap I f H).comp (Quotient.mk J) = (Quotient.mk I).comp f :=
  RingHom.ext fun x => by simp only [Function.comp_apply, RingHom.coe_comp, Ideal.quotientMap_mk]
#align ideal.quotient_map_comp_mk Ideal.quotientMap_comp_mk

/-- The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+** S`,  where `J = f(I)`. -/
@[simps]
def quotientEquiv (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) :
    R ⧸ I ≃+* S ⧸ J :=
  {
    quotientMap J (↑f)
      (by
        rw [hIJ]
        exact
          @le_comap_map _ S _ _ _ _ _
            _) with
    invFun :=
      quotientMap I (↑f.symm)
        (by
          rw [hIJ]
          exact le_of_eq (map_comap_of_equiv I f))
    left_inv := by
      rintro ⟨r⟩
      simp
    right_inv := by
      rintro ⟨s⟩
      simp }
#align ideal.quotient_equiv Ideal.quotientEquiv

@[simp]
theorem quotientEquiv_mk (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S))
    (x : R) : quotientEquiv I J f hIJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (f x) :=
  rfl
#align ideal.quotient_equiv_mk Ideal.quotientEquiv_mk

@[simp]
theorem quotientEquiv_symm_mk (I : Ideal R) (J : Ideal S) (f : R ≃+* S)
    (hIJ : J = I.map (f : R →+* S)) (x : S) :
    (quotientEquiv I J f hIJ).symm (Ideal.Quotient.mk J x) = Ideal.Quotient.mk I (f.symm x) :=
  rfl
#align ideal.quotient_equiv_symm_mk Ideal.quotientEquiv_symm_mk

/-- `H` and `h` are kept as separate hypothesis since H is used in constructing the quotient map. -/
theorem quotientMap_injective' {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f}
    (h : I.comap f ≤ J) : Function.Injective (quotientMap I f H) :=
  by
  refine' (injective_iff_map_eq_zero (QuotientMap I f H)).2 fun a ha => _
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a
  rw [quotient_map_mk, quotient.eq_zero_iff_mem] at ha
  exact quotient.eq_zero_iff_mem.mpr (h ha)
#align ideal.quotient_map_injective' Ideal.quotientMap_injective'

/-- If we take `J = I.comap f` then `quotient_map` is injective automatically. -/
theorem quotientMap_injective {I : Ideal S} {f : R →+* S} :
    Function.Injective (quotientMap I f le_rfl) :=
  quotientMap_injective' le_rfl
#align ideal.quotient_map_injective Ideal.quotientMap_injective

theorem quotientMap_surjective {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f}
    (hf : Function.Surjective f) : Function.Surjective (quotientMap I f H) := fun x =>
  let ⟨x, hx⟩ := Quotient.mk_surjective x
  let ⟨y, hy⟩ := hf x
  ⟨(Quotient.mk J) y, by simp [hx, hy]⟩
#align ideal.quotient_map_surjective Ideal.quotientMap_surjective

/-- Commutativity of a square is preserved when taking quotients by an ideal. -/
theorem comp_quotientMap_eq_of_comp_eq {R' S' : Type _} [CommRing R'] [CommRing S'] {f : R →+* S}
    {f' : R' →+* S'} {g : R →+* R'} {g' : S →+* S'} (hfg : f'.comp g = g'.comp f) (I : Ideal S') :
    (quotientMap I g' le_rfl).comp (quotientMap (I.comap g') f le_rfl) =
      (quotientMap I f' le_rfl).comp
        (quotientMap (I.comap f') g
          (le_of_eq (trans (comap_comap f g') (hfg ▸ comap_comap g f')))) :=
  by
  refine' RingHom.ext fun a => _
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a
  simp only [RingHom.comp_apply, quotient_map_mk]
  exact congr_arg (Quotient.mk' I) (trans (g'.comp_apply f r).symm (hfg ▸ f'.comp_apply g r))
#align ideal.comp_quotient_map_eq_of_comp_eq Ideal.comp_quotientMap_eq_of_comp_eq

/-- The algebra hom `A/I →+* B/J` induced by an algebra hom `f : A →ₐ[R₁] B` with `I ≤ f⁻¹(J)`. -/
def quotientMapₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (hIJ : I ≤ J.comap f) :
    A ⧸ I →ₐ[R₁] B ⧸ J :=
  { quotientMap J (f : A →+* B) hIJ with commutes' := fun r => by simp }
#align ideal.quotient_mapₐ Ideal.quotientMapₐ

@[simp]
theorem quotient_map_mkₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) {x : A} :
    quotientMapₐ J f H (Quotient.mk I x) = Quotient.mkₐ R₁ J (f x) :=
  rfl
#align ideal.quotient_map_mkₐ Ideal.quotient_map_mkₐ

theorem quotient_map_comp_mkₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) :
    (quotientMapₐ J f H).comp (Quotient.mkₐ R₁ I) = (Quotient.mkₐ R₁ J).comp f :=
  AlgHom.ext fun x => by simp only [quotient_map_mkₐ, quotient.mkₐ_eq_mk, AlgHom.comp_apply]
#align ideal.quotient_map_comp_mkₐ Ideal.quotient_map_comp_mkₐ

/-- The algebra equiv `A/I ≃ₐ[R] B/J` induced by an algebra equiv `f : A ≃ₐ[R] B`,
where`J = f(I)`. -/
def quotientEquivAlg (I : Ideal A) (J : Ideal B) (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
    (A ⧸ I) ≃ₐ[R₁] B ⧸ J :=
  { quotientEquiv I J (f : A ≃+* B) hIJ with commutes' := fun r => by simp }
#align ideal.quotient_equiv_alg Ideal.quotientEquivAlg

instance (priority := 100) quotientAlgebra {I : Ideal A} [Algebra R A] :
    Algebra (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  (quotientMap I (algebraMap R A) (le_of_eq rfl)).toAlgebra
#align ideal.quotient_algebra Ideal.quotientAlgebra

theorem algebraMap_quotient_injective {I : Ideal A} [Algebra R A] :
    Function.Injective (algebraMap (R ⧸ I.comap (algebraMap R A)) (A ⧸ I)) :=
  by
  rintro ⟨a⟩ ⟨b⟩ hab
  replace hab := quotient.eq.mp hab
  rw [← RingHom.map_sub] at hab
  exact quotient.eq.mpr hab
#align ideal.algebra_map_quotient_injective Ideal.algebraMap_quotient_injective

variable (R₁)

/-- Quotienting by equal ideals gives equivalent algebras. -/
def quotientEquivAlgOfEq {I J : Ideal A} (h : I = J) : (A ⧸ I) ≃ₐ[R₁] A ⧸ J :=
  quotientEquivAlg I J AlgEquiv.refl <| h ▸ (map_id I).symm
#align ideal.quotient_equiv_alg_of_eq Ideal.quotientEquivAlgOfEq

@[simp]
theorem quotientEquivAlgOfEq_mk {I J : Ideal A} (h : I = J) (x : A) :
    quotientEquivAlgOfEq R₁ h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl
#align ideal.quotient_equiv_alg_of_eq_mk Ideal.quotientEquivAlgOfEq_mk

@[simp]
theorem quotientEquivAlgOfEq_symm {I J : Ideal A} (h : I = J) :
    (quotientEquivAlgOfEq R₁ h).symm = quotientEquivAlgOfEq R₁ h.symm := by ext <;> rfl
#align ideal.quotient_equiv_alg_of_eq_symm Ideal.quotientEquivAlgOfEq_symm

end QuotientAlgebra

end Ideal

namespace DoubleQuot

open Ideal

variable {R : Type u}

section

variable [CommRing R] (I J : Ideal R)

/-- The obvious ring hom `R/I → R/(I ⊔ J)` -/
def quotLeftToQuotSup : R ⧸ I →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.factor I (I ⊔ J) le_sup_left
#align double_quot.quot_left_to_quot_sup DoubleQuot.quotLeftToQuotSup

/-- The kernel of `quot_left_to_quot_sup` -/
theorem ker_quotLeftToQuotSup : (quotLeftToQuotSup I J).ker = J.map (Ideal.Quotient.mk I) := by
  simp only [mk_ker, sup_idem, sup_comm, quot_left_to_quot_sup, quotient.factor, ker_quotient_lift,
    map_eq_iff_sup_ker_eq_of_surjective I.Quotient.mk quotient.mk_surjective, ← sup_assoc]
#align double_quot.ker_quot_left_to_quot_sup DoubleQuot.ker_quotLeftToQuotSup

/-- The ring homomorphism `(R/I)/J' -> R/(I ⊔ J)` induced by `quot_left_to_quot_sup` where `J'`
  is the image of `J` in `R/I`-/
def quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.lift (J.map (Ideal.Quotient.mk I)) (quot_left_to_quot_sup I J)
    (ker_quot_left_to_quot_sup I J).symm.le
#align double_quot.quot_quot_to_quot_sup DoubleQuot.quotQuotToQuotSup

/-- The composite of the maps `R → (R/I)` and `(R/I) → (R/I)/J'` -/
def quotQuotMk : R →+* (R ⧸ I) ⧸ J.map I.Quotient.mk :=
  (J.map I.Quotient.mk).Quotient.mk.comp I.Quotient.mk
#align double_quot.quot_quot_mk DoubleQuot.quotQuotMk

/-- The kernel of `quot_quot_mk` -/
theorem ker_quotQuotMk : (quotQuotMk I J).ker = I ⊔ J := by
  rw [RingHom.ker_eq_comap_bot, quot_quot_mk, ← comap_comap, ← RingHom.ker, mk_ker,
    comap_map_of_surjective (Ideal.Quotient.mk I) quotient.mk_surjective, ← RingHom.ker, mk_ker,
    sup_comm]
#align double_quot.ker_quot_quot_mk DoubleQuot.ker_quotQuotMk

/-- The ring homomorphism `R/(I ⊔ J) → (R/I)/J' `induced by `quot_quot_mk` -/
def liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I ⊔ J →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  Ideal.Quotient.lift (I ⊔ J) (quotQuotMk I J) (ker_quotQuotMk I J).symm.le
#align double_quot.lift_sup_quot_quot_mk DoubleQuot.liftSupQuotQuotMk

/-- `quot_quot_to_quot_add` and `lift_sup_double_qot_mk` are inverse isomorphisms. In the case where
    `I ≤ J`, this is the Third Isomorphism Theorem (see `quot_quot_equiv_quot_of_le`)-/
def quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J :=
  RingEquiv.ofHomInv (quotQuotToQuotSup I J) (liftSupQuotQuotMk I J)
    (by
      ext z
      rfl)
    (by
      ext z
      rfl)
#align double_quot.quot_quot_equiv_quot_sup DoubleQuot.quotQuotEquivQuotSup

@[simp]
theorem quotQuotEquivQuotSup_quotQuotMk (x : R) :
    quotQuotEquivQuotSup I J (quotQuotMk I J x) = Ideal.Quotient.mk (I ⊔ J) x :=
  rfl
#align double_quot.quot_quot_equiv_quot_sup_quot_quot_mk DoubleQuot.quotQuotEquivQuotSup_quotQuotMk

@[simp]
theorem quotQuotEquivQuotSup_symm_quotQuotMk (x : R) :
    (quotQuotEquivQuotSup I J).symm (Ideal.Quotient.mk (I ⊔ J) x) = quotQuotMk I J x :=
  rfl
#align double_quot.quot_quot_equiv_quot_sup_symm_quot_quot_mk DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk

/-- The obvious isomorphism `(R/I)/J' → (R/J)/I' `   -/
def quotQuotEquivComm : (R ⧸ I) ⧸ J.map I.Quotient.mk ≃+* (R ⧸ J) ⧸ I.map J.Quotient.mk :=
  ((quotQuotEquivQuotSup I J).trans (quotEquivOfEq sup_comm)).trans (quotQuotEquivQuotSup J I).symm
#align double_quot.quot_quot_equiv_comm DoubleQuot.quotQuotEquivComm

@[simp]
theorem quotQuotEquivComm_quotQuotMk (x : R) :
    quotQuotEquivComm I J (quotQuotMk I J x) = quotQuotMk J I x :=
  rfl
#align double_quot.quot_quot_equiv_comm_quot_quot_mk DoubleQuot.quotQuotEquivComm_quotQuotMk

@[simp]
theorem quotQuotEquivComm_comp_quotQuotMk :
    RingHom.comp (↑(quotQuotEquivComm I J)) (quotQuotMk I J) = quotQuotMk J I :=
  RingHom.ext <| quotQuotEquivComm_quotQuotMk I J
#align double_quot.quot_quot_equiv_comm_comp_quot_quot_mk DoubleQuot.quotQuotEquivComm_comp_quotQuotMk

@[simp]
theorem quotQuotEquivComm_symm : (quotQuotEquivComm I J).symm = quotQuotEquivComm J I :=
  rfl
#align double_quot.quot_quot_equiv_comm_symm DoubleQuot.quotQuotEquivComm_symm

variable {I J}

/-- **The Third Isomorphism theorem** for rings. See `quot_quot_equiv_quot_sup` for a version
    that does not assume an inclusion of ideals. -/
def quotQuotEquivQuotOfLe (h : I ≤ J) : (R ⧸ I) ⧸ J.map I.Quotient.mk ≃+* R ⧸ J :=
  (quotQuotEquivQuotSup I J).trans (Ideal.quotEquivOfEq <| sup_eq_right.mpr h)
#align double_quot.quot_quot_equiv_quot_of_le DoubleQuot.quotQuotEquivQuotOfLe

@[simp]
theorem quotQuotEquivQuotOfLe_quotQuotMk (x : R) (h : I ≤ J) :
    quotQuotEquivQuotOfLe h (quotQuotMk I J x) = J.Quotient.mk x :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_quot_quot_mk DoubleQuot.quotQuotEquivQuotOfLe_quotQuotMk

@[simp]
theorem quotQuotEquivQuotOfLe_symm_mk (x : R) (h : I ≤ J) :
    (quotQuotEquivQuotOfLe h).symm (J.Quotient.mk x) = quotQuotMk I J x :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_symm_mk DoubleQuot.quotQuotEquivQuotOfLe_symm_mk

theorem quotQuotEquivQuotOfLe_comp_quotQuotMk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLe h)) (quotQuotMk I J) = J.Quotient.mk := by ext <;> rfl
#align double_quot.quot_quot_equiv_quot_of_le_comp_quot_quot_mk DoubleQuot.quotQuotEquivQuotOfLe_comp_quotQuotMk

theorem quotQuotEquivQuotOfLe_symm_comp_mk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLe h).symm) J.Quotient.mk = quotQuotMk I J := by ext <;> rfl
#align double_quot.quot_quot_equiv_quot_of_le_symm_comp_mk DoubleQuot.quotQuotEquivQuotOfLe_symm_comp_mk

end

section Algebra

@[simp]
theorem quotQuotEquivComm_mk_mk [CommRing R] (I J : Ideal R) (x : R) :
    quotQuotEquivComm I J (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) = algebraMap R _ x :=
  rfl
#align double_quot.quot_quot_equiv_comm_mk_mk DoubleQuot.quotQuotEquivComm_mk_mk

variable [CommSemiring R] {A : Type v} [CommRing A] [Algebra R A] (I J : Ideal A)

@[simp]
theorem quotQuotEquivQuotSup_quot_quot_algebraMap (x : R) :
    DoubleQuot.quotQuotEquivQuotSup I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl
#align double_quot.quot_quot_equiv_quot_sup_quot_quot_algebra_map DoubleQuot.quotQuotEquivQuotSup_quot_quot_algebraMap

@[simp]
theorem quotQuotEquivComm_algebraMap (x : R) :
    quotQuotEquivComm I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl
#align double_quot.quot_quot_equiv_comm_algebra_map DoubleQuot.quotQuotEquivComm_algebraMap

end Algebra

end DoubleQuot

