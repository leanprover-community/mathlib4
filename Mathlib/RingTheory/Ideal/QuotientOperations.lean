/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient

#align_import ring_theory.ideal.quotient_operations from "leanprover-community/mathlib"@"b88d81c84530450a8989e918608e5960f015e6c8"

/-!
# More operations on modules and ideals related to quotients
-/

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)

/-- The induced map from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotientKerEquivOfRightInverse`) /
is surjective (`quotientKerEquivOfSurjective`).
-/
def kerLift (f : R →+* S) : R ⧸ ker f →+* S :=
  Ideal.Quotient.lift _ f fun _ => f.mem_ker.mp
#align ring_hom.ker_lift RingHom.kerLift

@[simp]
theorem kerLift_mk (f : R →+* S) (r : R) : kerLift f (Ideal.Quotient.mk (ker f) r) = f r :=
  Ideal.Quotient.lift_mk _ _ _
#align ring_hom.ker_lift_mk RingHom.kerLift_mk

/-- The induced map from the quotient by the kernel is injective. -/
theorem kerLift_injective (f : R →+* S) : Function.Injective (kerLift f) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : f a = f b) =>
    Ideal.Quotient.eq.2 <| show a - b ∈ ker f by rw [mem_ker, map_sub, h, sub_self]
                                                 -- 🎉 no goals
#align ring_hom.ker_lift_injective RingHom.kerLift_injective

theorem lift_injective_of_ker_le_ideal (I : Ideal R) {f : R →+* S} (H : ∀ a : R, a ∈ I → f a = 0)
    (hI : ker f ≤ I) : Function.Injective (Ideal.Quotient.lift I f H) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  -- ⊢ ∀ (x : R ⧸ I), ↑(Ideal.Quotient.lift I f H) x = 0 → x = 0
  intro u hu
  -- ⊢ u = 0
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
  -- ⊢ ↑(Ideal.Quotient.mk I) v = 0
  rw [Ideal.Quotient.lift_mk] at hu
  -- ⊢ ↑(Ideal.Quotient.mk I) v = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  -- ⊢ v ∈ I
  exact hI ((RingHom.mem_ker f).mpr hu)
  -- 🎉 no goals
#align ring_hom.lift_injective_of_ker_le_ideal RingHom.lift_injective_of_ker_le_ideal

variable {f}

/-- The **first isomorphism theorem** for commutative rings, computable version. -/
def quotientKerEquivOfRightInverse {g : S → R} (hf : Function.RightInverse g f) :
    R ⧸ ker f ≃+* S :=
  { kerLift f with
    toFun := kerLift f
    invFun := Ideal.Quotient.mk (ker f) ∘ g
    left_inv := by
      rintro ⟨x⟩
      -- ⊢ (↑(Ideal.Quotient.mk (ker f)) ∘ g) (↑(kerLift f) (Quot.mk Setoid.r x)) = Quo …
      apply kerLift_injective
      -- ⊢ ↑(kerLift f) ((↑(Ideal.Quotient.mk (ker f)) ∘ g) (↑(kerLift f) (Quot.mk Seto …
      simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, kerLift_mk,
        Function.comp_apply, hf (f x)]
    right_inv := hf }
#align ring_hom.quotient_ker_equiv_of_right_inverse RingHom.quotientKerEquivOfRightInverse

@[simp]
theorem quotientKerEquivOfRightInverse.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : R ⧸ ker f) : quotientKerEquivOfRightInverse hf x = kerLift f x :=
  rfl
#align ring_hom.quotient_ker_equiv_of_right_inverse.apply RingHom.quotientKerEquivOfRightInverse.apply

@[simp]
theorem quotientKerEquivOfRightInverse.Symm.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : S) : (quotientKerEquivOfRightInverse hf).symm x = Ideal.Quotient.mk (ker f) (g x) :=
  rfl
#align ring_hom.quotient_ker_equiv_of_right_inverse.symm.apply RingHom.quotientKerEquivOfRightInverse.Symm.apply

/-- The **first isomorphism theorem** for commutative rings. -/
noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ (ker f) ≃+* S :=
  quotientKerEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)
#align ring_hom.quotient_ker_equiv_of_surjective RingHom.quotientKerEquivOfSurjective

end RingHom

namespace Ideal

variable {R : Type u} {S : Type v} {F : Type w} [CommRing R] [CommRing S]

@[simp]
theorem map_quotient_self (I : Ideal R) : map (Quotient.mk I) I = ⊥ :=
  eq_bot_iff.2 <|
    Ideal.map_le_iff_le_comap.2 fun _ hx =>
    -- porting note: Lean can't infer `Module (R ⧸ I) (R ⧸ I)` on its own
      (@Submodule.mem_bot (R ⧸ I) _ _ _ Semiring.toModule _).2 <|
          Ideal.Quotient.eq_zero_iff_mem.2 hx
#align ideal.map_quotient_self Ideal.map_quotient_self

@[simp]
theorem mk_ker {I : Ideal R} : RingHom.ker (Quotient.mk I) = I := by
  ext
  -- ⊢ x✝ ∈ RingHom.ker (Quotient.mk I) ↔ x✝ ∈ I
  rw [RingHom.ker, mem_comap, @Submodule.mem_bot _ _ _ _ Semiring.toModule _,
    Quotient.eq_zero_iff_mem]
#align ideal.mk_ker Ideal.mk_ker

theorem map_mk_eq_bot_of_le {I J : Ideal R} (h : I ≤ J) : I.map (Quotient.mk J) = ⊥ := by
  rw [map_eq_bot_iff_le_ker, mk_ker]
  -- ⊢ I ≤ J
  exact h
  -- 🎉 no goals
#align ideal.map_mk_eq_bot_of_le Ideal.map_mk_eq_bot_of_le

theorem ker_quotient_lift {S : Type v} [CommRing S] {I : Ideal R} (f : R →+* S)
    (H : I ≤ RingHom.ker f) :
    RingHom.ker (Ideal.Quotient.lift I f H) = f.ker.map (Quotient.mk I) := by
  apply Ideal.ext
  -- ⊢ ∀ (x : R ⧸ I), x ∈ RingHom.ker (Quotient.lift I f H) ↔ x ∈ map (Quotient.mk  …
  intro x
  -- ⊢ x ∈ RingHom.ker (Quotient.lift I f H) ↔ x ∈ map (Quotient.mk I) (RingHom.ker …
  constructor
  -- ⊢ x ∈ RingHom.ker (Quotient.lift I f H) → x ∈ map (Quotient.mk I) (RingHom.ker …
  · intro hx
    -- ⊢ x ∈ map (Quotient.mk I) (RingHom.ker f)
    obtain ⟨y, hy⟩ := Quotient.mk_surjective x
    -- ⊢ x ∈ map (Quotient.mk I) (RingHom.ker f)
    rw [RingHom.mem_ker, ← hy, Ideal.Quotient.lift_mk, ← RingHom.mem_ker] at hx
    -- ⊢ x ∈ map (Quotient.mk I) (RingHom.ker f)
    rw [← hy, mem_map_iff_of_surjective (Quotient.mk I) Quotient.mk_surjective]
    -- ⊢ ∃ x, x ∈ RingHom.ker f ∧ ↑(Quotient.mk I) x = ↑(Quotient.mk I) y
    exact ⟨y, hx, rfl⟩
    -- 🎉 no goals
  · intro hx
    -- ⊢ x ∈ RingHom.ker (Quotient.lift I f H)
    rw [mem_map_iff_of_surjective (Quotient.mk I) Quotient.mk_surjective] at hx
    -- ⊢ x ∈ RingHom.ker (Quotient.lift I f H)
    obtain ⟨y, hy⟩ := hx
    -- ⊢ x ∈ RingHom.ker (Quotient.lift I f H)
    rw [RingHom.mem_ker, ← hy.right, Ideal.Quotient.lift_mk]
    -- ⊢ ↑f y = 0
    exact hy.left
    -- 🎉 no goals
#align ideal.ker_quotient_lift Ideal.ker_quotient_lift

@[simp]
theorem bot_quotient_isMaximal_iff (I : Ideal R) : (⊥ : Ideal (R ⧸ I)).IsMaximal ↔ I.IsMaximal :=
  ⟨fun hI =>
    @mk_ker _ _ I ▸
      @comap_isMaximal_of_surjective _ _ _ _ _ _ (Quotient.mk I) Quotient.mk_surjective ⊥ hI,
    fun hI => by
    skip
    -- ⊢ IsMaximal ⊥
    letI := Quotient.field I
    -- ⊢ IsMaximal ⊥
    exact bot_isMaximal⟩
    -- 🎉 no goals
#align ideal.bot_quotient_is_maximal_iff Ideal.bot_quotient_isMaximal_iff

/-- See also `Ideal.mem_quotient_iff_mem` in case `I ≤ J`. -/
@[simp]
theorem mem_quotient_iff_mem_sup {I J : Ideal R} {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J ⊔ I := by
  rw [← mem_comap, comap_map_of_surjective (Quotient.mk I) Quotient.mk_surjective, ←
    RingHom.ker_eq_comap_bot, mk_ker]
#align ideal.mem_quotient_iff_mem_sup Ideal.mem_quotient_iff_mem_sup

/-- See also `Ideal.mem_quotient_iff_mem_sup` if the assumption `I ≤ J` is not available. -/
theorem mem_quotient_iff_mem {I J : Ideal R} (hIJ : I ≤ J) {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J := by
  rw [mem_quotient_iff_mem_sup, sup_eq_left.mpr hIJ]
  -- 🎉 no goals
#align ideal.mem_quotient_iff_mem Ideal.mem_quotient_iff_mem

section QuotientAlgebra

variable (R₁ R₂ : Type*) {A B : Type*}

variable [CommSemiring R₁] [CommSemiring R₂] [CommRing A] [CommRing B]

variable [Algebra R₁ A] [Algebra R₂ A] [Algebra R₁ B]

/-- The `R₁`-algebra structure on `A/I` for an `R₁`-algebra `A` -/
instance Quotient.algebra {I : Ideal A} : Algebra R₁ (A ⧸ I) :=
  { toRingHom :=  RingHom.comp (Ideal.Quotient.mk I) (algebraMap R₁ A)
    smul_def' := fun _ x =>
      Quotient.inductionOn' x fun _ =>
        ((Quotient.mk I).congr_arg <| Algebra.smul_def _ _).trans (RingHom.map_mul _ _ _)
    commutes' := fun _ _ => mul_comm _ _ }
#align ideal.quotient.algebra Ideal.Quotient.algebra

-- Lean can struggle to find this instance later if we don't provide this shortcut
-- Porting note: this can probably now be deleted
-- update: maybe not - removal causes timeouts
instance Quotient.isScalarTower [SMul R₁ R₂] [IsScalarTower R₁ R₂ A] (I : Ideal A) :
    IsScalarTower R₁ R₂ (A ⧸ I) := by infer_instance
                                      -- 🎉 no goals
#align ideal.quotient.is_scalar_tower Ideal.Quotient.isScalarTower

/-- The canonical morphism `A →ₐ[R₁] A ⧸ I` as morphism of `R₁`-algebras, for `I` an ideal of
`A`, where `A` is an `R₁`-algebra. -/
def Quotient.mkₐ (I : Ideal A) : A →ₐ[R₁] A ⧸ I :=
  ⟨⟨⟨⟨fun a => Submodule.Quotient.mk a, rfl⟩, fun _ _ => rfl⟩, rfl, fun _ _ => rfl⟩, fun _ => rfl⟩
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
theorem Quotient.mkₐ_eq_mk (I : Ideal A) : ⇑(Quotient.mkₐ R₁ I) = Quotient.mk I :=
  rfl
#align ideal.quotient.mkₐ_eq_mk Ideal.Quotient.mkₐ_eq_mk

@[simp]
theorem Quotient.algebraMap_eq (I : Ideal R) : algebraMap R (R ⧸ I) = Quotient.mk I :=
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
theorem Quotient.mkₐ_ker (I : Ideal A) : RingHom.ker (Quotient.mkₐ R₁ I : A →+* A ⧸ I) = I :=
  Ideal.mk_ker
#align ideal.quotient.mkₐ_ker Ideal.Quotient.mkₐ_ker

variable {R₁}

/-- `Ideal.quotient.lift` as an `AlgHom`. -/
def Quotient.liftₐ (I : Ideal A) (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    A ⧸ I →ₐ[R₁] B :=
  {-- this is IsScalarTower.algebraMap_apply R₁ A (A ⧸ I) but the file `Algebra.Algebra.Tower`
      -- imports this file.
      Ideal.Quotient.lift
      I (f : A →+* B) hI with
    commutes' := fun r => by
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
  AlgHom.ext fun _ => (Ideal.Quotient.lift_mk I (f : A →+* B) hI : _)
#align ideal.quotient.liftₐ_comp Ideal.Quotient.liftₐ_comp

theorem KerLift.map_smul (f : A →ₐ[R₁] B) (r : R₁) (x : A ⧸ (RingHom.ker f.toRingHom)) :
    f.toRingHom.kerLift (r • x) = r • f.toRingHom.kerLift x := by
  obtain ⟨a, rfl⟩ := Quotient.mkₐ_surjective R₁ _ x
  -- ⊢ ↑(RingHom.kerLift ↑f) (r • ↑(Quotient.mkₐ R₁ (RingHom.ker ↑f)) a) = r • ↑(Ri …
  exact f.map_smul _ _
  -- 🎉 no goals
#align ideal.ker_lift.map_smul Ideal.KerLift.map_smul

/-- The induced algebras morphism from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotientKerAlgEquivOfRightInverse`) /
is surjective (`quotientKerAlgEquivOfSurjective`).
-/
def kerLiftAlg (f : A →ₐ[R₁] B) : A ⧸ (RingHom.ker f.toRingHom) →ₐ[R₁] B :=
  AlgHom.mk' f.toRingHom.kerLift fun _ _ => KerLift.map_smul f _ _
#align ideal.ker_lift_alg Ideal.kerLiftAlg

-- Porting note: changed from f.toRingHom to f on LHS since f.toRingHom = f is in simp
@[simp]
theorem kerLiftAlg_mk (f : A →ₐ[R₁] B) (a : A) :
    kerLiftAlg f (Quotient.mk (RingHom.ker f) a) = f a := by
  rfl
  -- 🎉 no goals
#align ideal.ker_lift_alg_mk Ideal.kerLiftAlg_mk

-- Porting note: not sure about this simpNF
-- The linter says:
-- #check Ideal.kerLiftAlg_toRingHom.{u_3, u_2, u_1} /- Left-hand side simplifies from
--   ↑(Ideal.kerLiftAlg f)
-- to
--   ↑(Ideal.kerLiftAlg f)
-- using
--   simp only [@AlgHom.toRingHom_eq_coe]
@[simp, nolint simpNF]
theorem kerLiftAlg_toRingHom (f : A →ₐ[R₁] B) :
    (kerLiftAlg f).toRingHom = RingHom.kerLift (f : A →+* B) :=
  rfl
#align ideal.ker_lift_alg_to_ring_hom Ideal.kerLiftAlg_toRingHom

-- Porting note: short circuit tc synth and use unification (_)
/-- The induced algebra morphism from the quotient by the kernel is injective. -/
theorem kerLiftAlg_injective (f : A →ₐ[R₁] B) : Function.Injective (kerLiftAlg f) :=
  @RingHom.kerLift_injective A B (_) (_) f
#align ideal.ker_lift_alg_injective Ideal.kerLiftAlg_injective

/-- The **first isomorphism** theorem for algebras, computable version. -/
def quotientKerAlgEquivOfRightInverse {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) : (A ⧸ (RingHom.ker f.toRingHom)) ≃ₐ[R₁] B :=
  { RingHom.quotientKerEquivOfRightInverse fun x => show f.toRingHom (g x) = x from hf x,
    kerLiftAlg f with }
#align ideal.quotient_ker_alg_equiv_of_right_inverse Ideal.quotientKerAlgEquivOfRightInverse

@[simp]
theorem quotientKerAlgEquivOfRightInverse.apply {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) (x : A ⧸ (RingHom.ker f.toRingHom)) :
    quotientKerAlgEquivOfRightInverse hf x = kerLiftAlg f x :=
  rfl
#align ideal.quotient_ker_alg_equiv_of_right_inverse.apply Ideal.quotientKerAlgEquivOfRightInverse.apply

@[simp]
theorem QuotientKerAlgEquivOfRightInverseSymm.apply {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) (x : B) : (quotientKerAlgEquivOfRightInverse hf).symm x =
    Quotient.mkₐ R₁ (RingHom.ker f.toRingHom) (g x) :=
  rfl
#align ideal.quotient_ker_alg_equiv_of_right_inverse_symm.apply Ideal.QuotientKerAlgEquivOfRightInverseSymm.apply

/-- The **first isomorphism theorem** for algebras. -/
noncomputable def quotientKerAlgEquivOfSurjective {f : A →ₐ[R₁] B} (hf : Function.Surjective f) :
    (A ⧸ (RingHom.ker f.toRingHom)) ≃ₐ[R₁] B :=
  quotientKerAlgEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)
#align ideal.quotient_ker_alg_equiv_of_surjective Ideal.quotientKerAlgEquivOfSurjective

/-- The ring hom `R/I →+* S/J` induced by a ring hom `f : R →+* S` with `I ≤ f⁻¹(J)` -/
def quotientMap {I : Ideal R} (J : Ideal S) (f : R →+* S) (hIJ : I ≤ J.comap f) : R ⧸ I →+* S ⧸ J :=
  Quotient.lift I ((Quotient.mk J).comp f) fun _ ha => by
    simpa [Function.comp_apply, RingHom.coe_comp, Quotient.eq_zero_iff_mem] using hIJ ha
    -- 🎉 no goals
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
                          -- 🎉 no goals
#align ideal.quotient_map_comp_mk Ideal.quotientMap_comp_mk

/-- The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+** S`, where `J = f(I)`. -/
@[simps]
def quotientEquiv (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) :
    R ⧸ I ≃+* S ⧸ J :=
  {
    quotientMap J (↑f)
      (by
        rw [hIJ]
        -- ⊢ I ≤ comap (↑f) (map (↑f) I)
        exact
          @le_comap_map _ S _ _ _ _ _
            _) with
    invFun :=
      quotientMap I (↑f.symm)
        (by
          rw [hIJ]
          -- ⊢ map (↑f) I ≤ comap (↑(RingEquiv.symm f)) I
          exact le_of_eq (map_comap_of_equiv I f))
          -- 🎉 no goals
    left_inv := by
      rintro ⟨r⟩
      -- ⊢ ↑(quotientMap I ↑(RingEquiv.symm f) (_ : J ≤ comap (↑(RingEquiv.symm f)) I)) …
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
        quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    right_inv := by
      rintro ⟨s⟩
      -- ⊢ OneHom.toFun (↑↑src✝) (↑(quotientMap I ↑(RingEquiv.symm f) (_ : J ≤ comap (↑ …
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
        quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] }
#align ideal.quotient_equiv Ideal.quotientEquiv

/- Porting note: removed simp. LHS simplified. Slightly different version of the simplified
form closed this and was itself closed by simp -/
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
    (h : I.comap f ≤ J) : Function.Injective (quotientMap I f H) := by
  refine' (injective_iff_map_eq_zero (quotientMap I f H)).2 fun a ha => _
  -- ⊢ a = 0
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  -- ⊢ ↑(Quotient.mk J) r = 0
  rw [quotientMap_mk, Quotient.eq_zero_iff_mem] at ha
  -- ⊢ ↑(Quotient.mk J) r = 0
  exact Quotient.eq_zero_iff_mem.mpr (h ha)
  -- 🎉 no goals
#align ideal.quotient_map_injective' Ideal.quotientMap_injective'

/-- If we take `J = I.comap f` then `QuotientMap` is injective automatically. -/
theorem quotientMap_injective {I : Ideal S} {f : R →+* S} :
    Function.Injective (quotientMap I f le_rfl) :=
  quotientMap_injective' le_rfl
#align ideal.quotient_map_injective Ideal.quotientMap_injective

theorem quotientMap_surjective {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f}
    (hf : Function.Surjective f) : Function.Surjective (quotientMap I f H) := fun x =>
  let ⟨x, hx⟩ := Quotient.mk_surjective x
  let ⟨y, hy⟩ := hf x
  ⟨(Quotient.mk J) y, by simp [hx, hy]⟩
                         -- 🎉 no goals
#align ideal.quotient_map_surjective Ideal.quotientMap_surjective

/-- Commutativity of a square is preserved when taking quotients by an ideal. -/
theorem comp_quotientMap_eq_of_comp_eq {R' S' : Type*} [CommRing R'] [CommRing S'] {f : R →+* S}
    {f' : R' →+* S'} {g : R →+* R'} {g' : S →+* S'} (hfg : f'.comp g = g'.comp f) (I : Ideal S') :
    -- Porting note: was losing track of I
    let leq := le_of_eq (_root_.trans (comap_comap (I := I) f g') (hfg ▸ comap_comap (I := I) g f'))
    (quotientMap I g' le_rfl).comp (quotientMap (I.comap g') f le_rfl) =
    (quotientMap I f' le_rfl).comp (quotientMap (I.comap f') g leq) := by
  refine RingHom.ext fun a => ?_
  -- ⊢ ↑(RingHom.comp (quotientMap I g' (_ : comap g' I ≤ comap g' I)) (quotientMap …
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  -- ⊢ ↑(RingHom.comp (quotientMap I g' (_ : comap g' I ≤ comap g' I)) (quotientMap …
  simp only [RingHom.comp_apply, quotientMap_mk]
  -- ⊢ ↑(Quotient.mk I) (↑g' (↑f r)) = ↑(Quotient.mk I) (↑f' (↑g r))
  exact congr_arg (Ideal.Quotient.mk I) (_root_.trans (g'.comp_apply f r).symm
    (hfg ▸ f'.comp_apply g r))
#align ideal.comp_quotient_map_eq_of_comp_eq Ideal.comp_quotientMap_eq_of_comp_eq

/-- The algebra hom `A/I →+* B/J` induced by an algebra hom `f : A →ₐ[R₁] B` with `I ≤ f⁻¹(J)`. -/
def quotientMapₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (hIJ : I ≤ J.comap f) :
    A ⧸ I →ₐ[R₁] B ⧸ J :=
  { quotientMap J (f : A →+* B) hIJ with commutes' := fun r => by simp only [RingHom.toFun_eq_coe,
    quotientMap_algebraMap, AlgHom.coe_toRingHom, AlgHom.commutes, Quotient.mk_algebraMap] }
#align ideal.quotient_mapₐ Ideal.quotientMapₐ

@[simp]
theorem quotient_map_mkₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) {x : A} :
    quotientMapₐ J f H (Quotient.mk I x) = Quotient.mkₐ R₁ J (f x) :=
  rfl
#align ideal.quotient_map_mkₐ Ideal.quotient_map_mkₐ

theorem quotient_map_comp_mkₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) :
    (quotientMapₐ J f H).comp (Quotient.mkₐ R₁ I) = (Quotient.mkₐ R₁ J).comp f :=
  AlgHom.ext fun x => by simp only [quotient_map_mkₐ, Quotient.mkₐ_eq_mk, AlgHom.comp_apply]
                         -- 🎉 no goals
#align ideal.quotient_map_comp_mkₐ Ideal.quotient_map_comp_mkₐ

/-- The algebra equiv `A/I ≃ₐ[R] B/J` induced by an algebra equiv `f : A ≃ₐ[R] B`,
where`J = f(I)`. -/
def quotientEquivAlg (I : Ideal A) (J : Ideal B) (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
    (A ⧸ I) ≃ₐ[R₁] B ⧸ J :=
  { quotientEquiv I J (f : A ≃+* B) hIJ with
    commutes' := fun r => by
      -- Porting note: Needed to add the below lemma because Equivs coerce weird
      have : ∀ (e : RingEquiv (A ⧸ I) (B ⧸ J)), Equiv.toFun e.toEquiv = FunLike.coe e := fun _ ↦ rfl
      -- ⊢ Equiv.toFun src✝.toEquiv (↑(algebraMap R₁ (A ⧸ I)) r) = ↑(algebraMap R₁ (B ⧸ …
      rw [this]
      -- ⊢ ↑src✝ (↑(algebraMap R₁ (A ⧸ I)) r) = ↑(algebraMap R₁ (B ⧸ J)) r
      simp only [quotientEquiv_apply, RingHom.toFun_eq_coe, quotientMap_algebraMap,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, Quotient.mk_algebraMap]}
#align ideal.quotient_equiv_alg Ideal.quotientEquivAlg

instance (priority := 100) quotientAlgebra {I : Ideal A} [Algebra R A] :
    Algebra (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  (quotientMap I (algebraMap R A) (le_of_eq rfl)).toAlgebra
#align ideal.quotient_algebra Ideal.quotientAlgebra

theorem algebraMap_quotient_injective {I : Ideal A} [Algebra R A] :
    Function.Injective (algebraMap (R ⧸ I.comap (algebraMap R A)) (A ⧸ I)) := by
  rintro ⟨a⟩ ⟨b⟩ hab
  -- ⊢ Quot.mk Setoid.r a = Quot.mk Setoid.r b
  replace hab := Quotient.eq.mp hab
  -- ⊢ Quot.mk Setoid.r a = Quot.mk Setoid.r b
  rw [← RingHom.map_sub] at hab
  -- ⊢ Quot.mk Setoid.r a = Quot.mk Setoid.r b
  exact Quotient.eq.mpr hab
  -- 🎉 no goals
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
    (quotientEquivAlgOfEq R₁ h).symm = quotientEquivAlgOfEq R₁ h.symm := by
  ext
  -- ⊢ ↑(AlgEquiv.symm (quotientEquivAlgOfEq R₁ h)) a✝ = ↑(quotientEquivAlgOfEq R₁  …
  rfl
  -- 🎉 no goals
#align ideal.quotient_equiv_alg_of_eq_symm Ideal.quotientEquivAlgOfEq_symm

lemma comap_map_mk {I J : Ideal R} (h : I ≤ J) :
    Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = J :=
  by ext; rw [← Ideal.mem_quotient_iff_mem h, Ideal.mem_comap]
     -- ⊢ x✝ ∈ comap (Quotient.mk I) (map (Quotient.mk I) J) ↔ x✝ ∈ J
          -- 🎉 no goals

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

/-- The kernel of `quotLeftToQuotSup` -/
theorem ker_quotLeftToQuotSup : RingHom.ker (quotLeftToQuotSup I J) =
    J.map (Ideal.Quotient.mk I) := by
  simp only [mk_ker, sup_idem, sup_comm, quotLeftToQuotSup, Quotient.factor, ker_quotient_lift,
    map_eq_iff_sup_ker_eq_of_surjective (Ideal.Quotient.mk I) Quotient.mk_surjective, ← sup_assoc]
#align double_quot.ker_quot_left_to_quot_sup DoubleQuot.ker_quotLeftToQuotSup

/-- The ring homomorphism `(R/I)/J' -> R/(I ⊔ J)` induced by `quotLeftToQuotSup` where `J'`
  is the image of `J` in `R/I`-/
def quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.lift (J.map (Ideal.Quotient.mk I)) (quotLeftToQuotSup I J)
    (ker_quotLeftToQuotSup I J).symm.le
#align double_quot.quot_quot_to_quot_sup DoubleQuot.quotQuotToQuotSup

/-- The composite of the maps `R → (R/I)` and `(R/I) → (R/I)/J'` -/
def quotQuotMk : R →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I))).comp (Ideal.Quotient.mk I)
#align double_quot.quot_quot_mk DoubleQuot.quotQuotMk

-- Porting note: mismatched instances
/-- The kernel of `quotQuotMk` -/
theorem ker_quotQuotMk : RingHom.ker (quotQuotMk I J) = I ⊔ J := by
  rw [RingHom.ker_eq_comap_bot, quotQuotMk, ← comap_comap, ← RingHom.ker, mk_ker,
    comap_map_of_surjective (Ideal.Quotient.mk I) Quotient.mk_surjective, ← RingHom.ker, mk_ker,
    sup_comm]
#align double_quot.ker_quot_quot_mk DoubleQuot.ker_quotQuotMk

/-- The ring homomorphism `R/(I ⊔ J) → (R/I)/J' `induced by `quotQuotMk` -/
def liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I ⊔ J →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  Ideal.Quotient.lift (I ⊔ J) (quotQuotMk I J) (ker_quotQuotMk I J).symm.le
#align double_quot.lift_sup_quot_quot_mk DoubleQuot.liftSupQuotQuotMk

/-- `quotQuotToQuotSup` and `liftSupQuotQuotMk` are inverse isomorphisms. In the case where
    `I ≤ J`, this is the Third Isomorphism Theorem (see `quotQuotEquivQuotOfLe`)-/
def quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J :=
  RingEquiv.ofHomInv (quotQuotToQuotSup I J) (liftSupQuotQuotMk I J)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      -- ⊢ RingHom.comp (RingHom.comp (RingHom.comp ↑(liftSupQuotQuotMk I J) ↑(quotQuot …
      rfl)
      -- 🎉 no goals
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      -- ⊢ RingHom.comp (RingHom.comp ↑(quotQuotToQuotSup I J) ↑(liftSupQuotQuotMk I J) …
      rfl)
      -- 🎉 no goals
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
def quotQuotEquivComm : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+*
    (R ⧸ J) ⧸ I.map (Ideal.Quotient.mk J) :=
  ((quotQuotEquivQuotSup I J).trans (quotEquivOfEq (sup_comm))).trans
    (quotQuotEquivQuotSup J I).symm
#align double_quot.quot_quot_equiv_comm DoubleQuot.quotQuotEquivComm

-- Porting note: mismatched instances
@[simp]
theorem quotQuotEquivComm_quotQuotMk (x : R) :
    quotQuotEquivComm I J (quotQuotMk I J x) = quotQuotMk J I x :=
  rfl
#align double_quot.quot_quot_equiv_comm_quot_quot_mk DoubleQuot.quotQuotEquivComm_quotQuotMk

-- Porting note: mismatched instances
@[simp]
theorem quotQuotEquivComm_comp_quotQuotMk :
    RingHom.comp (↑(quotQuotEquivComm I J)) (quotQuotMk I J) = quotQuotMk J I :=
  RingHom.ext <| quotQuotEquivComm_quotQuotMk I J
#align double_quot.quot_quot_equiv_comm_comp_quot_quot_mk DoubleQuot.quotQuotEquivComm_comp_quotQuotMk

@[simp]
theorem quotQuotEquivComm_symm : (quotQuotEquivComm I J).symm = quotQuotEquivComm J I := by
  /-  Porting note: this proof used to just be rfl but currently rfl opens up a bottomless pit
  of processor cycles. Synthesizing instances does not seem to be an issue.
  -/
  change (((quotQuotEquivQuotSup I J).trans (quotEquivOfEq (sup_comm))).trans
    (quotQuotEquivQuotSup J I).symm).symm =
      ((quotQuotEquivQuotSup J I).trans (quotEquivOfEq (sup_comm))).trans
        (quotQuotEquivQuotSup I J).symm
  ext r
  -- ⊢ ↑(RingEquiv.symm (RingEquiv.trans (RingEquiv.trans (quotQuotEquivQuotSup I J …
  dsimp
  -- ⊢ ↑(RingEquiv.symm (quotQuotEquivQuotSup I J)) (↑(RingEquiv.symm (quotEquivOfE …
  rfl
  -- 🎉 no goals
#align double_quot.quot_quot_equiv_comm_symm DoubleQuot.quotQuotEquivComm_symm

variable {I J}

/-- **The Third Isomorphism theorem** for rings. See `quotQuotEquivQuotSup` for a version
    that does not assume an inclusion of ideals. -/
def quotQuotEquivQuotOfLE (h : I ≤ J) : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ J :=
  (quotQuotEquivQuotSup I J).trans (Ideal.quotEquivOfEq <| sup_eq_right.mpr h)
#align double_quot.quot_quot_equiv_quot_of_le DoubleQuot.quotQuotEquivQuotOfLE

@[simp]
theorem quotQuotEquivQuotOfLE_quotQuotMk (x : R) (h : I ≤ J) :
    quotQuotEquivQuotOfLE h (quotQuotMk I J x) = (Ideal.Quotient.mk J) x :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_quot_quot_mk DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk

@[simp]
theorem quotQuotEquivQuotOfLE_symm_mk (x : R) (h : I ≤ J) :
    (quotQuotEquivQuotOfLE h).symm ((Ideal.Quotient.mk J) x) = quotQuotMk I J x :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_symm_mk DoubleQuot.quotQuotEquivQuotOfLE_symm_mk

theorem quotQuotEquivQuotOfLE_comp_quotQuotMk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h)) (quotQuotMk I J) = (Ideal.Quotient.mk J) := by
  ext
  -- ⊢ ↑(RingHom.comp (↑(quotQuotEquivQuotOfLE h)) (quotQuotMk I J)) x✝ = ↑(Ideal.Q …
  rfl
  -- 🎉 no goals
#align double_quot.quot_quot_equiv_quot_of_le_comp_quot_quot_mk DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMk

theorem quotQuotEquivQuotOfLE_symm_comp_mk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h).symm) (Ideal.Quotient.mk J) = quotQuotMk I J := by
  ext
  -- ⊢ ↑(RingHom.comp (↑(RingEquiv.symm (quotQuotEquivQuotOfLE h))) (Ideal.Quotient …
  rfl
  -- 🎉 no goals
#align double_quot.quot_quot_equiv_quot_of_le_symm_comp_mk DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mk

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

section AlgebraQuotient

variable (R) {A : Type*} [CommSemiring R] [CommRing A] [Algebra R A] (I J : Ideal A)

/-- The natural algebra homomorphism `A / I → A / (I ⊔ J)`. -/
def quotLeftToQuotSupₐ : A ⧸ I →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotLeftToQuotSup I J) fun _ => rfl
#align double_quot.quot_left_to_quot_supₐ DoubleQuot.quotLeftToQuotSupₐ

@[simp]
theorem quotLeftToQuotSupₐ_toRingHom :
    (quotLeftToQuotSupₐ R I J : _ →+* _) = quotLeftToQuotSup I J :=
  rfl
#align double_quot.quot_left_to_quot_supₐ_to_ring_hom DoubleQuot.quotLeftToQuotSupₐ_toRingHom

@[simp]
theorem coe_quotLeftToQuotSupₐ : ⇑(quotLeftToQuotSupₐ R I J) = quotLeftToQuotSup I J :=
  rfl
#align double_quot.coe_quot_left_to_quot_supₐ DoubleQuot.coe_quotLeftToQuotSupₐ

/-- The algebra homomorphism `(A / I) / J' -> A / (I ⊔ J)` induced by `quotQuotToQuotSup`,
  where `J'` is the projection of `J` in `A / I`. -/
def quotQuotToQuotSupₐ : (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotQuotToQuotSup I J) fun _ => rfl
#align double_quot.quot_quot_to_quot_supₐ DoubleQuot.quotQuotToQuotSupₐ

@[simp]
theorem quotQuotToQuotSupₐ_toRingHom :
    ((quotQuotToQuotSupₐ R I J) : _ ⧸ map (Ideal.Quotient.mkₐ R I) J →+* _) =
      quotQuotToQuotSup I J :=
  rfl
#align double_quot.quot_quot_to_quot_supₐ_to_ring_hom DoubleQuot.quotQuotToQuotSupₐ_toRingHom

@[simp]
theorem coe_quotQuotToQuotSupₐ : ⇑(quotQuotToQuotSupₐ R I J) = quotQuotToQuotSup I J :=
  rfl
#align double_quot.coe_quot_quot_to_quot_supₐ DoubleQuot.coe_quotQuotToQuotSupₐ

/-- The composition of the algebra homomorphisms `A → (A / I)` and `(A / I) → (A / I) / J'`,
  where `J'` is the projection `J` in `A / I`. -/
def quotQuotMkₐ : A →ₐ[R] (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) :=
  AlgHom.mk (quotQuotMk I J) fun _ => rfl
#align double_quot.quot_quot_mkₐ DoubleQuot.quotQuotMkₐ

@[simp]
theorem quotQuotMkₐ_toRingHom :
    (quotQuotMkₐ R I J : _ →+* _ ⧸ J.map (Quotient.mkₐ R I)) = quotQuotMk I J :=
  rfl
#align double_quot.quot_quot_mkₐ_to_ring_hom DoubleQuot.quotQuotMkₐ_toRingHom

@[simp]
theorem coe_quotQuotMkₐ : ⇑(quotQuotMkₐ R I J) = quotQuotMk I J :=
  rfl
#align double_quot.coe_quot_quot_mkₐ DoubleQuot.coe_quotQuotMkₐ

/-- The injective algebra homomorphism `A / (I ⊔ J) → (A / I) / J'`induced by `quot_quot_mk`,
  where `J'` is the projection `J` in `A / I`. -/
def liftSupQuotQuotMkₐ (I J : Ideal A) : A ⧸ I ⊔ J →ₐ[R] (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) :=
  AlgHom.mk (liftSupQuotQuotMk I J) fun _ => rfl
#align double_quot.lift_sup_quot_quot_mkₐ DoubleQuot.liftSupQuotQuotMkₐ

@[simp]
theorem liftSupQuotQuotMkₐ_toRingHom :
    (liftSupQuotQuotMkₐ R I J : _ →+* _ ⧸ J.map (Quotient.mkₐ R I)) = liftSupQuotQuotMk I J :=
  rfl
#align double_quot.lift_sup_quot_quot_mkₐ_to_ring_hom DoubleQuot.liftSupQuotQuotMkₐ_toRingHom

@[simp]
theorem coe_liftSupQuotQuotMkₐ : ⇑(liftSupQuotQuotMkₐ R I J) = liftSupQuotQuotMk I J :=
  rfl
#align double_quot.coe_lift_sup_quot_quot_mkₐ DoubleQuot.coe_liftSupQuotQuotMkₐ

/-- `quotQuotToQuotSup` and `liftSupQuotQuotMk` are inverse isomorphisms. In the case where
`I ≤ J`, this is the Third Isomorphism Theorem (see `DoubleQuot.quotQuotEquivQuotOfLE`). -/
def quotQuotEquivQuotSupₐ : ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] A ⧸ I ⊔ J :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivQuotSup I J) fun _ => rfl
#align double_quot.quot_quot_equiv_quot_supₐ DoubleQuot.quotQuotEquivQuotSupₐ

@[simp]
theorem quotQuotEquivQuotSupₐ_toRingEquiv :
    (quotQuotEquivQuotSupₐ R I J : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _) = quotQuotEquivQuotSup I J :=
  rfl
#align double_quot.quot_quot_equiv_quot_supₐ_to_ring_equiv DoubleQuot.quotQuotEquivQuotSupₐ_toRingEquiv

@[simp]
-- Porting note: had to add an extra coercion arrow on the right hand side.
theorem coe_quotQuotEquivQuotSupₐ : ⇑(quotQuotEquivQuotSupₐ R I J) = ⇑(quotQuotEquivQuotSup I J) :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_supₐ DoubleQuot.coe_quotQuotEquivQuotSupₐ

@[simp]
theorem quotQuotEquivQuotSupₐ_symm_toRingEquiv :
    ((quotQuotEquivQuotSupₐ R I J).symm : _ ≃+* _ ⧸ J.map (Quotient.mkₐ R I)) =
      (quotQuotEquivQuotSup I J).symm :=
  rfl
#align double_quot.quot_quot_equiv_quot_supₐ_symm_to_ring_equiv DoubleQuot.quotQuotEquivQuotSupₐ_symm_toRingEquiv

@[simp]
-- Porting note: had to add an extra coercion arrow on the right hand side.
theorem coe_quotQuotEquivQuotSupₐ_symm :
    ⇑(quotQuotEquivQuotSupₐ R I J).symm = ⇑(quotQuotEquivQuotSup I J).symm :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_supₐ_symm DoubleQuot.coe_quotQuotEquivQuotSupₐ_symm

/-- The natural algebra isomorphism `(A / I) / J' → (A / J) / I'`,
  where `J'` (resp. `I'`) is the projection of `J` in `A / I` (resp. `I` in `A / J`). -/
def quotQuotEquivCommₐ :
    ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] (A ⧸ J) ⧸ I.map (Quotient.mkₐ R J) :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivComm I J) fun _ => rfl
#align double_quot.quot_quot_equiv_commₐ DoubleQuot.quotQuotEquivCommₐ

@[simp]
theorem quotQuotEquivCommₐ_toRingEquiv :
    (quotQuotEquivCommₐ R I J : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _ ⧸ I.map (Quotient.mkₐ R J)) =
      quotQuotEquivComm I J :=
  -- Porting note: should just be `rfl` but `AlgEquiv.toRingEquiv` and `AlgEquiv.ofRingEquiv`
  -- involve repacking everything in the structure, so Lean ends up unfolding `quotQuotEquivComm`
  -- and timing out.
  RingEquiv.ext fun _ => rfl
#align double_quot.quot_quot_equiv_commₐ_to_ring_equiv DoubleQuot.quotQuotEquivCommₐ_toRingEquiv

@[simp]
theorem coe_quotQuotEquivCommₐ : ⇑(quotQuotEquivCommₐ R I J) = ⇑(quotQuotEquivComm I J) :=
  rfl
#align double_quot.coe_quot_quot_equiv_commₐ DoubleQuot.coe_quotQuotEquivCommₐ

@[simp]
theorem quotQuotEquivComm_symmₐ : (quotQuotEquivCommₐ R I J).symm = quotQuotEquivCommₐ R J I := by
  -- Porting note: should just be `rfl` but `AlgEquiv.toRingEquiv` and `AlgEquiv.ofRingEquiv`
  -- involve repacking everything in the structure, so Lean ends up unfolding `quotQuotEquivComm`
  -- and timing out.
  ext
  -- ⊢ ↑(AlgEquiv.symm (quotQuotEquivCommₐ R I J)) a✝ = ↑(quotQuotEquivCommₐ R J I) …
  unfold quotQuotEquivCommₐ
  -- ⊢ ↑(AlgEquiv.symm (AlgEquiv.ofRingEquiv (_ : ∀ (x : R), ↑(quotQuotEquivComm I  …
  congr
  -- 🎉 no goals
#align double_quot.quot_quot_equiv_comm_symmₐ DoubleQuot.quotQuotEquivComm_symmₐ

@[simp]
theorem quotQuotEquivComm_comp_quotQuotMkₐ :
    AlgHom.comp (↑(quotQuotEquivCommₐ R I J)) (quotQuotMkₐ R I J) = quotQuotMkₐ R J I :=
  AlgHom.ext <| quotQuotEquivComm_quotQuotMk I J
#align double_quot.quot_quot_equiv_comm_comp_quot_quot_mkₐ DoubleQuot.quotQuotEquivComm_comp_quotQuotMkₐ

variable {I J}

/-- The **third isomorphism theorem** for algebras. See `quotQuotEquivQuotSupₐ` for version
    that does not assume an inclusion of ideals. -/
def quotQuotEquivQuotOfLEₐ (h : I ≤ J) : ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] A ⧸ J :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivQuotOfLE h) fun _ => rfl
#align double_quot.quot_quot_equiv_quot_of_leₐ DoubleQuot.quotQuotEquivQuotOfLEₐ

@[simp]
theorem quotQuotEquivQuotOfLEₐ_toRingEquiv (h : I ≤ J) :
    (quotQuotEquivQuotOfLEₐ R h : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _) = quotQuotEquivQuotOfLE h :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_leₐ_to_ring_equiv DoubleQuot.quotQuotEquivQuotOfLEₐ_toRingEquiv

@[simp]
-- Porting note: had to add an extra coercion arrow on the right hand side.
theorem coe_quotQuotEquivQuotOfLEₐ (h : I ≤ J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h) = ⇑(quotQuotEquivQuotOfLE h) :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_of_leₐ DoubleQuot.coe_quotQuotEquivQuotOfLEₐ

@[simp]
theorem quotQuotEquivQuotOfLEₐ_symm_toRingEquiv (h : I ≤ J) :
    ((quotQuotEquivQuotOfLEₐ R h).symm : _ ≃+* _ ⧸ J.map (Quotient.mkₐ R I)) =
      (quotQuotEquivQuotOfLE h).symm :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_leₐ_symm_to_ring_equiv DoubleQuot.quotQuotEquivQuotOfLEₐ_symm_toRingEquiv

@[simp]
-- Porting note: had to add an extra coercion arrow on the right hand side.
theorem coe_quotQuotEquivQuotOfLEₐ_symm (h : I ≤ J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h).symm = ⇑(quotQuotEquivQuotOfLE h).symm :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_of_leₐ_symm DoubleQuot.coe_quotQuotEquivQuotOfLEₐ_symm

@[simp]
theorem quotQuotEquivQuotOfLE_comp_quotQuotMkₐ (h : I ≤ J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h)) (quotQuotMkₐ R I J) = Quotient.mkₐ R J :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_comp_quot_quot_mkₐ DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMkₐ

@[simp]
theorem quotQuotEquivQuotOfLE_symm_comp_mkₐ (h : I ≤ J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h).symm) (Quotient.mkₐ R J) = quotQuotMkₐ R I J :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_symm_comp_mkₐ DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mkₐ

end AlgebraQuotient
end DoubleQuot
