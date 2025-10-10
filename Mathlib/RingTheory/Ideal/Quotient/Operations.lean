/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Patrick Massot
-/
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Ring.Fin
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# More operations on modules and ideals related to quotients

## Main results:

- `RingHom.quotientKerEquivRange` : the **first isomorphism theorem** for commutative rings.
- `RingHom.quotientKerEquivRangeS` : the **first isomorphism theorem**
  for a morphism from a commutative ring to a semiring.
- `AlgHom.quotientKerEquivRange` : the **first isomorphism theorem**
  for a morphism of algebras (over a commutative semiring)
- `RingHom.quotientKerEquivRangeS` : the **first isomorphism theorem**
  for a morphism from a commutative ring to a semiring.
- `Ideal.quotientInfRingEquivPiQuotient`: the **Chinese Remainder Theorem**, version for coprime
  ideals (see also `ZMod.prodEquivPi` in `Data.ZMod.Quotient` for elementary versions about
  `ZMod`).
-/

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [Ring R] [Semiring S] (f : R →+* S)

/-- The induced map from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotientKerEquivOfRightInverse`) /
is surjective (`quotientKerEquivOfSurjective`).
-/
def kerLift : R ⧸ ker f →+* S :=
  Ideal.Quotient.lift _ f fun _ => mem_ker.mp

@[simp]
theorem kerLift_mk (r : R) : kerLift f (Ideal.Quotient.mk (ker f) r) = f r :=
  Ideal.Quotient.lift_mk _ _ _

theorem lift_injective_of_ker_le_ideal (I : Ideal R) [I.IsTwoSided]
    {f : R →+* S} (H : ∀ a : R, a ∈ I → f a = 0)
    (hI : ker f ≤ I) : Function.Injective (Ideal.Quotient.lift I f H) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro u hu
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [Ideal.Quotient.lift_mk] at hu
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI (RingHom.mem_ker.mpr hu)

/-- The induced map from the quotient by the kernel is injective. -/
theorem kerLift_injective : Function.Injective (kerLift f) :=
  lift_injective_of_ker_le_ideal (ker f) (fun a => by simp only [mem_ker, imp_self]) le_rfl


variable {f}

/-- The **first isomorphism theorem for commutative rings**, computable version. -/
def quotientKerEquivOfRightInverse {g : S → R} (hf : Function.RightInverse g f) :
    R ⧸ ker f ≃+* S :=
  { kerLift f with
    toFun := kerLift f
    invFun := Ideal.Quotient.mk (ker f) ∘ g
    left_inv := by
      rintro ⟨x⟩
      apply kerLift_injective
      simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, kerLift_mk,
        Function.comp_apply, hf (f x)]
    right_inv := hf }

@[simp]
theorem quotientKerEquivOfRightInverse.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : R ⧸ ker f) : quotientKerEquivOfRightInverse hf x = kerLift f x :=
  rfl

@[simp]
theorem quotientKerEquivOfRightInverse.Symm.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : S) : (quotientKerEquivOfRightInverse hf).symm x = Ideal.Quotient.mk (ker f) (g x) :=
  rfl

/-- The **first isomorphism theorem** for commutative rings, surjective case. -/
noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ (ker f) ≃+* S :=
  quotientKerEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)

@[simp]
lemma quotientKerEquivOfSurjective_apply_mk {f : R →+* S} (hf : Function.Surjective f) (x : R) :
    f.quotientKerEquivOfSurjective hf (Ideal.Quotient.mk _ x) = f x :=
  rfl

/-- The **first isomorphism theorem** for commutative rings (`RingHom.rangeS` version). -/
noncomputable def quotientKerEquivRangeS (f : R →+* S) : R ⧸ ker f ≃+* f.rangeS :=
  (Ideal.quotEquivOfEq f.ker_rangeSRestrict.symm).trans <|
  quotientKerEquivOfSurjective f.rangeSRestrict_surjective

variable {S : Type v} [Ring S] (f : R →+* S)

/-- The **first isomorphism theorem** for commutative rings (`RingHom.range` version). -/
noncomputable def quotientKerEquivRange (f : R →+* S) : R ⧸ ker f ≃+* f.range :=
  (Ideal.quotEquivOfEq f.ker_rangeRestrict.symm).trans <|
    quotientKerEquivOfSurjective f.rangeRestrict_surjective

end RingHom

namespace Ideal
open Function RingHom

variable {R : Type u} {S : Type v} {F : Type w} [Ring R] [Semiring S]

@[simp]
theorem map_quotient_self (I : Ideal R) [I.IsTwoSided] : map (Quotient.mk I) I = ⊥ :=
  eq_bot_iff.2 <|
    Ideal.map_le_iff_le_comap.2 fun _ hx =>
      (Submodule.mem_bot (R ⧸ I)).2 <| Ideal.Quotient.eq_zero_iff_mem.2 hx

@[simp]
theorem mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) = I := by
  ext
  rw [ker, mem_comap, Submodule.mem_bot, Quotient.eq_zero_iff_mem]

theorem map_mk_eq_bot_of_le {I J : Ideal R} [J.IsTwoSided] (h : I ≤ J) :
    I.map (Quotient.mk J) = ⊥ := by
  rw [map_eq_bot_iff_le_ker, mk_ker]
  exact h

theorem ker_quotient_lift {I : Ideal R} [I.IsTwoSided] (f : R →+* S)
    (H : I ≤ ker f) :
    ker (Ideal.Quotient.lift I f H) = (RingHom.ker f).map (Quotient.mk I) := by
  apply Ideal.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Quotient.mk_surjective x
    rw [mem_ker, ← hy, Ideal.Quotient.lift_mk, ← mem_ker] at hx
    rw [← hy, mem_map_iff_of_surjective (Quotient.mk I) Quotient.mk_surjective]
    exact ⟨y, hx, rfl⟩
  · intro hx
    rw [mem_map_iff_of_surjective (Quotient.mk I) Quotient.mk_surjective] at hx
    obtain ⟨y, hy⟩ := hx
    rw [mem_ker, ← hy.right, Ideal.Quotient.lift_mk]
    exact hy.left

lemma injective_lift_iff {I : Ideal R} [I.IsTwoSided]
    {f : R →+* S} (H : ∀ (a : R), a ∈ I → f a = 0) :
    Injective (Quotient.lift I f H) ↔ ker f = I := by
  rw [injective_iff_ker_eq_bot, ker_quotient_lift, map_eq_bot_iff_le_ker, mk_ker]
  constructor
  · exact fun h ↦ le_antisymm h H
  · rintro rfl; rfl

lemma ker_Pi_Quotient_mk {ι : Type*} (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] :
    ker (Pi.ringHom fun i : ι ↦ Quotient.mk (I i)) = ⨅ i, I i := by
  simp [Pi.ker_ringHom, mk_ker]

@[simp]
theorem bot_quotient_isMaximal_iff (I : Ideal R) [I.IsTwoSided] :
    (⊥ : Ideal (R ⧸ I)).IsMaximal ↔ I.IsMaximal :=
  ⟨fun hI =>
    mk_ker (I := I) ▸
      comap_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective (K := ⊥) (H := hI),
    fun hI => by
    letI := Quotient.divisionRing I
    exact bot_isMaximal⟩

/-- See also `Ideal.mem_quotient_iff_mem` in case `I ≤ J`. -/
@[simp]
theorem mem_quotient_iff_mem_sup {I J : Ideal R} [I.IsTwoSided] {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J ⊔ I := by
  rw [← mem_comap, comap_map_of_surjective (Quotient.mk I) Quotient.mk_surjective, ←
    ker_eq_comap_bot, mk_ker]

/-- See also `Ideal.mem_quotient_iff_mem_sup` if the assumption `I ≤ J` is not available. -/
theorem mem_quotient_iff_mem {I J : Ideal R} [I.IsTwoSided] (hIJ : I ≤ J) {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J := by
  rw [mem_quotient_iff_mem_sup, sup_eq_left.mpr hIJ]

section ChineseRemainder
open Function Quotient Finset

variable {ι : Type*}

/-- The homomorphism from `R/(⋂ i, f i)` to `∏ i, (R / f i)` featured in the Chinese
  Remainder Theorem. It is bijective if the ideals `f i` are coprime. -/
def quotientInfToPiQuotient (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] :
    (R ⧸ ⨅ i, I i) →+* ∀ i, R ⧸ I i :=
  Quotient.lift (⨅ i, I i) (Pi.ringHom fun i : ι ↦ Quotient.mk (I i))
    (by simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])

lemma quotientInfToPiQuotient_mk (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] (x : R) :
    quotientInfToPiQuotient I (Quotient.mk _ x) = fun i : ι ↦ Quotient.mk (I i) x :=
  rfl

lemma quotientInfToPiQuotient_mk' (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] (x : R) (i : ι) :
    quotientInfToPiQuotient I (Quotient.mk _ x) i = Quotient.mk (I i) x :=
  rfl

lemma quotientInfToPiQuotient_inj (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] :
    Injective (quotientInfToPiQuotient I) := by
  rw [quotientInfToPiQuotient, injective_lift_iff, ker_Pi_Quotient_mk]

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]

lemma quotientInfToPiQuotient_surj {I : ι → Ideal R}
    (hI : Pairwise (IsCoprime on I)) : Surjective (quotientInfToPiQuotient I) := by
  classical
  cases nonempty_fintype ι
  intro g
  choose f hf using fun i ↦ mk_surjective (g i)
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
      intro j hj
      exact hI (by simpa [ne_comm, isCoprime_iff_add] using hj)
    rcases isCoprime_iff_exists.mp (isCoprime_biInf hI') with ⟨u, hu, e, he, hue⟩
    replace he : ∀ j, j ≠ i → e ∈ I j := by simpa using he
    refine ⟨e, ?_, ?_⟩
    · simp [eq_sub_of_add_eq' hue, map_sub, eq_zero_iff_mem.mpr hu]
    · exact fun j hj ↦ eq_zero_iff_mem.mpr (he j hj)
  choose e he using key
  use mk _ (∑ i, f i*e i)
  ext i
  rw [quotientInfToPiQuotient_mk', map_sum, Fintype.sum_eq_single i]
  · simp [(he i).1, hf]
  · intro j hj
    simp [(he j).2 i hj.symm]

/-- **Chinese Remainder Theorem**. Eisenbud Ex.2.6.
Similar to Atiyah-Macdonald 1.10 and Stacks 00DT -/
noncomputable def quotientInfRingEquivPiQuotient (f : ι → Ideal R)
    (hf : Pairwise (IsCoprime on f)) : (R ⧸ ⨅ i, f i) ≃+* ∀ i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨quotientInfToPiQuotient_inj f, quotientInfToPiQuotient_surj hf⟩,
    quotientInfToPiQuotient f with }

/-- Corollary of Chinese Remainder Theorem: if `Iᵢ` are pairwise coprime ideals in a
commutative ring then the canonical map `R → ∏ (R ⧸ Iᵢ)` is surjective. -/
lemma pi_quotient_surjective {I : ι → Ideal R}
    (hf : Pairwise fun i j ↦ IsCoprime (I i) (I j)) (x : (i : ι) → R ⧸ I i) :
    ∃ r : R, ∀ i, r = x i := by
  obtain ⟨y, rfl⟩ := Ideal.quotientInfToPiQuotient_surj hf x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨r, fun i ↦ rfl⟩

-- variant of `IsDedekindDomain.exists_forall_sub_mem_ideal` which doesn't assume Dedekind domain!
/-- Corollary of Chinese Remainder Theorem: if `Iᵢ` are pairwise coprime ideals in a
commutative ring then given elements `xᵢ` you can find `r` with `r - xᵢ ∈ Iᵢ` for all `i`. -/
lemma exists_forall_sub_mem_ideal
    {I : ι → Ideal R} (hI : Pairwise fun i j ↦ IsCoprime (I i) (I j)) (x : ι → R) :
    ∃ r : R, ∀ i, r - x i ∈ I i := by
  obtain ⟨y, hy⟩ := Ideal.pi_quotient_surjective hI (fun i ↦ x i)
  exact ⟨y, fun i ↦ (Submodule.Quotient.eq (I i)).mp <| hy i⟩

/-- **Chinese remainder theorem**, specialized to two ideals. -/
noncomputable def quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    R ⧸ I ⊓ J ≃+* (R ⧸ I) × R ⧸ J :=
  let f : Fin 2 → Ideal R := ![I, J]
  have hf : Pairwise (IsCoprime on f) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> try contradiction
    · assumption
    · exact coprime.symm
  (Ideal.quotEquivOfEq (by simp [f, iInf, inf_comm])).trans <|
            (Ideal.quotientInfRingEquivPiQuotient f hf).trans <| RingEquiv.piFinTwo fun i => R ⧸ f i

@[simp]
theorem quotientInfEquivQuotientProd_fst (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J) :
    (quotientInfEquivQuotientProd I J coprime x).fst =
      Ideal.Quotient.factor inf_le_left x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
theorem quotientInfEquivQuotientProd_snd (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J) :
    (quotientInfEquivQuotientProd I J coprime x).snd =
      Ideal.Quotient.factor inf_le_right x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
theorem fst_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.fst _ _).comp
        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor inf_le_left := by
  apply Quotient.ringHom_ext; ext; rfl

@[simp]
theorem snd_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.snd _ _).comp
        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor inf_le_right := by
  apply Quotient.ringHom_ext; ext; rfl

/-- **Chinese remainder theorem**, specialized to two ideals. -/
noncomputable def quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    R ⧸ I * J ≃+* (R ⧸ I) × R ⧸ J :=
  Ideal.quotEquivOfEq (inf_eq_mul_of_isCoprime coprime).symm |>.trans <|
    Ideal.quotientInfEquivQuotientProd I J coprime

@[simp]
theorem quotientMulEquivQuotientProd_fst (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I * J) :
    (quotientMulEquivQuotientProd I J coprime x).fst =
      Ideal.Quotient.factor mul_le_right x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
theorem quotientMulEquivQuotientProd_snd (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I * J) :
    (quotientMulEquivQuotientProd I J coprime x).snd =
      Ideal.Quotient.factor mul_le_left x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
theorem fst_comp_quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.fst _ _).comp
        (quotientMulEquivQuotientProd I J coprime : R ⧸ I * J →+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor mul_le_right := by
  apply Quotient.ringHom_ext; ext; rfl

@[simp]
theorem snd_comp_quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.snd _ _).comp
        (quotientMulEquivQuotientProd I J coprime : R ⧸ I * J →+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor mul_le_left := by
  apply Quotient.ringHom_ext; ext; rfl

end ChineseRemainder

section QuotientAlgebra

variable (R₁ R₂ : Type*) {A B : Type*}
variable [CommSemiring R₁] [CommSemiring R₂] [Ring A]
variable [Algebra R₁ A] [Algebra R₂ A]

/-- The `R₁`-algebra structure on `A/I` for an `R₁`-algebra `A` -/
instance Quotient.algebra {I : Ideal A} [I.IsTwoSided] : Algebra R₁ (A ⧸ I) where
  algebraMap := (Ideal.Quotient.mk I).comp (algebraMap R₁ A)
  smul_def' := fun _ x =>
    Quotient.inductionOn' x fun _ =>
      ((Quotient.mk I).congr_arg <| Algebra.smul_def _ _).trans (RingHom.map_mul _ _ _)
  commutes' := by rintro r ⟨x⟩; exact congr_arg (⟦·⟧) (Algebra.commutes r x)

instance {A} [CommRing A] [Algebra R₁ A] (I : Ideal A) : Algebra R₁ (A ⧸ I) := inferInstance

-- This instance can be inferred, but is kept around as a useful shortcut.
instance Quotient.isScalarTower [SMul R₁ R₂] [IsScalarTower R₁ R₂ A] (I : Ideal A) :
    IsScalarTower R₁ R₂ (A ⧸ I) := inferInstance

/-- The canonical morphism `A →ₐ[R₁] A ⧸ I` as morphism of `R₁`-algebras, for `I` an ideal of
`A`, where `A` is an `R₁`-algebra. -/
def Quotient.mkₐ (I : Ideal A) [I.IsTwoSided] : A →ₐ[R₁] A ⧸ I :=
  ⟨⟨⟨⟨fun a => Submodule.Quotient.mk a, rfl⟩, fun _ _ => rfl⟩, rfl, fun _ _ => rfl⟩, fun _ => rfl⟩

theorem Quotient.algHom_ext {I : Ideal A} [I.IsTwoSided]
    {S} [Semiring S] [Algebra R₁ S] ⦃f g : A ⧸ I →ₐ[R₁] S⦄
    (h : f.comp (Quotient.mkₐ R₁ I) = g.comp (Quotient.mkₐ R₁ I)) : f = g :=
  AlgHom.ext fun x => Quotient.inductionOn' x <| AlgHom.congr_fun h

theorem Quotient.alg_map_eq {A} [CommRing A] [Algebra R₁ A] (I : Ideal A) :
    algebraMap R₁ (A ⧸ I) = (algebraMap A (A ⧸ I)).comp (algebraMap R₁ A) :=
  rfl

theorem Quotient.mkₐ_toRingHom (I : Ideal A) [I.IsTwoSided] :
    (Quotient.mkₐ R₁ I).toRingHom = Ideal.Quotient.mk I :=
  rfl

@[simp]
theorem Quotient.mkₐ_eq_mk (I : Ideal A) [I.IsTwoSided] : ⇑(Quotient.mkₐ R₁ I) = Quotient.mk I :=
  rfl

@[simp]
theorem Quotient.algebraMap_eq {R} [CommRing R] (I : Ideal R) :
    algebraMap R (R ⧸ I) = Quotient.mk I :=
  rfl

@[simp]
theorem Quotient.mk_comp_algebraMap (I : Ideal A) [I.IsTwoSided] :
    (Quotient.mk I).comp (algebraMap R₁ A) = algebraMap R₁ (A ⧸ I) :=
  rfl

@[simp]
theorem Quotient.mk_algebraMap (I : Ideal A) [I.IsTwoSided] (x : R₁) :
    Quotient.mk I (algebraMap R₁ A x) = algebraMap R₁ (A ⧸ I) x :=
  rfl

/-- The canonical morphism `A →ₐ[R₁] I.quotient` is surjective. -/
theorem Quotient.mkₐ_surjective (I : Ideal A) [I.IsTwoSided] :
    Function.Surjective (Quotient.mkₐ R₁ I) :=
  Quot.mk_surjective

/-- The kernel of `A →ₐ[R₁] I.quotient` is `I`. -/
@[simp]
theorem Quotient.mkₐ_ker (I : Ideal A) [I.IsTwoSided] :
    RingHom.ker (Quotient.mkₐ R₁ I : A →+* A ⧸ I) = I :=
  Ideal.mk_ker

lemma Quotient.mk_bijective_iff_eq_bot (I : Ideal A) [I.IsTwoSided] :
    Function.Bijective (mk I) ↔ I = ⊥ := by
  constructor
  · intro h
    rw [← map_eq_bot_iff_of_injective h.1]
    exact (map_eq_bot_iff_le_ker _).mpr <| le_of_eq mk_ker.symm
  · exact fun h => ⟨(injective_iff_ker_eq_bot _).mpr <| by rw [mk_ker, h], mk_surjective⟩

section

/-- `AlgHom` version of `Ideal.Quotient.factor`. -/
def Quotient.factorₐ {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (hIJ : I ≤ J) :
    A ⧸ I →ₐ[R₁] A ⧸ J where
  __ := Ideal.Quotient.factor hIJ
  commutes' _ := rfl

variable {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (hIJ : I ≤ J)

@[simp]
lemma Quotient.coe_factorₐ :
    (Ideal.Quotient.factorₐ R₁ hIJ : A ⧸ I →+* A ⧸ J) = Ideal.Quotient.factor hIJ := rfl

@[simp]
lemma Quotient.factorₐ_apply_mk (x : A) :
    Ideal.Quotient.factorₐ R₁ hIJ x = x := rfl

@[simp]
lemma Quotient.factorₐ_comp_mk :
    (Ideal.Quotient.factorₐ R₁ hIJ).comp (Ideal.Quotient.mkₐ R₁ I) = Ideal.Quotient.mkₐ R₁ J := rfl

@[simp]
lemma Quotient.factorₐ_comp {K : Ideal A} [K.IsTwoSided] (hJK : J ≤ K) :
    (Ideal.Quotient.factorₐ R₁ hJK).comp (Ideal.Quotient.factorₐ R₁ hIJ) =
      Ideal.Quotient.factorₐ R₁ (hIJ.trans hJK) :=
  Ideal.Quotient.algHom_ext _ (by ext; simp)

end

variable {R₁}

section

variable [Semiring B] [Algebra R₁ B]

/-- `Ideal.quotient.lift` as an `AlgHom`. -/
def Quotient.liftₐ (I : Ideal A) [I.IsTwoSided] (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    A ⧸ I →ₐ[R₁] B :=
  {-- this is IsScalarTower.algebraMap_apply R₁ A (A ⧸ I) but the file `Algebra.Algebra.Tower`
      -- imports this file.
      Ideal.Quotient.lift
      I (f : A →+* B) hI with
    commutes' := fun r => by
      have : algebraMap R₁ (A ⧸ I) r = Ideal.Quotient.mk I (algebraMap R₁ A r) := rfl
      rw [this, RingHom.toFun_eq_coe, Ideal.Quotient.lift_mk,
        AlgHom.coe_toRingHom, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        map_smul, map_one] }

@[simp]
theorem Quotient.liftₐ_apply (I : Ideal A) [I.IsTwoSided]
    (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) (x) :
    Ideal.Quotient.liftₐ I f hI x = Ideal.Quotient.lift I (f : A →+* B) hI x :=
  rfl

theorem Quotient.liftₐ_comp (I : Ideal A) [I.IsTwoSided]
    (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    (Ideal.Quotient.liftₐ I f hI).comp (Ideal.Quotient.mkₐ R₁ I) = f :=
  AlgHom.ext fun _ => (Ideal.Quotient.lift_mk I (f : A →+* B) hI :)

theorem Quotient.span_singleton_one (I : Ideal A) [I.IsTwoSided] :
    Submodule.span A {(1 : A ⧸ I)} = ⊤ := by
  rw [← map_one (mk _), ← Submodule.range_mkQ I, ← Submodule.map_top, ← Ideal.span_singleton_one,
    Ideal.span, Submodule.map_span, Set.image_singleton, Submodule.mkQ_apply, Quotient.mk_eq_mk]

open Pointwise in
lemma Quotient.smul_top {R : Type*} [CommRing R] (a : R) (I : Ideal R) :
    (a • ⊤ : Submodule R (R ⧸ I)) = Submodule.span R {Submodule.Quotient.mk a} := by
  simp [← Ideal.Quotient.span_singleton_one, Algebra.smul_def, Submodule.smul_span]

theorem KerLift.map_smul (f : A →ₐ[R₁] B) (r : R₁) (x : A ⧸ (RingHom.ker f)) :
    f.kerLift (r • x) = r • f.kerLift x := by
  obtain ⟨a, rfl⟩ := Quotient.mkₐ_surjective R₁ _ x
  exact _root_.map_smul f _ _

/-- The induced algebras morphism from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotientKerAlgEquivOfRightInverse`) /
is surjective (`quotientKerAlgEquivOfSurjective`).
-/
def kerLiftAlg (f : A →ₐ[R₁] B) : A ⧸ (RingHom.ker f) →ₐ[R₁] B :=
  AlgHom.mk' (RingHom.kerLift (f : A →+* B)) fun _ _ => KerLift.map_smul f _ _

@[simp]
theorem kerLiftAlg_mk (f : A →ₐ[R₁] B) (a : A) :
    kerLiftAlg f (Quotient.mk (RingHom.ker f) a) = f a := by
  rfl

@[simp]
theorem kerLiftAlg_toRingHom (f : A →ₐ[R₁] B) :
    (kerLiftAlg f : A ⧸ ker f →+* B) = RingHom.kerLift (f : A →+* B) :=
  rfl

/-- The induced algebra morphism from the quotient by the kernel is injective. -/
theorem kerLiftAlg_injective (f : A →ₐ[R₁] B) : Function.Injective (kerLiftAlg f) :=
  RingHom.kerLift_injective (R := A) (S := B) f

/-- The **first isomorphism** theorem for algebras, computable version. -/
@[simps!]
def quotientKerAlgEquivOfRightInverse {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) : (A ⧸ RingHom.ker f) ≃ₐ[R₁] B :=
  { RingHom.quotientKerEquivOfRightInverse hf,
    kerLiftAlg f with }

/-- The **first isomorphism theorem** for algebras. -/
@[simps!]
noncomputable def quotientKerAlgEquivOfSurjective {f : A →ₐ[R₁] B} (hf : Function.Surjective f) :
    (A ⧸ (RingHom.ker f)) ≃ₐ[R₁] B :=
  quotientKerAlgEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)

end

section Ring_Ring

variable {S : Type v} [Ring S]

/-- The ring hom `R/I →+* S/J` induced by a ring hom `f : R →+* S` with `I ≤ f⁻¹(J)` -/
def quotientMap {I : Ideal R} (J : Ideal S) [I.IsTwoSided] [J.IsTwoSided] (f : R →+* S)
    (hIJ : I ≤ J.comap f) : R ⧸ I →+* S ⧸ J :=
  Quotient.lift I ((Quotient.mk J).comp f) fun _ ha => by
    simpa [Function.comp_apply, RingHom.coe_comp, Quotient.eq_zero_iff_mem] using hIJ ha

@[simp]
theorem quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R →+* S} {H : J ≤ I.comap f} {x : R} :
    quotientMap I f H (Quotient.mk J x) = Quotient.mk I (f x) :=
  Quotient.lift_mk J _ _

@[simp]
theorem quotientMap_algebraMap {J : Ideal A} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : A →+* S} {H : J ≤ I.comap f}
    {x : R₁} : quotientMap I f H (algebraMap R₁ (A ⧸ J) x) = Quotient.mk I (f (algebraMap _ _ x)) :=
  Quotient.lift_mk J _ _

theorem quotientMap_comp_mk {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R →+* S} (H : J ≤ I.comap f) :
    (quotientMap I f H).comp (Quotient.mk J) = (Quotient.mk I).comp f :=
  RingHom.ext fun x => by simp only [Function.comp_apply, RingHom.coe_comp, Ideal.quotientMap_mk]

lemma ker_quotientMap_mk {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided] :
    RingHom.ker (quotientMap (J.map _) (Quotient.mk I) le_comap_map) = I.map (Quotient.mk J) := by
  rw [Ideal.quotientMap, Ideal.ker_quotient_lift, ← RingHom.comap_ker, Ideal.mk_ker,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]

section quotientEquiv

variable (I : Ideal R) (J : Ideal S) [I.IsTwoSided] [J.IsTwoSided]
    (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S))

/-- The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+* S`, where `J = f(I)`. -/
@[simps]
def quotientEquiv : R ⧸ I ≃+* S ⧸ J where
  __ := quotientMap J f (hIJ ▸ le_comap_map)
  invFun := quotientMap I f.symm (hIJ ▸ (map_comap_of_equiv f).le)
  left_inv := by
    rintro ⟨r⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
      quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  right_inv := by
    rintro ⟨s⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
      quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]

-- Not `@[simp]` since `simp` proves it.
theorem quotientEquiv_mk (x : R) :
    quotientEquiv I J f hIJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (f x) :=
  rfl

-- Not `@[simp]` since `simp` proves it.
theorem quotientEquiv_symm_mk (x : S) :
    (quotientEquiv I J f hIJ).symm (Ideal.Quotient.mk J x) = Ideal.Quotient.mk I (f.symm x) :=
  rfl

end quotientEquiv

/-- `H` and `h` are kept as separate hypothesis since H is used in constructing the quotient map. -/
theorem quotientMap_injective' {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R →+* S} {H : J ≤ I.comap f} (h : I.comap f ≤ J) :
    Function.Injective (quotientMap I f H) := by
  refine (injective_iff_map_eq_zero (quotientMap I f H)).2 fun a ha => ?_
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  rw [quotientMap_mk, Quotient.eq_zero_iff_mem] at ha
  exact Quotient.eq_zero_iff_mem.mpr (h ha)

/-- If we take `J = I.comap f` then `quotientMap` is injective automatically. -/
theorem quotientMap_injective {I : Ideal S} {f : R →+* S} [I.IsTwoSided] :
    Function.Injective (quotientMap I f le_rfl) :=
  quotientMap_injective' le_rfl

theorem quotientMap_surjective {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R →+* S} {H : J ≤ I.comap f}
    (hf : Function.Surjective f) : Function.Surjective (quotientMap I f H) := fun x =>
  let ⟨x, hx⟩ := Quotient.mk_surjective x
  let ⟨y, hy⟩ := hf x
  ⟨(Quotient.mk J) y, by simp [hx, hy]⟩

/-- Commutativity of a square is preserved when taking quotients by an ideal. -/
theorem comp_quotientMap_eq_of_comp_eq {R' S' : Type*} [Ring R'] [Ring S'] {f : R →+* S}
    {f' : R' →+* S'} {g : R →+* R'} {g' : S →+* S'} (hfg : f'.comp g = g'.comp f)
    (I : Ideal S') [I.IsTwoSided] :
    let leq := le_of_eq (_root_.trans (comap_comap f g') (hfg ▸ comap_comap g f'))
    (quotientMap I g' le_rfl).comp (quotientMap (I.comap g') f le_rfl) =
    (quotientMap I f' le_rfl).comp (quotientMap (I.comap f') g leq) := by
  refine RingHom.ext fun a => ?_
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  simp only [RingHom.comp_apply, quotientMap_mk]
  exact (Ideal.Quotient.mk I).congr_arg (_root_.trans (g'.comp_apply f r).symm
    (hfg ▸ f'.comp_apply g r))

end Ring_Ring


section

variable [Ring B] [Algebra R₁ B] {I : Ideal A} (J : Ideal B) [I.IsTwoSided] [J.IsTwoSided]

/-- The algebra hom `A/I →+* B/J` induced by an algebra hom `f : A →ₐ[R₁] B` with `I ≤ f⁻¹(J)`. -/
def quotientMapₐ (f : A →ₐ[R₁] B) (hIJ : I ≤ J.comap f) :
    A ⧸ I →ₐ[R₁] B ⧸ J :=
  { quotientMap J (f : A →+* B) hIJ with commutes' := fun r => by simp only [RingHom.toFun_eq_coe,
    quotientMap_algebraMap, AlgHom.coe_toRingHom, AlgHom.commutes, Quotient.mk_algebraMap] }

@[simp]
theorem quotient_map_mkₐ (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) {x : A} :
    quotientMapₐ J f H (Quotient.mk I x) = Quotient.mkₐ R₁ J (f x) :=
  rfl

theorem quotient_map_comp_mkₐ (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) :
    (quotientMapₐ J f H).comp (Quotient.mkₐ R₁ I) = (Quotient.mkₐ R₁ J).comp f :=
  AlgHom.ext fun x => by simp only [quotient_map_mkₐ, Quotient.mkₐ_eq_mk, AlgHom.comp_apply]

variable (I) in
/-- The algebra equiv `A/I ≃ₐ[R] B/J` induced by an algebra equiv `f : A ≃ₐ[R] B`,
where`J = f(I)`. -/
def quotientEquivAlg (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
    (A ⧸ I) ≃ₐ[R₁] B ⧸ J :=
  { quotientEquiv I J (f : A ≃+* B) hIJ with
    commutes' r := by simp }

end

/-- If `P` lies over `p`, then `R / p` has a canonical map to `A / P`. -/
abbrev Quotient.algebraQuotientOfLEComap {R} [CommRing R] [Algebra R A] {p : Ideal R}
    {P : Ideal A} [P.IsTwoSided] (h : p ≤ comap (algebraMap R A) P) :
    Algebra (R ⧸ p) (A ⧸ P) where
  algebraMap := quotientMap P (algebraMap R A) h
  smul := Quotient.lift₂ (⟦· • ·⟧) fun r₁ a₁ r₂ a₂ hr ha ↦ Quotient.sound <| by
    have := h (p.quotientRel_def.mp hr)
    rw [mem_comap, map_sub] at this
    simpa only [Algebra.smul_def] using P.quotientRel_def.mpr
      (P.mul_sub_mul_mem this <| P.quotientRel_def.mp ha)
  smul_def' := by rintro ⟨_⟩ ⟨_⟩; exact congr_arg (⟦·⟧) (Algebra.smul_def _ _)
  commutes' := by rintro ⟨_⟩ ⟨_⟩; exact congr_arg (⟦·⟧) (Algebra.commutes _ _)

instance (priority := 100) quotientAlgebra {R} [CommRing R] {I : Ideal A} [I.IsTwoSided]
    [Algebra R A] : Algebra (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  Quotient.algebraQuotientOfLEComap le_rfl

instance (R) {A} [CommRing R] [CommRing A] (I : Ideal A) [Algebra R A] :
    Algebra (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) := inferInstance

theorem algebraMap_quotient_injective {R} [CommRing R] {I : Ideal A} [I.IsTwoSided] [Algebra R A] :
    Function.Injective (algebraMap (R ⧸ I.comap (algebraMap R A)) (A ⧸ I)) := by
  rintro ⟨a⟩ ⟨b⟩ hab
  replace hab := Quotient.eq.mp hab
  rw [← RingHom.map_sub] at hab
  exact Quotient.eq.mpr hab

variable (R₁)

/-- Quotienting by equal ideals gives equivalent algebras. -/
def quotientEquivAlgOfEq {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
    (A ⧸ I) ≃ₐ[R₁] A ⧸ J :=
  quotientEquivAlg I J AlgEquiv.refl <| h ▸ (map_id I).symm

@[simp]
theorem quotientEquivAlgOfEq_mk {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) (x : A) :
    quotientEquivAlgOfEq R₁ h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl

@[simp]
theorem quotientEquivAlgOfEq_symm {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
    (quotientEquivAlgOfEq R₁ h).symm = quotientEquivAlgOfEq R₁ h.symm := by
  ext
  rfl

lemma comap_map_mk {I J : Ideal R} [I.IsTwoSided] (h : I ≤ J) :
    Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = J := by
  ext; rw [← Ideal.mem_quotient_iff_mem h, Ideal.mem_comap]

/-- The **first isomorphism theorem** for commutative algebras (`AlgHom.range` version). -/
noncomputable def quotientKerEquivRange
    {R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Semiring B] [Algebra R B]
    (f : A →ₐ[R] B) :
    (A ⧸ RingHom.ker f) ≃ₐ[R] f.range :=
  (Ideal.quotientEquivAlgOfEq R (AlgHom.ker_rangeRestrict f).symm).trans <|
    Ideal.quotientKerAlgEquivOfSurjective f.rangeRestrict_surjective

end QuotientAlgebra

end Ideal

section quotientBot

variable {R S : Type*}

variable (R) in
/-- The quotient of a ring by he zero ideal is isomorphic to the ring itself. -/
def RingEquiv.quotientBot [Ring R] : R ⧸ (⊥ : Ideal R) ≃+* R :=
  (Ideal.quotEquivOfEq (RingHom.ker_coe_equiv <| .refl _).symm).trans <|
    RingHom.quotientKerEquivOfRightInverse (f := .id R) (g := _root_.id) fun _ ↦ rfl

@[simp]
lemma RingEquiv.quotientBot_mk [Ring R] (r : R) :
    RingEquiv.quotientBot R (Ideal.Quotient.mk ⊥ r) = r :=
  rfl

@[simp]
lemma RingEquiv.quotientBot_symm_mk [Ring R] (r : R) :
    (RingEquiv.quotientBot R).symm r = r :=
  rfl

variable (R S) in
/-- `RingEquiv.quotientBot` as an algebra isomorphism. -/
def AlgEquiv.quotientBot [CommSemiring R] [Ring S] [Algebra R S] :
    (S ⧸ (⊥ : Ideal S)) ≃ₐ[R] S where
  __ := RingEquiv.quotientBot S
  commutes' x := by simp [← Ideal.Quotient.mk_algebraMap]

@[simp]
lemma AlgEquiv.quotientBot_mk [CommSemiring R] [CommRing S] [Algebra R S] (s : S) :
    AlgEquiv.quotientBot R S (Ideal.Quotient.mk ⊥ s) = s :=
  rfl

@[simp]
lemma AlgEquiv.quotientBot_symm_mk [CommSemiring R] [CommRing S] [Algebra R S]
    (s : S) : (AlgEquiv.quotientBot R S).symm s = s :=
  rfl

end quotientBot

namespace DoubleQuot

open Ideal

variable {R : Type u}

section

variable [CommRing R] (I J : Ideal R)

/-- The obvious ring hom `R/I → R/(I ⊔ J)` -/
def quotLeftToQuotSup : R ⧸ I →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.factor le_sup_left

/-- The kernel of `quotLeftToQuotSup` -/
theorem ker_quotLeftToQuotSup : RingHom.ker (quotLeftToQuotSup I J) =
    J.map (Ideal.Quotient.mk I) := by
  simp only [mk_ker, sup_idem, sup_comm, quotLeftToQuotSup, Quotient.factor, ker_quotient_lift,
    map_eq_iff_sup_ker_eq_of_surjective (Ideal.Quotient.mk I) Quotient.mk_surjective, ← sup_assoc]

/-- The ring homomorphism `(R/I)/J' -> R/(I ⊔ J)` induced by `quotLeftToQuotSup` where `J'`
  is the image of `J` in `R/I` -/
def quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.lift (J.map (Ideal.Quotient.mk I)) (quotLeftToQuotSup I J)
    (ker_quotLeftToQuotSup I J).symm.le

/-- The composite of the maps `R → (R/I)` and `(R/I) → (R/I)/J'` -/
def quotQuotMk : R →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I))).comp (Ideal.Quotient.mk I)

/-- The kernel of `quotQuotMk` -/
theorem ker_quotQuotMk : RingHom.ker (quotQuotMk I J) = I ⊔ J := by
  rw [RingHom.ker_eq_comap_bot, quotQuotMk, ← comap_comap, ← RingHom.ker, mk_ker,
    comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, ← RingHom.ker,
    mk_ker, sup_comm]

/-- The ring homomorphism `R/(I ⊔ J) → (R/I)/J' `induced by `quotQuotMk` -/
def liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I ⊔ J →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  Ideal.Quotient.lift (I ⊔ J) (quotQuotMk I J) (ker_quotQuotMk I J).symm.le

/-- `quotQuotToQuotSup` and `liftSupQuotQuotMk` are inverse isomorphisms. In the case where
`I ≤ J`, this is the Third Isomorphism Theorem (see `quotQuotEquivQuotOfLe`). -/
def quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J :=
  RingEquiv.ofHomInv (quotQuotToQuotSup I J) (liftSupQuotQuotMk I J)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)

@[simp]
theorem quotQuotEquivQuotSup_quotQuotMk (x : R) :
    quotQuotEquivQuotSup I J (quotQuotMk I J x) = Ideal.Quotient.mk (I ⊔ J) x :=
  rfl

@[simp]
theorem quotQuotEquivQuotSup_symm_quotQuotMk (x : R) :
    (quotQuotEquivQuotSup I J).symm (Ideal.Quotient.mk (I ⊔ J) x) = quotQuotMk I J x :=
  rfl

/-- The obvious isomorphism `(R/I)/J' → (R/J)/I'` -/
def quotQuotEquivComm : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+*
    (R ⧸ J) ⧸ I.map (Ideal.Quotient.mk J) :=
  ((quotQuotEquivQuotSup I J).trans (quotEquivOfEq (sup_comm ..))).trans
    (quotQuotEquivQuotSup J I).symm

@[simp]
theorem quotQuotEquivComm_quotQuotMk (x : R) :
    quotQuotEquivComm I J (quotQuotMk I J x) = quotQuotMk J I x :=
  rfl

@[simp]
theorem quotQuotEquivComm_comp_quotQuotMk :
    RingHom.comp (↑(quotQuotEquivComm I J)) (quotQuotMk I J) = quotQuotMk J I :=
  RingHom.ext <| quotQuotEquivComm_quotQuotMk I J

@[simp]
theorem quotQuotEquivComm_symm : (quotQuotEquivComm I J).symm = quotQuotEquivComm J I := by
  rfl

variable {I J}

/-- **The Third Isomorphism theorem** for rings. See `quotQuotEquivQuotSup` for a version
    that does not assume an inclusion of ideals. -/
def quotQuotEquivQuotOfLE (h : I ≤ J) : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ J :=
  (quotQuotEquivQuotSup I J).trans (Ideal.quotEquivOfEq <| sup_eq_right.mpr h)

@[simp]
theorem quotQuotEquivQuotOfLE_quotQuotMk (x : R) (h : I ≤ J) :
    quotQuotEquivQuotOfLE h (quotQuotMk I J x) = (Ideal.Quotient.mk J) x :=
  rfl

@[simp]
theorem quotQuotEquivQuotOfLE_symm_mk (x : R) (h : I ≤ J) :
    (quotQuotEquivQuotOfLE h).symm ((Ideal.Quotient.mk J) x) = quotQuotMk I J x :=
  rfl

theorem quotQuotEquivQuotOfLE_comp_quotQuotMk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h)) (quotQuotMk I J) = (Ideal.Quotient.mk J) := by
  ext
  rfl

theorem quotQuotEquivQuotOfLE_symm_comp_mk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h).symm) (Ideal.Quotient.mk J) = quotQuotMk I J := by
  ext
  rfl

end

section Algebra

@[simp]
theorem quotQuotEquivComm_mk_mk [CommRing R] (I J : Ideal R) (x : R) :
    quotQuotEquivComm I J (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) = algebraMap R _ x :=
  rfl

variable [CommSemiring R] {A : Type v} [CommRing A] [Algebra R A] (I J : Ideal A)

@[simp]
theorem quotQuotEquivQuotSup_quot_quot_algebraMap (x : R) :
    DoubleQuot.quotQuotEquivQuotSup I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl

@[simp]
theorem quotQuotEquivComm_algebraMap (x : R) :
    quotQuotEquivComm I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl

end Algebra

section AlgebraQuotient

variable (R) {A : Type*} [CommSemiring R] [CommRing A] [Algebra R A] (I J : Ideal A)

/-- The natural algebra homomorphism `A / I → A / (I ⊔ J)`. -/
def quotLeftToQuotSupₐ : A ⧸ I →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotLeftToQuotSup I J) fun _ => rfl

@[simp]
theorem quotLeftToQuotSupₐ_toRingHom :
    (quotLeftToQuotSupₐ R I J : _ →+* _) = quotLeftToQuotSup I J :=
  rfl

@[simp]
theorem coe_quotLeftToQuotSupₐ : ⇑(quotLeftToQuotSupₐ R I J) = quotLeftToQuotSup I J :=
  rfl

/-- The algebra homomorphism `(A / I) / J' -> A / (I ⊔ J)` induced by `quotQuotToQuotSup`,
  where `J'` is the projection of `J` in `A / I`. -/
def quotQuotToQuotSupₐ : (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotQuotToQuotSup I J) fun _ => rfl

@[simp]
theorem quotQuotToQuotSupₐ_toRingHom :
    ((quotQuotToQuotSupₐ R I J) : _ ⧸ map (Ideal.Quotient.mkₐ R I) J →+* _) =
      quotQuotToQuotSup I J :=
  rfl

@[simp]
theorem coe_quotQuotToQuotSupₐ : ⇑(quotQuotToQuotSupₐ R I J) = quotQuotToQuotSup I J :=
  rfl

/-- The composition of the algebra homomorphisms `A → (A / I)` and `(A / I) → (A / I) / J'`,
  where `J'` is the projection `J` in `A / I`. -/
def quotQuotMkₐ : A →ₐ[R] (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) :=
  AlgHom.mk (quotQuotMk I J) fun _ => rfl

@[simp]
theorem quotQuotMkₐ_toRingHom :
    (quotQuotMkₐ R I J : _ →+* _ ⧸ J.map (Quotient.mkₐ R I)) = quotQuotMk I J :=
  rfl

@[simp]
theorem coe_quotQuotMkₐ : ⇑(quotQuotMkₐ R I J) = quotQuotMk I J :=
  rfl

/-- The injective algebra homomorphism `A / (I ⊔ J) → (A / I) / J'`induced by `quot_quot_mk`,
  where `J'` is the projection `J` in `A / I`. -/
def liftSupQuotQuotMkₐ (I J : Ideal A) : A ⧸ I ⊔ J →ₐ[R] (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) :=
  AlgHom.mk (liftSupQuotQuotMk I J) fun _ => rfl

@[simp]
theorem liftSupQuotQuotMkₐ_toRingHom :
    (liftSupQuotQuotMkₐ R I J : _ →+* _ ⧸ J.map (Quotient.mkₐ R I)) = liftSupQuotQuotMk I J :=
  rfl

@[simp]
theorem coe_liftSupQuotQuotMkₐ : ⇑(liftSupQuotQuotMkₐ R I J) = liftSupQuotQuotMk I J :=
  rfl

/-- `quotQuotToQuotSup` and `liftSupQuotQuotMk` are inverse isomorphisms. In the case where
`I ≤ J`, this is the Third Isomorphism Theorem (see `DoubleQuot.quotQuotEquivQuotOfLE`). -/
def quotQuotEquivQuotSupₐ : ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] A ⧸ I ⊔ J :=
  AlgEquiv.ofRingEquiv (f := quotQuotEquivQuotSup I J) fun _ => rfl

@[simp]
theorem quotQuotEquivQuotSupₐ_toRingEquiv :
    (quotQuotEquivQuotSupₐ R I J : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _) = quotQuotEquivQuotSup I J :=
  rfl

@[simp]
theorem coe_quotQuotEquivQuotSupₐ : ⇑(quotQuotEquivQuotSupₐ R I J) = quotQuotEquivQuotSup I J :=
  rfl

@[simp]
theorem quotQuotEquivQuotSupₐ_symm_toRingEquiv :
    ((quotQuotEquivQuotSupₐ R I J).symm : _ ≃+* _ ⧸ J.map (Quotient.mkₐ R I)) =
      (quotQuotEquivQuotSup I J).symm :=
  rfl

@[simp]
theorem coe_quotQuotEquivQuotSupₐ_symm :
    ⇑(quotQuotEquivQuotSupₐ R I J).symm = (quotQuotEquivQuotSup I J).symm :=
  rfl

/-- The natural algebra isomorphism `(A / I) / J' → (A / J) / I'`,
  where `J'` (resp. `I'`) is the projection of `J` in `A / I` (resp. `I` in `A / J`). -/
def quotQuotEquivCommₐ :
    ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] (A ⧸ J) ⧸ I.map (Quotient.mkₐ R J) :=
  AlgEquiv.ofRingEquiv (f := quotQuotEquivComm I J) fun _ => rfl

@[simp]
theorem quotQuotEquivCommₐ_toRingEquiv :
    (quotQuotEquivCommₐ R I J : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _ ⧸ I.map (Quotient.mkₐ R J)) =
      quotQuotEquivComm I J :=
  rfl

@[simp]
theorem coe_quotQuotEquivCommₐ : ⇑(quotQuotEquivCommₐ R I J) = ⇑(quotQuotEquivComm I J) :=
  rfl

@[simp]
theorem quotQuotEquivComm_symmₐ : (quotQuotEquivCommₐ R I J).symm = quotQuotEquivCommₐ R J I := by
  rfl

@[simp]
theorem quotQuotEquivComm_comp_quotQuotMkₐ :
    AlgHom.comp (↑(quotQuotEquivCommₐ R I J)) (quotQuotMkₐ R I J) = quotQuotMkₐ R J I :=
  AlgHom.ext <| quotQuotEquivComm_quotQuotMk I J

variable {I J}

/-- The **third isomorphism theorem** for algebras. See `quotQuotEquivQuotSupₐ` for version
    that does not assume an inclusion of ideals. -/
def quotQuotEquivQuotOfLEₐ (h : I ≤ J) : ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] A ⧸ J :=
  AlgEquiv.ofRingEquiv (f := quotQuotEquivQuotOfLE h) fun _ => rfl

@[simp]
theorem quotQuotEquivQuotOfLEₐ_toRingEquiv (h : I ≤ J) :
    (quotQuotEquivQuotOfLEₐ R h : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _) = quotQuotEquivQuotOfLE h :=
  rfl

@[simp]
theorem coe_quotQuotEquivQuotOfLEₐ (h : I ≤ J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h) = quotQuotEquivQuotOfLE h :=
  rfl

@[simp]
theorem quotQuotEquivQuotOfLEₐ_symm_toRingEquiv (h : I ≤ J) :
    ((quotQuotEquivQuotOfLEₐ R h).symm : _ ≃+* _ ⧸ J.map (Quotient.mkₐ R I)) =
      (quotQuotEquivQuotOfLE h).symm :=
  rfl

@[simp]
theorem coe_quotQuotEquivQuotOfLEₐ_symm (h : I ≤ J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h).symm = (quotQuotEquivQuotOfLE h).symm :=
  rfl

@[simp]
theorem quotQuotEquivQuotOfLE_comp_quotQuotMkₐ (h : I ≤ J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h)) (quotQuotMkₐ R I J) = Quotient.mkₐ R J :=
  rfl

@[simp]
theorem quotQuotEquivQuotOfLE_symm_comp_mkₐ (h : I ≤ J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h).symm) (Quotient.mkₐ R J) = quotQuotMkₐ R I J :=
  rfl

end AlgebraQuotient
end DoubleQuot

namespace Ideal

section PowQuot

variable {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)

/-- `I ^ n ⧸ I ^ (n + 1)` can be viewed as a quotient module and as ideal of `R ⧸ I ^ (n + 1)`.
This definition gives the `R`-linear equivalence between the two. -/
noncomputable
def powQuotPowSuccLinearEquivMapMkPowSuccPow :
    ((I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R))) ≃ₗ[R]
    Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n) := by
  refine { LinearMap.codRestrict
    (Submodule.restrictScalars _ (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)))
    (Submodule.mapQ (I • ⊤) (I ^ (n + 1)) (Submodule.subtype (I ^ n)) ?_) ?_,
    Equiv.ofBijective _ ⟨?_, ?_⟩ with }
  · intro
    simp [Submodule.mem_smul_top_iff, pow_succ']
  · intro x
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [Ideal.mem_sup_left hy]
  · intro a b
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    simp [Ideal.Quotient.eq, Submodule.Quotient.eq, Submodule.mem_smul_top_iff, pow_succ']
  · intro ⟨x, hx⟩
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    simp

/-- `I ^ n ⧸ I ^ (n + 1)` can be viewed as a quotient module and as ideal of `R ⧸ I ^ (n + 1)`.
This definition gives the equivalence between the two, instead of the `R`-linear equivalence,
to bypass typeclass synthesis issues on complex `Module` goals. -/
noncomputable
def powQuotPowSuccEquivMapMkPowSuccPow :
    ((I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R))) ≃
    Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n) :=
  powQuotPowSuccLinearEquivMapMkPowSuccPow I n

end PowQuot

end Ideal
