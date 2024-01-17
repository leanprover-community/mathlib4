/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.Finiteness

#align_import ring_theory.graded_algebra.homogeneous_ideal from "leanprover-community/mathlib"@"4e861f25ba5ceef42ba0712d8ffeb32f38ad6441"

/-!
# Homogeneous ideals of a graded algebra

This file defines homogeneous ideals of `GradedRing 𝒜` where `𝒜 : ι → Submodule R A` and
operations on them.

## Main definitions

For any `I : Ideal A`:
* `Ideal.IsHomogeneous 𝒜 I`: The property that an ideal is closed under `GradedRing.proj`.
* `HomogeneousSubmodule A ℳ`: The structure extending ideals which satisfy `Ideal.IsHomogeneous`.
* `Ideal.homogeneousCore I 𝒜`: The largest homogeneous ideal smaller than `I`.
* `Ideal.homogeneousHull I 𝒜`: The smallest homogeneous ideal larger than `I`.

## Main statements

* `HomogeneousSubmodule.completeLattice`: `Ideal.IsHomogeneous` is preserved by `⊥`, `⊤`, `⊔`, `⊓`,
  `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `Ideal.homogeneousCore.gi`: `Ideal.homogeneousCore` forms a galois insertion with coercion.
* `Ideal.homogeneousHull.gi`: `Ideal.homogeneousHull` forms a galois insertion with coercion.

## Implementation notes

We introduce `Submodule.homogeneousCore'` earlier than might be expected so that we can get access
to `Ideal.IsHomogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/


open SetLike DirectSum Set

open BigOperators Pointwise DirectSum

variable {ιA ιM σA σM R A M : Type*} [AddCommMonoid M] [SetLike σM M] [AddSubmonoidClass σM M]
variable [DecidableEq ιA] [DecidableEq ιM]

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)
variable [Decomposition ℳ]

section HomogeneousDef

variable [Semiring A] [Module A M]
variable [SetLike σA A] [AddSubmonoidClass σA A]
variable [DecidableEq ιA] [AddMonoid ιA] [GradedRing 𝒜]

variable (p : Submodule A M) (I : Ideal A)

/-- An `p : Submodule A M` is homogeneous if for every `m ∈ p`, all homogeneous components
  of `m` are in `I`. -/
def Submodule.IsHomogeneous : Prop :=
  ∀ (i : ιM) ⦃m : M⦄, m ∈ p → (DirectSum.decompose ℳ m i : M) ∈ p
#align ideal.is_homogeneous Submodule.IsHomogeneous

/-- An `I : Ideal A` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`. -/
def Ideal.IsHomogeneous : Prop :=
  Submodule.IsHomogeneous 𝒜 I

variable (A) in
/-- For any `Semiring A`, we collect the homogeneous submodule of `A`-modules into a type. -/
structure HomogeneousSubmodule extends Submodule A M where
  is_homogeneous' : Submodule.IsHomogeneous ℳ toSubmodule
#align homogeneous_ideal HomogeneousSubmodule


/-- For any `Semiring A`, we collect the homogeneous ideals of `A` into a type. -/
def HomogeneousIdeal := HomogeneousSubmodule A 𝒜

variable {𝒜 ℳ}

/-- Converting a homogeneous ideal to an ideal. -/
def HomogeneousIdeal.toIdeal (I : HomogeneousIdeal 𝒜) : Ideal A :=
  I.toSubmodule
#align homogeneous_ideal.to_ideal HomogeneousIdeal.toIdeal

lemma HomogeneousIdeal.isHomogeneous (I : HomogeneousIdeal 𝒜) : I.IsHomogeneous 𝒜 := I.2

theorem HomogeneousSubmodule.isHomogeneous (I : HomogeneousSubmodule A ℳ) :
    I.toSubmodule.IsHomogeneous ℳ :=
  I.is_homogeneous'
#align homogeneous_ideal.is_homogeneous HomogeneousSubmodule.isHomogeneous

theorem HomogeneousSubmodule.toSubmodule_injective :
    Function.Injective (HomogeneousSubmodule.toSubmodule : HomogeneousSubmodule A ℳ→ Submodule A M) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]
#align homogeneous_ideal.to_ideal_injective HomogeneousSubmodule.toSubmodule_injective

instance HomogeneousSubmodule.setLike : SetLike (HomogeneousSubmodule A ℳ) M where
  coe p := p.toSubmodule
  coe_injective' _ _ h := HomogeneousSubmodule.toSubmodule_injective <| SetLike.coe_injective h

instance HomogeneousIdeal.setLike : SetLike (HomogeneousIdeal 𝒜) A := HomogeneousSubmodule.setLike
#align homogeneous_ideal.set_like HomogeneousIdeal.setLike

@[ext]
theorem HomogeneousSubmodule.ext
    {I J : HomogeneousSubmodule A ℳ} (h : I.toSubmodule = J.toSubmodule) : I = J :=
  HomogeneousSubmodule.toSubmodule_injective h
#align homogeneous_ideal.ext HomogeneousSubmodule.ext

@[simp]
theorem HomogeneousSubmodule.mem_iff {I : HomogeneousSubmodule A ℳ} {x : M} :
    x ∈ I.toSubmodule ↔ x ∈ I :=
  Iff.rfl
#align homogeneous_ideal.mem_iff HomogeneousSubmodule.mem_iff

end HomogeneousDef

section HomogeneousCore

variable [Semiring A] [Module A M]

variable (p : Submodule A M)

/-- For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousCore' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal. -/
def Submodule.homogeneousCore' (I : Submodule A M) : Submodule A M :=
  Submodule.span A ((↑) '' (((↑) : Subtype (Homogeneous ℳ) → M) ⁻¹' I))
#align ideal.homogeneous_core' Submodule.homogeneousCore'

theorem Submodule.homogeneousCore'_mono : Monotone (Submodule.homogeneousCore' (A := A) ℳ) :=
  fun _ _ I_le_J => Submodule.span_mono <| Set.image_subset _ fun _ => @I_le_J _
#align ideal.homogeneous_core'_mono Submodule.homogeneousCore'_mono

theorem Submodule.homogeneousCore'_le : p.homogeneousCore' ℳ ≤ p :=
  Submodule.span_le.2 <| image_preimage_subset _ _
#align ideal.homogeneous_core'_le Submodule.homogeneousCore'_le

end HomogeneousCore

section IsHomogeneousSubmoduleDefs

variable [AddMonoid ιA] [SetLike σA A] [SetLike σA A]

variable [Semiring A] [AddSubmonoidClass σA A] [Module A M] [GradedRing 𝒜]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

variable (p : Submodule A M) (I : Ideal A)

theorem Submodule.isHomogeneous_iff_forall_subset :
    p.IsHomogeneous ℳ ↔ ∀ i, (p : Set M) ⊆ GradedModule.proj ℳ i ⁻¹' (p : Set M) :=
  Iff.rfl
#align ideal.is_homogeneous_iff_forall_subset Submodule.isHomogeneous_iff_forall_subset

theorem Submodule.isHomogeneous_iff_subset_iInter :
    p.IsHomogeneous ℳ ↔ (p : Set M) ⊆ ⋂ i, GradedModule.proj ℳ i ⁻¹' ↑p :=
  subset_iInter_iff.symm
#align ideal.is_homogeneous_iff_subset_Inter Submodule.isHomogeneous_iff_subset_iInter

theorem Submodule.mul_homogeneous_element_mem_of_mem {p : Submodule A M} (r : A) (x : M)
    (hx₁ : Homogeneous ℳ x) (hx₂ : x ∈ p) (j : ιM) : GradedModule.proj ℳ j (r • x) ∈ p := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_smul, map_sum]
  apply Submodule.sum_mem
  intro k _
  obtain ⟨i, hi⟩ := hx₁
  have mem₁ : (DirectSum.decompose 𝒜 r k : A) • x ∈ ℳ (k +ᵥ i) :=
    GradedSMul.smul_mem (SetLike.coe_mem _) hi
  erw [GradedModule.proj_apply, DirectSum.decompose_of_mem ℳ mem₁, coe_of_apply]
  split_ifs with h
  · exact Submodule.smul_mem _ _ hx₂
  · exact p.zero_mem
#align ideal.mul_homogeneous_element_mem_of_mem Submodule.mul_homogeneous_element_mem_of_mem

theorem Submodule.homogeneous_span (s : Set M) (h : ∀ x ∈ s, Homogeneous ℳ x) :
    (Submodule.span A s).IsHomogeneous ℳ := by
  rintro i r hr
  rw [mem_span_set] at hr
  obtain ⟨c, hc, rfl⟩ := hr
  rw [ Finsupp.sum, decompose_sum, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  refine' Submodule.sum_mem _ _
  rintro z hz1
  apply Submodule.mul_homogeneous_element_mem_of_mem (𝒜 := 𝒜) (ℳ := ℳ)
  · exact h _ (hc hz1)
  · exact Submodule.subset_span (hc hz1)
#align ideal.is_homogeneous_span Submodule.homogeneous_span

/-- For any `p : Submodule A M`, not necessarily homogeneous, `p.homogeneousCore' ℳ`
is the largest homogeneous ideal of `A` contained in `I`. -/
def Submodule.homogeneousCore : HomogeneousSubmodule A ℳ :=
  ⟨p.homogeneousCore' ℳ,
    Submodule.homogeneous_span 𝒜 _ _ fun _ h => (Subtype.image_preimage_coe _ _ ▸ h).2⟩
#align ideal.homogeneous_core Submodule.homogeneousCore

theorem Submodule.homogeneousCore_mono : Monotone (Submodule.homogeneousCore 𝒜 ℳ) :=
  Submodule.homogeneousCore'_mono ℳ
#align ideal.homogeneous_core_mono Submodule.homogeneousCore_mono

theorem Submodule.toSubmodule_homogeneousCore_le : (p.homogeneousCore 𝒜 ℳ).toSubmodule ≤ p :=
  Submodule.homogeneousCore'_le ℳ p
#align ideal.to_ideal_homogeneous_core_le Submodule.toSubmodule_homogeneousCore_le

variable {𝒜 I}

theorem Submodule.mem_homogeneousCore_of_homogeneous_of_mem {x : M} (h : Homogeneous ℳ x)
    (hmem : x ∈ p) : x ∈ p.homogeneousCore 𝒜 ℳ :=
  Submodule.subset_span ⟨⟨x, h⟩, hmem, rfl⟩
#align ideal.mem_homogeneous_core_of_is_homogeneous_of_mem Submodule.mem_homogeneousCore_of_homogeneous_of_mem

theorem Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self (h : p.IsHomogeneous ℳ) :
    (p.homogeneousCore 𝒜 ℳ).toSubmodule = p := by
  apply le_antisymm (p.homogeneousCore'_le ℳ) _
  intro x hx
  classical
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨⟨_, homogeneous_coe _⟩, h _ hx, rfl⟩
#align ideal.is_homogeneous.to_ideal_homogeneous_core_eq_self Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self

@[simp]
theorem HomogeneousSubmodule.toSubmodule_homogeneousCore_eq_self (p : HomogeneousSubmodule A ℳ) :
    p.toSubmodule.homogeneousCore 𝒜 ℳ = p := by
  ext1
  convert Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self ℳ _ p.isHomogeneous
#align homogeneous_ideal.to_ideal_homogeneous_core_eq_self HomogeneousSubmodule.toSubmodule_homogeneousCore_eq_self

variable (𝒜 I)

theorem Submodule.IsHomogeneous.iff_eq : p.IsHomogeneous ℳ ↔ (p.homogeneousCore 𝒜 ℳ).toSubmodule = p :=
  ⟨fun hI => hI.toSubmodule_homogeneousCore_eq_self, fun hI => hI ▸ (p.homogeneousCore 𝒜 ℳ).2⟩
#align ideal.is_homogeneous.iff_eq Submodule.IsHomogeneous.iff_eq

theorem Submodule.IsHomogeneous.iff_exists :
    p.IsHomogeneous ℳ ↔ ∃ S : Set {x // Homogeneous ℳ x}, p = Submodule.span A ((↑) '' S) := by
  rw [Submodule.IsHomogeneous.iff_eq 𝒜, eq_comm]
  exact ((Set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm

theorem Ideal.IsHomogeneous.iff_exists :
    I.IsHomogeneous 𝒜 ↔ ∃ S : Set (homogeneousSubmonoid 𝒜), I = Ideal.span ((↑) '' S) :=
  Submodule.IsHomogeneous.iff_exists 𝒜 𝒜 I
#align ideal.is_homogeneous.iff_exists Ideal.IsHomogeneous.iff_exists

end IsHomogeneousSubmoduleDefs

/-! ### Operations

In this section, we show that `Ideal.IsHomogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `HomogeneousSubmodule`. -/


section Operations

section Semiring

variable [Semiring A] [Module A M]

variable [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A]
variable [GradedRing 𝒜] [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

namespace Submodule.IsHomogeneous

theorem bot : Submodule.IsHomogeneous (A := A) ℳ ⊥ := fun i r hr => by
  simp only [Submodule.mem_bot] at hr
  rw [hr, decompose_zero, zero_apply]
  apply Submodule.zero_mem
#align ideal.is_homogeneous.bot Submodule.IsHomogeneous.bot

theorem top : Submodule.IsHomogeneous (A := A) ℳ ⊤ := fun i r _ => by simp only [Submodule.mem_top]
#align ideal.is_homogeneous.top Submodule.IsHomogeneous.top

variable {𝒜 ℳ}

theorem inf {I J : Submodule A M} (HI : I.IsHomogeneous ℳ) (HJ : J.IsHomogeneous ℳ) :
    (I ⊓ J).IsHomogeneous ℳ :=
  fun _ _ hr => ⟨HI _ hr.1, HJ _ hr.2⟩
#align ideal.is_homogeneous.inf Submodule.IsHomogeneous.inf

theorem sup {I J : Submodule A M} (HI : I.IsHomogeneous ℳ) (HJ : J.IsHomogeneous ℳ) :
    (I ⊔ J).IsHomogeneous ℳ := by
  rw [iff_exists 𝒜 ℳ] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  refine' ⟨s₁ ∪ s₂, _⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm
#align ideal.is_homogeneous.sup Submodule.IsHomogeneous.sup

protected theorem iSup {κ : Sort*} {f : κ → Submodule A M} (h : ∀ i, (f i).IsHomogeneous ℳ) :
    (⨆ i, f i).IsHomogeneous ℳ := by
  simp_rw [iff_exists 𝒜 ℳ] at h ⊢
  choose s hs using h
  refine' ⟨⋃ i, s i, _⟩
  simp_rw [Set.image_iUnion, Submodule.span_iUnion]
  congr
  exact funext hs
#align ideal.is_homogeneous.supr Submodule.IsHomogeneous.iSup

protected theorem iInf {κ : Sort*} {f : κ → Submodule A M} (h : ∀ i, (f i).IsHomogeneous ℳ) :
    (⨅ i, f i).IsHomogeneous ℳ := by
  intro i x hx
  simp only [Submodule.mem_iInf] at hx ⊢
  exact fun j => h _ _ (hx j)
#align ideal.is_homogeneous.infi Submodule.IsHomogeneous.iInf

theorem iSup₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Submodule A M}
    (h : ∀ i j, (f i j).IsHomogeneous ℳ) : (⨆ (i) (j), f i j).IsHomogeneous ℳ :=
  IsHomogeneous.iSup (𝒜 := 𝒜) fun i => IsHomogeneous.iSup (𝒜 := 𝒜) <| h i
#align ideal.is_homogeneous.supr₂ Submodule.IsHomogeneous.iSup₂

theorem iInf₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Submodule A M}
    (h : ∀ i j, (f i j).IsHomogeneous ℳ) : (⨅ (i) (j), f i j).IsHomogeneous ℳ :=
  IsHomogeneous.iInf fun i => IsHomogeneous.iInf <| h i
#align ideal.is_homogeneous.infi₂ Submodule.IsHomogeneous.iInf₂

theorem sSup {ℐ : Set (Submodule A M)} (h : ∀ I ∈ ℐ, I.IsHomogeneous ℳ) :
    (sSup ℐ).IsHomogeneous ℳ := by
  rw [sSup_eq_iSup]
  exact iSup₂ (𝒜 := 𝒜) h
#align ideal.is_homogeneous.Sup Submodule.IsHomogeneous.sSup

theorem sInf {ℐ : Set (Submodule A M)} (h : ∀ I ∈ ℐ, I.IsHomogeneous ℳ) :
    (sInf ℐ).IsHomogeneous ℳ := by
  rw [sInf_eq_iInf]
  exact iInf₂ h
#align ideal.is_homogeneous.Inf Submodule.IsHomogeneous.sInf

end Submodule.IsHomogeneous

variable {𝒜 ℳ}

namespace HomogeneousSubmodule

instance : PartialOrder (HomogeneousSubmodule A ℳ) :=
  SetLike.instPartialOrder

instance : Top (HomogeneousSubmodule A ℳ) :=
  ⟨⟨⊤, Submodule.IsHomogeneous.top ℳ⟩⟩

instance : Bot (HomogeneousSubmodule A ℳ) :=
  ⟨⟨⊥, Submodule.IsHomogeneous.bot ℳ⟩⟩

-- set_option synthInstance.checkSynthOrder false in
-- instance
--     {A : Type*} [Semiring A]
--     {ιA : Type*} {σA : Type*} (𝒜 : semiOutParam <| ιA → σA)
--     [DecidableEq ιA]
--     [AddMonoid ιA]
--     [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]

--     {ιM σM M : Type*} (ℳ : ιM → σM)
--     [AddCommMonoid M] [Module A M] [SetLike σM M]
--     [DecidableEq ιM]

--     [AddSubmonoidClass σM M] [Decomposition ℳ]
--     [VAdd ιA ιM] [GradedSMul 𝒜 ℳ] : Sup (HomogeneousSubmodule A ℳ) :=
--   ⟨fun I J => ⟨I.toSubmodule ⊔ J.toSubmodule, I.isHomogeneous.sup (𝒜 := 𝒜) J.isHomogeneous⟩⟩

set_option synthInstance.checkSynthOrder false in
instance : Sup (HomogeneousSubmodule A ℳ) :=
  ⟨fun I J => ⟨I.toSubmodule ⊔ J.toSubmodule, I.isHomogeneous.sup (𝒜 := 𝒜) J.isHomogeneous⟩⟩

instance : Inf (HomogeneousSubmodule A ℳ) :=
  ⟨fun I J => ⟨_, I.isHomogeneous.inf J.isHomogeneous⟩⟩

set_option synthInstance.checkSynthOrder false in
instance SupSet : SupSet (HomogeneousSubmodule A ℳ) :=
  ⟨fun S => ⟨⨆ s ∈ S, toSubmodule s, Submodule.IsHomogeneous.iSup₂ (𝒜 := 𝒜) fun s _ => s.isHomogeneous⟩⟩

instance : InfSet (HomogeneousSubmodule A ℳ) :=
  ⟨fun S => ⟨⨅ s ∈ S, toSubmodule s, Submodule.IsHomogeneous.iInf₂ fun s _ => s.isHomogeneous⟩⟩

@[simp]
theorem coe_top : ((⊤ : HomogeneousSubmodule A ℳ) : Set M) = univ :=
  rfl
#align homogeneous_ideal.coe_top HomogeneousSubmodule.coe_top

@[simp]
theorem coe_bot : ((⊥ : HomogeneousSubmodule A ℳ) : Set M) = 0 :=
  rfl
#align homogeneous_ideal.coe_bot HomogeneousSubmodule.coe_bot

@[simp]
theorem coe_sup (I J : HomogeneousSubmodule A ℳ) : ↑(I ⊔ J) = (I + J : Set M) :=
  Submodule.coe_sup _ _
#align homogeneous_ideal.coe_sup HomogeneousSubmodule.coe_sup

@[simp]
theorem coe_inf (I J : HomogeneousSubmodule A ℳ) : (↑(I ⊓ J) : Set M) = ↑I ∩ ↑J :=
  rfl
#align homogeneous_ideal.coe_inf HomogeneousSubmodule.coe_inf

@[simp]
theorem toSubmodule_top : (⊤ : HomogeneousSubmodule A ℳ).toSubmodule = (⊤ : Submodule A M) :=
  rfl
#align homogeneous_ideal.to_ideal_top HomogeneousSubmodule.toSubmodule_top

@[simp]
theorem toSubmodule_bot : (⊥ : HomogeneousSubmodule A ℳ).toSubmodule = (⊥ : Submodule A M) :=
  rfl
#align homogeneous_ideal.to_ideal_bot HomogeneousSubmodule.toSubmodule_bot

@[simp]
theorem toSubmodule_sup (I J : HomogeneousSubmodule A ℳ) : (I ⊔ J).toSubmodule = I.toSubmodule ⊔ J.toSubmodule :=
  rfl
#align homogeneous_ideal.to_ideal_sup HomogeneousSubmodule.toSubmodule_sup

@[simp]
theorem toSubmodule_inf (I J : HomogeneousSubmodule A ℳ) : (I ⊓ J).toSubmodule = I.toSubmodule ⊓ J.toSubmodule :=
  rfl
#align homogeneous_ideal.to_ideal_inf HomogeneousSubmodule.toSubmodule_inf

@[simp]
theorem toSubmodule_sSup (ℐ : Set (HomogeneousSubmodule A ℳ)) : (sSup ℐ).toSubmodule = ⨆ s ∈ ℐ, toSubmodule s :=
  rfl
#align homogeneous_ideal.to_ideal_Sup HomogeneousSubmodule.toSubmodule_sSup

@[simp]
theorem toSubmodule_sInf (ℐ : Set (HomogeneousSubmodule A ℳ)) : (sInf ℐ).toSubmodule = ⨅ s ∈ ℐ, toSubmodule s :=
  rfl
#align homogeneous_ideal.to_ideal_Inf HomogeneousSubmodule.toSubmodule_sInf

@[simp]
theorem toSubmodule_iSup {κ : Sort*} (s : κ → HomogeneousSubmodule A ℳ) :
    (⨆ i, s i).toSubmodule = ⨆ i, (s i).toSubmodule := by
  rw [iSup, toSubmodule_sSup, iSup_range]
#align homogeneous_ideal.to_ideal_supr HomogeneousSubmodule.toSubmodule_iSup

@[simp]
theorem toSubmodule_iInf {κ : Sort*} (s : κ → HomogeneousSubmodule A ℳ) :
    (⨅ i, s i).toSubmodule = ⨅ i, (s i).toSubmodule := by
  rw [iInf, toSubmodule_sInf, iInf_range]
#align homogeneous_ideal.to_ideal_infi HomogeneousSubmodule.toSubmodule_iInf

-- @[simp] -- Porting note: simp can prove this
theorem toSubmodule_iSup₂ {κ : Sort*} {κ' : κ → Sort*} (s : ∀ i, κ' i → HomogeneousSubmodule A ℳ) :
    (⨆ (i) (j), s i j).toSubmodule = ⨆ (i) (j), (s i j).toSubmodule := by
  simp_rw [toSubmodule_iSup]
#align homogeneous_ideal.to_ideal_supr₂ HomogeneousSubmodule.toSubmodule_iSup₂

-- @[simp] -- Porting note: simp can prove this
theorem toSubmodule_iInf₂ {κ : Sort*} {κ' : κ → Sort*} (s : ∀ i, κ' i → HomogeneousSubmodule A ℳ) :
    (⨅ (i) (j), s i j).toSubmodule = ⨅ (i) (j), (s i j).toSubmodule := by
  simp_rw [toSubmodule_iInf]
#align homogeneous_ideal.to_ideal_infi₂ HomogeneousSubmodule.toSubmodule_iInf₂

@[simp]
theorem eq_top_iff (I : HomogeneousSubmodule A ℳ) : I = ⊤ ↔ I.toSubmodule = ⊤ :=
  toSubmodule_injective.eq_iff.symm
#align homogeneous_ideal.eq_top_iff HomogeneousSubmodule.eq_top_iff

@[simp]
theorem eq_bot_iff (I : HomogeneousSubmodule A ℳ) : I = ⊥ ↔ I.toSubmodule = ⊥ :=
  toSubmodule_injective.eq_iff.symm
#align homogeneous_ideal.eq_bot_iff HomogeneousSubmodule.eq_bot_iff

set_option synthInstance.checkSynthOrder false in
instance completeLattice : CompleteLattice (HomogeneousSubmodule A ℳ) :=
  toSubmodule_injective.completeLattice _ toSubmodule_sup toSubmodule_inf toSubmodule_sSup toSubmodule_sInf toSubmodule_top
    toSubmodule_bot

set_option synthInstance.checkSynthOrder false in
instance : Add (HomogeneousSubmodule A ℳ) :=
  ⟨(· ⊔ ·)⟩

@[simp]
theorem toSubmodule_add (I J : HomogeneousSubmodule A ℳ) : (I + J).toSubmodule = I.toSubmodule + J.toSubmodule :=
  rfl
#align homogeneous_ideal.to_ideal_add HomogeneousSubmodule.toSubmodule_add

instance : Inhabited (HomogeneousSubmodule A ℳ) where default := ⊥

end HomogeneousSubmodule

end Semiring

section CommSemiring

variable {𝒜}

variable [CommSemiring A] [Module A M]

variable [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]

variable (I : Submodule A M)

-- In general, submodules cannot be multiplied, so this lemma is not generalized
theorem Ideal.IsHomogeneous.mul {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I * J).IsHomogeneous 𝒜 := by
  rw [Ideal.IsHomogeneous.iff_exists 𝒜] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  rw [Ideal.span_mul_span']
  exact ⟨s₁ * s₂, congr_arg _ <| (Set.image_mul (homogeneousSubmonoid 𝒜).subtype).symm⟩
#align ideal.is_homogeneous.mul Ideal.IsHomogeneous.mul

instance : Mul (HomogeneousIdeal 𝒜) where
  mul I J := ⟨I.toIdeal * J.toIdeal, Ideal.IsHomogeneous.mul I.isHomogeneous J.isHomogeneous⟩

@[simp]
theorem HomogeneousIdeal.toIdeal_mul (I J : HomogeneousIdeal 𝒜) :
    (I * J).toIdeal = I.toIdeal * J.toIdeal :=
  rfl
#align homogeneous_ideal.to_ideal_mul HomogeneousIdeal.toIdeal_mul

end CommSemiring

end Operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/


section homogeneousCore

open HomogeneousSubmodule

variable [Semiring A] [Module A M]

variable [AddMonoid ιA]
variable [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [VAdd ιA ιM] [Decomposition ℳ] [GradedSMul 𝒜 ℳ]

variable (I : Ideal A) (p : Submodule A M)

theorem Submodule.homogeneousCore.gc : GaloisConnection toSubmodule (Submodule.homogeneousCore 𝒜 ℳ) := fun I _ =>
  ⟨fun H => I.toSubmodule_homogeneousCore_eq_self (𝒜 := 𝒜) ▸ Submodule.homogeneousCore_mono 𝒜 ℳ H,
    fun H => le_trans H (Submodule.homogeneousCore'_le _ _)⟩
#align ideal.homogeneous_core.gc Submodule.homogeneousCore.gc

/-- `toSubmodule : HomogeneousSubmodule A ℳ → Ideal A` and `Ideal.homogeneousCore 𝒜` forms a galois
coinsertion. -/
def Submodule.homogeneousCore.gi : GaloisCoinsertion toSubmodule (Submodule.homogeneousCore 𝒜 ℳ) where
  choice I HI :=
    ⟨I, le_antisymm (I.toSubmodule_homogeneousCore_le 𝒜 ℳ) HI ▸ HomogeneousSubmodule.isHomogeneous _⟩
  gc := Submodule.homogeneousCore.gc 𝒜 ℳ
  u_l_le _ := Submodule.homogeneousCore'_le _ _
  choice_eq I H := le_antisymm H (I.toSubmodule_homogeneousCore_le _ _)
#align ideal.homogeneous_core.gi Submodule.homogeneousCore.gi

-- set_option synthInstance.maxHeartbeats 40000 in
theorem Submodule.homogeneousCore_eq_sSup :
    letI _ : CompleteLattice (HomogeneousSubmodule A ℳ) :=
      HomogeneousSubmodule.completeLattice (𝒜 := 𝒜)
    letI _ : SupSet (HomogeneousSubmodule A ℳ) :=
      HomogeneousSubmodule.SupSet (𝒜 := 𝒜)
    p.homogeneousCore 𝒜 ℳ = sSup { q : HomogeneousSubmodule A ℳ | q.toSubmodule ≤ p } :=
  letI _ : CompleteLattice (HomogeneousSubmodule A ℳ) :=
      HomogeneousSubmodule.completeLattice (𝒜 := 𝒜)
  letI _ : SupSet (HomogeneousSubmodule A ℳ) :=
    HomogeneousSubmodule.SupSet (𝒜 := 𝒜)
  Eq.symm <| IsLUB.sSup_eq <| (Submodule.homogeneousCore.gc 𝒜 ℳ).isGreatest_u.isLUB
#align ideal.homogeneous_core_eq_Sup Submodule.homogeneousCore_eq_sSup

theorem Submodule.homogeneousCore'_eq_sSup :
    p.homogeneousCore' ℳ = sSup { q : Submodule A M | q.IsHomogeneous ℳ ∧ q ≤ p } := by
  refine' (IsLUB.sSup_eq _).symm
  apply IsGreatest.isLUB
  have coe_mono : Monotone (toSubmodule : HomogeneousSubmodule A ℳ → Submodule A M) := fun x y => id
  convert coe_mono.map_isGreatest (Submodule.homogeneousCore.gc 𝒜 ℳ).isGreatest_u using 1
  ext x
  rw [mem_image, mem_setOf_eq]
  refine' ⟨fun hI => ⟨⟨x, hI.1⟩, ⟨hI.2, rfl⟩⟩, _⟩
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact ⟨x.isHomogeneous, hx⟩
#align ideal.homogeneous_core'_eq_Sup Submodule.homogeneousCore'_eq_sSup

end homogeneousCore

/-! ### Homogeneous hulls -/


section HomogeneousHull

open HomogeneousSubmodule

variable [Semiring A] [Module A M] [DecidableEq ιA] [AddMonoid ιA]
variable [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜] [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

variable (I : Ideal A) (p : Submodule A M)

/-- For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousHull 𝒜` is
the smallest homogeneous ideal containing `I`. -/
def Submodule.homogeneousHull : HomogeneousSubmodule A ℳ :=
  ⟨Submodule.span A { r : M | ∃ (i : ιM) (x : p), (DirectSum.decompose ℳ (x : M) i : M) = r }, by
    refine' Submodule.homogeneous_span 𝒜 ℳ _ fun x hx => _
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.homogeneous_coe⟩
#align ideal.homogeneous_hull Submodule.homogeneousHull

theorem Submodule.le_toSubmodule_homogeneousHull : p ≤ (Submodule.homogeneousHull 𝒜 ℳ p).toSubmodule := by
  intro r hr
  classical
  rw [← DirectSum.sum_support_decompose ℳ r]
  refine' Submodule.sum_mem _ _
  intro j _
  apply Submodule.subset_span
  use j
  use ⟨r, hr⟩
#align ideal.le_to_ideal_homogeneous_hull Submodule.le_toSubmodule_homogeneousHull

theorem Submodule.homogeneousHull_mono : Monotone (Submodule.homogeneousHull 𝒜 ℳ) := fun I J I_le_J => by
  apply Submodule.span_mono
  rintro r ⟨hr1, ⟨x, hx⟩, rfl⟩
  refine' ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩
#align ideal.homogeneous_hull_mono Submodule.homogeneousHull_mono

variable {I ℳ}

theorem Submodule.IsHomogeneous.toSubmodule_homogeneousHull_eq_self (h : p.IsHomogeneous ℳ) :
    (Submodule.homogeneousHull 𝒜 ℳ p).toSubmodule = p := by
  apply le_antisymm _ (Submodule.le_toSubmodule_homogeneousHull _ _ _)
  apply Submodule.span_le.2
  rintro _ ⟨i, x, rfl⟩
  exact h _ x.prop
#align ideal.is_homogeneous.to_ideal_homogeneous_hull_eq_self Submodule.IsHomogeneous.toSubmodule_homogeneousHull_eq_self

@[simp]
theorem HomogeneousSubmodule.homogeneousHull_toSubmodule_eq_self (I : HomogeneousSubmodule A ℳ) :
    I.toSubmodule.homogeneousHull 𝒜 ℳ = I :=
  HomogeneousSubmodule.toSubmodule_injective <| I.isHomogeneous.toSubmodule_homogeneousHull_eq_self 𝒜
#align homogeneous_ideal.homogeneous_hull_to_ideal_eq_self HomogeneousSubmodule.homogeneousHull_toSubmodule_eq_self

variable (I)

theorem Submodule.toSubmodule_homogeneousHull_eq_iSup :
    (p.homogeneousHull 𝒜 ℳ).toSubmodule = ⨆ i, Submodule.span A (GradedModule.proj ℳ i '' p) := by
  rw [← Submodule.span_iUnion]
  apply congr_arg (Submodule.span A ·) _
  aesop
#align ideal.to_ideal_homogeneous_hull_eq_supr Submodule.toSubmodule_homogeneousHull_eq_iSup

theorem Submodule.homogeneousHull_eq_iSup :
    p.homogeneousHull 𝒜 ℳ =
      ⨆ i, ⟨Submodule.span A (GradedModule.proj ℳ i '' p), Submodule.homogeneous_span 𝒜 ℳ _ (by
        rintro _ ⟨x, -, rfl⟩
        apply SetLike.homogeneous_coe)⟩ := by
  ext1
  rw [Submodule.toSubmodule_homogeneousHull_eq_iSup, toSubmodule_iSup]
#align ideal.homogeneous_hull_eq_supr Submodule.homogeneousHull_eq_iSup

end HomogeneousHull

section GaloisConnection

open HomogeneousSubmodule

variable [Semiring A] [Module A M] [DecidableEq ιA] [AddMonoid ιA]

variable [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜] [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

theorem Submodule.homogeneousHull.gc : GaloisConnection (Submodule.homogeneousHull 𝒜 ℳ) toSubmodule := fun _ J =>
  ⟨le_trans (Submodule.le_toSubmodule_homogeneousHull _ _ _),
    fun H => J.homogeneousHull_toSubmodule_eq_self 𝒜 ▸ Submodule.homogeneousHull_mono 𝒜 ℳ H⟩
#align ideal.homogeneous_hull.gc Submodule.homogeneousHull.gc

/-- `Ideal.homogeneousHull 𝒜` and `toSubmodule : HomogeneousSubmodule A ℳ → Ideal A` form a galois
insertion. -/
def Submodule.homogeneousHull.gi : GaloisInsertion (Submodule.homogeneousHull 𝒜 ℳ) toSubmodule where
  choice I H := ⟨I, le_antisymm H (I.le_toSubmodule_homogeneousHull 𝒜 ℳ) ▸ isHomogeneous _⟩
  gc := Submodule.homogeneousHull.gc 𝒜 ℳ
  le_l_u _ := Submodule.le_toSubmodule_homogeneousHull 𝒜 _ _
  choice_eq I H := le_antisymm (I.le_toSubmodule_homogeneousHull 𝒜 ℳ) H
#align ideal.homogeneous_hull.gi Submodule.homogeneousHull.gi

theorem Submodule.homogeneousHull_eq_sInf (I : Submodule A M) :
    I.homogeneousHull 𝒜 ℳ = sInf { J : HomogeneousSubmodule A ℳ | I ≤ J.toSubmodule } :=
  Eq.symm <| IsGLB.sInf_eq <| (Submodule.homogeneousHull.gc 𝒜 ℳ).isLeast_l.isGLB
#align ideal.homogeneous_hull_eq_Inf Submodule.homogeneousHull_eq_sInf

end GaloisConnection

section IrrelevantIdeal

variable [Semiring A]

variable [CanonicallyOrderedAddCommMonoid ιA]

variable [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]

open GradedRing SetLike.GradedMonoid DirectSum

/-- For a graded ring `⨁ᵢ 𝒜ᵢ` graded by a `CanonicallyOrderedAddCommMonoid ι`, the irrelevant ideal
refers to `⨁_{i>0} 𝒜ᵢ`, or equivalently `{a | a₀ = 0}`. This definition is used in `Proj`
construction where `ι` is always `ℕ` so the irrelevant ideal is simply elements with `0` as
0-th coordinate.

# Future work
Here in the definition, `ι` is assumed to be `CanonicallyOrderedAddCommMonoid`. However, the notion
of irrelevant ideal makes sense in a more general setting by defining it as the ideal of elements
with `0` as i-th coordinate for all `i ≤ 0`, i.e. `{a | ∀ (i : ι), i ≤ 0 → aᵢ = 0}`.
-/
def HomogeneousIdeal.irrelevant : HomogeneousIdeal 𝒜 :=
  ⟨RingHom.ker (GradedRing.projZeroRingHom 𝒜), fun i r (hr : (decompose 𝒜 r 0 : A) = 0) => by
    change (decompose 𝒜 (decompose 𝒜 r _ : A) 0 : A) = 0
    by_cases h : i = 0
    · rw [h, hr, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
    · rw [decompose_of_mem_ne 𝒜 (SetLike.coe_mem _) h]⟩
#align homogeneous_ideal.irrelevant HomogeneousIdeal.irrelevant

@[simp]
theorem HomogeneousIdeal.mem_irrelevant_iff (a : A) :
    a ∈ HomogeneousIdeal.irrelevant 𝒜 ↔ proj 𝒜 0 a = 0 :=
  Iff.rfl
#align homogeneous_ideal.mem_irrelevant_iff HomogeneousIdeal.mem_irrelevant_iff

@[simp]
theorem HomogeneousIdeal.toIdeal_irrelevant :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal = RingHom.ker (GradedRing.projZeroRingHom 𝒜) :=
  rfl
#align homogeneous_ideal.to_ideal_irrelevant HomogeneousIdeal.toIdeal_irrelevant

end IrrelevantIdeal
