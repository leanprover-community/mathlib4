/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule

/-!
# Homogeneous ideals of a graded algebra

This file defines homogeneous ideals of `GradedRing 𝒜` where `𝒜 : ι → Submodule R A` and
operations on them.

## Main definitions

For any `I : Ideal A`:
* `Ideal.IsHomogeneous 𝒜 I`: The property that an ideal is closed under `GradedRing.proj`.
* `HomogeneousIdeal 𝒜`: The structure extending ideals which satisfy `Ideal.IsHomogeneous`.
* `Ideal.homogeneousCore I 𝒜`: The largest homogeneous ideal smaller than `I`.
* `Ideal.homogeneousHull I 𝒜`: The smallest homogeneous ideal larger than `I`.

## Main statements

* `HomogeneousIdeal.completeLattice`: `Ideal.IsHomogeneous` is preserved by `⊥`, `⊤`, `⊔`, `⊓`,
  `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `Ideal.homogeneousCore.gi`: `Ideal.homogeneousCore` forms a Galois insertion with coercion.
* `Ideal.homogeneousHull.gi`: `Ideal.homogeneousHull` forms a Galois insertion with coercion.

## Implementation notes

We introduce `Ideal.homogeneousCore'` earlier than might be expected so that we can get access
to `Ideal.IsHomogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/

@[expose] public section


open SetLike DirectSum Set

open Pointwise DirectSum

variable {ι σ A : Type*}

section HomogeneousDef

variable [Semiring A]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]
variable (I : Ideal A)

/-- An `I : Ideal A` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`. -/
abbrev Ideal.IsHomogeneous : Prop := Submodule.IsHomogeneous I 𝒜

theorem Ideal.IsHomogeneous.mem_iff {I} (hI : Ideal.IsHomogeneous 𝒜 I) {x} :
    x ∈ I ↔ ∀ i, (decompose 𝒜 x i : A) ∈ I :=
  AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hI

/-- For any `Semiring A`, we collect the homogeneous ideals of `A` into a type. -/
abbrev HomogeneousIdeal := HomogeneousSubmodule 𝒜 𝒜

variable {𝒜}

/-- Converting a homogeneous ideal to an ideal. -/
abbrev HomogeneousIdeal.toIdeal (I : HomogeneousIdeal 𝒜) : Ideal A :=
  I.toSubmodule

theorem HomogeneousIdeal.span_isHomogeneousElem_eq (I : HomogeneousIdeal 𝒜) :
    Ideal.span { x | x ∈ I ∧ SetLike.IsHomogeneousElem 𝒜 x } = I.toIdeal :=
  le_antisymm (Ideal.span_le.mpr fun _ h ↦ h.1) <|
    (I.2.closure_isHomogeneousElem 𝒜).symm.trans_le <|
      AddSubmonoid.closure_le.mpr Ideal.subset_span

theorem HomogeneousIdeal.isHomogeneous (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.IsHomogeneous 𝒜 := I.is_homogeneous'

theorem HomogeneousIdeal.toIdeal_injective :
    Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 → Ideal A) :=
  HomogeneousSubmodule.toSubmodule_injective 𝒜 𝒜

instance HomogeneousIdeal.setLike : SetLike (HomogeneousIdeal 𝒜) A :=
  HomogeneousSubmodule.setLike 𝒜 𝒜

@[ext]
theorem HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h : I.toIdeal = J.toIdeal) : I = J :=
  HomogeneousIdeal.toIdeal_injective h

theorem HomogeneousIdeal.ext' {I J : HomogeneousIdeal 𝒜} (h : ∀ i, ∀ x ∈ 𝒜 i, x ∈ I ↔ x ∈ J) :
    I = J := HomogeneousSubmodule.ext' 𝒜 𝒜 h

@[simp high]
theorem HomogeneousIdeal.mem_iff {I : HomogeneousIdeal 𝒜} {x : A} : x ∈ I.toIdeal ↔ x ∈ I :=
  Iff.rfl

end HomogeneousDef

section HomogeneousCore

variable [Semiring A]
variable [SetLike σ A] (𝒜 : ι → σ)
variable (I : Ideal A)

/-- For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousCore' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal. -/
def Ideal.homogeneousCore' (I : Ideal A) : Ideal A :=
  Ideal.span ((↑) '' (((↑) : Subtype (SetLike.IsHomogeneousElem 𝒜) → A) ⁻¹' I))

theorem Ideal.homogeneousCore'_mono : Monotone (Ideal.homogeneousCore' 𝒜) :=
  fun _ _ I_le_J => Ideal.span_mono <| Set.image_mono fun _ => @I_le_J _

theorem Ideal.homogeneousCore'_le : I.homogeneousCore' 𝒜 ≤ I :=
  Ideal.span_le.2 <| image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousIdealDefs

variable [Semiring A]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]
variable (I : Ideal A)

theorem Ideal.isHomogeneous_iff_forall_subset :
    I.IsHomogeneous 𝒜 ↔ ∀ i, (I : Set A) ⊆ GradedRing.proj 𝒜 i ⁻¹' I :=
  Iff.rfl

theorem Ideal.isHomogeneous_iff_subset_iInter :
    I.IsHomogeneous 𝒜 ↔ (I : Set A) ⊆ ⋂ i, GradedRing.proj 𝒜 i ⁻¹' ↑I :=
  subset_iInter_iff.symm

theorem Ideal.mul_homogeneous_element_mem_of_mem
    {I : Ideal A} (r x : A) (hx₁ : SetLike.IsHomogeneousElem 𝒜 x)
    (hx₂ : x ∈ I) (j : ι) : GradedRing.proj 𝒜 j (r * x) ∈ I := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_mul, map_sum]
  apply Ideal.sum_mem
  intro k _
  obtain ⟨i, hi⟩ := hx₁
  have mem₁ : (DirectSum.decompose 𝒜 r k : A) * x ∈ 𝒜 (k + i) :=
    GradedMul.mul_mem (SetLike.coe_mem _) hi
  rw [GradedRing.proj_apply, DirectSum.decompose_of_mem 𝒜 mem₁, coe_of_apply]
  split_ifs
  · exact I.mul_mem_left _ hx₂
  · exact I.zero_mem

theorem Ideal.homogeneous_span (s : Set A) (h : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x) :
    (Ideal.span s).IsHomogeneous 𝒜 := by
  rintro i r hr
  rw [Ideal.span, Finsupp.span_eq_range_linearCombination] at hr
  rw [LinearMap.mem_range] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [Finsupp.linearCombination_apply, Finsupp.sum, decompose_sum, DFinsupp.finset_sum_apply,
    AddSubmonoidClass.coe_finset_sum]
  refine Ideal.sum_mem _ ?_
  rintro z hz1
  rw [smul_eq_mul]
  refine Ideal.mul_homogeneous_element_mem_of_mem 𝒜 (s z) z ?_ ?_ i
  · rcases z with ⟨z, hz2⟩
    apply h _ hz2
  · exact Ideal.subset_span z.2

/-- For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousCore' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`. -/
def Ideal.homogeneousCore : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.homogeneousCore' 𝒜 I,
    Ideal.homogeneous_span _ _ fun _ h => by
      have := Subtype.image_preimage_coe (setOf (SetLike.IsHomogeneousElem 𝒜)) (I : Set A)
      exact (cast congr(_ ∈ $this) h).1⟩

theorem Ideal.homogeneousCore_mono : Monotone (Ideal.homogeneousCore 𝒜) :=
  Ideal.homogeneousCore'_mono 𝒜

theorem Ideal.toIdeal_homogeneousCore_le : (I.homogeneousCore 𝒜).toIdeal ≤ I :=
  Ideal.homogeneousCore'_le 𝒜 I

variable {𝒜 I}

theorem Ideal.mem_homogeneousCore_of_homogeneous_of_mem {x : A} (h : SetLike.IsHomogeneousElem 𝒜 x)
    (hmem : x ∈ I) : x ∈ I.homogeneousCore 𝒜 :=
  Ideal.subset_span ⟨⟨x, h⟩, hmem, rfl⟩

theorem Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self (h : I.IsHomogeneous 𝒜) :
    (I.homogeneousCore 𝒜).toIdeal = I := by
  apply le_antisymm (I.homogeneousCore'_le 𝒜) _
  intro x hx
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Ideal.sum_mem _ fun j _ => Ideal.subset_span ⟨⟨_, isHomogeneousElem_coe _⟩, h _ hx, rfl⟩

@[simp]
theorem HomogeneousIdeal.toIdeal_homogeneousCore_eq_self (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.homogeneousCore 𝒜 = I := by
  ext1
  convert Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self I.isHomogeneous

variable (𝒜 I)

theorem Ideal.IsHomogeneous.iff_eq : I.IsHomogeneous 𝒜 ↔ (I.homogeneousCore 𝒜).toIdeal = I :=
  ⟨fun hI => hI.toIdeal_homogeneousCore_eq_self, fun hI => hI ▸ (Ideal.homogeneousCore 𝒜 I).2⟩

theorem Ideal.IsHomogeneous.iff_exists :
    I.IsHomogeneous 𝒜 ↔ ∃ S : Set (homogeneousSubmonoid 𝒜), I = Ideal.span ((↑) '' S) := by
  rw [Ideal.IsHomogeneous.iff_eq, eq_comm]
  exact ((Set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm

end IsHomogeneousIdealDefs

/-! ### Operations

In this section, we show that `Ideal.IsHomogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `HomogeneousIdeal`. -/


section Operations

section Semiring

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

namespace Ideal.IsHomogeneous

theorem bot : Ideal.IsHomogeneous 𝒜 ⊥ := fun i r hr => by
  simp only [Ideal.mem_bot] at hr
  rw [hr, decompose_zero, zero_apply]
  apply Ideal.zero_mem

theorem top : Ideal.IsHomogeneous 𝒜 ⊤ := fun i r _ => by simp only [Submodule.mem_top]

variable {𝒜}

theorem inf {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I ⊓ J).IsHomogeneous 𝒜 :=
  fun _ _ hr => ⟨HI _ hr.1, HJ _ hr.2⟩

theorem sup {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I ⊔ J).IsHomogeneous 𝒜 := by
  rw [iff_exists] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  refine ⟨s₁ ∪ s₂, ?_⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm

protected theorem iSup {κ : Sort*} {f : κ → Ideal A} (h : ∀ i, (f i).IsHomogeneous 𝒜) :
    (⨆ i, f i).IsHomogeneous 𝒜 := by
  simp_rw [iff_exists] at h ⊢
  choose s hs using h
  refine ⟨⋃ i, s i, ?_⟩
  simp_rw [Set.image_iUnion, Ideal.span_iUnion]
  congr
  exact funext hs

protected theorem iInf {κ : Sort*} {f : κ → Ideal A} (h : ∀ i, (f i).IsHomogeneous 𝒜) :
    (⨅ i, f i).IsHomogeneous 𝒜 := by
  intro i x hx
  simp only [Ideal.mem_iInf] at hx ⊢
  exact fun j => h _ _ (hx j)

theorem iSup₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Ideal A}
    (h : ∀ i j, (f i j).IsHomogeneous 𝒜) : (⨆ (i) (j), f i j).IsHomogeneous 𝒜 :=
  IsHomogeneous.iSup fun i => IsHomogeneous.iSup <| h i

theorem iInf₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Ideal A}
    (h : ∀ i j, (f i j).IsHomogeneous 𝒜) : (⨅ (i) (j), f i j).IsHomogeneous 𝒜 :=
  IsHomogeneous.iInf fun i => IsHomogeneous.iInf <| h i

theorem sSup {ℐ : Set (Ideal A)} (h : ∀ I ∈ ℐ, Ideal.IsHomogeneous 𝒜 I) :
    (sSup ℐ).IsHomogeneous 𝒜 := by
  rw [sSup_eq_iSup]
  exact iSup₂ h

theorem sInf {ℐ : Set (Ideal A)} (h : ∀ I ∈ ℐ, Ideal.IsHomogeneous 𝒜 I) :
    (sInf ℐ).IsHomogeneous 𝒜 := by
  rw [sInf_eq_iInf]
  exact iInf₂ h

end Ideal.IsHomogeneous

variable {𝒜}

namespace HomogeneousIdeal

instance : PartialOrder (HomogeneousIdeal 𝒜) :=
  SetLike.instPartialOrder

instance : Top (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊤, Ideal.IsHomogeneous.top 𝒜⟩⟩

instance : Bot (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊥, Ideal.IsHomogeneous.bot 𝒜⟩⟩

instance : Max (HomogeneousIdeal 𝒜) :=
  ⟨fun I J => ⟨_, I.isHomogeneous.sup J.isHomogeneous⟩⟩

instance : Min (HomogeneousIdeal 𝒜) :=
  ⟨fun I J => ⟨_, I.isHomogeneous.inf J.isHomogeneous⟩⟩

instance : SupSet (HomogeneousIdeal 𝒜) :=
  ⟨fun S => ⟨⨆ s ∈ S, toIdeal s, Ideal.IsHomogeneous.iSup₂ fun s _ => s.isHomogeneous⟩⟩

instance : InfSet (HomogeneousIdeal 𝒜) :=
  ⟨fun S => ⟨⨅ s ∈ S, toIdeal s, Ideal.IsHomogeneous.iInf₂ fun s _ => s.isHomogeneous⟩⟩

@[simp]
theorem coe_top : ((⊤ : HomogeneousIdeal 𝒜) : Set A) = univ :=
  rfl

@[simp]
theorem coe_bot : ((⊥ : HomogeneousIdeal 𝒜) : Set A) = 0 :=
  rfl

@[simp]
theorem coe_sup (I J : HomogeneousIdeal 𝒜) : ↑(I ⊔ J) = (I + J : Set A) :=
  Submodule.coe_sup _ _

@[simp]
theorem coe_inf (I J : HomogeneousIdeal 𝒜) : (↑(I ⊓ J) : Set A) = ↑I ∩ ↑J :=
  rfl

@[simp]
theorem toIdeal_top : (⊤ : HomogeneousIdeal 𝒜).toIdeal = (⊤ : Ideal A) :=
  rfl

@[simp]
theorem toIdeal_bot : (⊥ : HomogeneousIdeal 𝒜).toIdeal = (⊥ : Ideal A) :=
  rfl

@[simp]
theorem toIdeal_sup (I J : HomogeneousIdeal 𝒜) : (I ⊔ J).toIdeal = I.toIdeal ⊔ J.toIdeal :=
  rfl

@[simp]
theorem toIdeal_inf (I J : HomogeneousIdeal 𝒜) : (I ⊓ J).toIdeal = I.toIdeal ⊓ J.toIdeal :=
  rfl

@[simp]
theorem toIdeal_sSup (ℐ : Set (HomogeneousIdeal 𝒜)) : (sSup ℐ).toIdeal = ⨆ s ∈ ℐ, toIdeal s :=
  rfl

@[simp]
theorem toIdeal_sInf (ℐ : Set (HomogeneousIdeal 𝒜)) : (sInf ℐ).toIdeal = ⨅ s ∈ ℐ, toIdeal s :=
  rfl

@[simp]
theorem toIdeal_iSup {κ : Sort*} (s : κ → HomogeneousIdeal 𝒜) :
    (⨆ i, s i).toIdeal = ⨆ i, (s i).toIdeal := by
  rw [iSup, toIdeal_sSup, iSup_range]

@[simp]
theorem toIdeal_iInf {κ : Sort*} (s : κ → HomogeneousIdeal 𝒜) :
    (⨅ i, s i).toIdeal = ⨅ i, (s i).toIdeal := by
  rw [iInf, toIdeal_sInf, iInf_range]

theorem toIdeal_iSup₂ {κ : Sort*} {κ' : κ → Sort*} (s : ∀ i, κ' i → HomogeneousIdeal 𝒜) :
    (⨆ (i) (j), s i j).toIdeal = ⨆ (i) (j), (s i j).toIdeal := by
  simp_rw [toIdeal_iSup]

theorem toIdeal_iInf₂ {κ : Sort*} {κ' : κ → Sort*} (s : ∀ i, κ' i → HomogeneousIdeal 𝒜) :
    (⨅ (i) (j), s i j).toIdeal = ⨅ (i) (j), (s i j).toIdeal := by
  simp_rw [toIdeal_iInf]

@[simp]
theorem eq_top_iff (I : HomogeneousIdeal 𝒜) : I = ⊤ ↔ I.toIdeal = ⊤ :=
  toIdeal_injective.eq_iff.symm

@[simp]
theorem eq_bot_iff (I : HomogeneousIdeal 𝒜) : I = ⊥ ↔ I.toIdeal = ⊥ :=
  toIdeal_injective.eq_iff.symm

instance completeLattice : CompleteLattice (HomogeneousIdeal 𝒜) :=
  toIdeal_injective.completeLattice _ toIdeal_sup toIdeal_inf toIdeal_sSup toIdeal_sInf toIdeal_top
    toIdeal_bot

instance : Add (HomogeneousIdeal 𝒜) :=
  ⟨(· ⊔ ·)⟩

@[simp]
theorem toIdeal_add (I J : HomogeneousIdeal 𝒜) : (I + J).toIdeal = I.toIdeal + J.toIdeal :=
  rfl

instance : Inhabited (HomogeneousIdeal 𝒜) where default := ⊥

end HomogeneousIdeal

end Semiring

section CommSemiring

variable [CommSemiring A]
variable [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜]
variable (I : Ideal A)

theorem Ideal.IsHomogeneous.mul {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I * J).IsHomogeneous 𝒜 := by
  rw [Ideal.IsHomogeneous.iff_exists] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  rw [Ideal.span_mul_span']
  exact ⟨s₁ * s₂, congr_arg _ <| (Set.image_mul (homogeneousSubmonoid 𝒜).subtype).symm⟩

instance : Mul (HomogeneousIdeal 𝒜) where
  mul I J := ⟨I.toIdeal * J.toIdeal, I.isHomogeneous.mul J.isHomogeneous⟩

@[simp]
theorem HomogeneousIdeal.toIdeal_mul (I J : HomogeneousIdeal 𝒜) :
    (I * J).toIdeal = I.toIdeal * J.toIdeal :=
  rfl

end CommSemiring

end Operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/


section homogeneousCore

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable (I : Ideal A)

theorem Ideal.homogeneousCore.gc : GaloisConnection toIdeal (Ideal.homogeneousCore 𝒜) := fun I _ =>
  ⟨fun H => I.toIdeal_homogeneousCore_eq_self ▸ Ideal.homogeneousCore_mono 𝒜 H,
    fun H => le_trans H (Ideal.homogeneousCore'_le _ _)⟩

/-- `toIdeal : HomogeneousIdeal 𝒜 → Ideal A` and `Ideal.homogeneousCore 𝒜` forms a Galois
coinsertion. -/
def Ideal.homogeneousCore.gi : GaloisCoinsertion toIdeal (Ideal.homogeneousCore 𝒜) where
  choice I HI :=
    ⟨I, le_antisymm (I.toIdeal_homogeneousCore_le 𝒜) HI ▸ HomogeneousIdeal.isHomogeneous _⟩
  gc := Ideal.homogeneousCore.gc 𝒜
  u_l_le _ := Ideal.homogeneousCore'_le _ _
  choice_eq I H := le_antisymm H (I.toIdeal_homogeneousCore_le _)

theorem Ideal.homogeneousCore_eq_sSup :
    I.homogeneousCore 𝒜 = sSup { J : HomogeneousIdeal 𝒜 | J.toIdeal ≤ I } :=
  Eq.symm <| IsLUB.sSup_eq <| (Ideal.homogeneousCore.gc 𝒜).isGreatest_u.isLUB

theorem Ideal.homogeneousCore'_eq_sSup :
    I.homogeneousCore' 𝒜 = sSup { J : Ideal A | J.IsHomogeneous 𝒜 ∧ J ≤ I } := by
  refine (IsLUB.sSup_eq ?_).symm
  apply IsGreatest.isLUB
  have coe_mono : Monotone (toIdeal : HomogeneousIdeal 𝒜 → Ideal A) := fun x y => id
  convert coe_mono.map_isGreatest (Ideal.homogeneousCore.gc 𝒜).isGreatest_u using 1
  ext x
  rw [mem_image, mem_setOf_eq]
  refine ⟨fun hI => ⟨⟨x, hI.1⟩, ⟨hI.2, rfl⟩⟩, ?_⟩
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact ⟨x.isHomogeneous, hx⟩

end homogeneousCore

/-! ### Homogeneous hulls -/


section HomogeneousHull

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable (I : Ideal A)

/-- For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousHull 𝒜` is
the smallest homogeneous ideal containing `I`. -/
def Ideal.homogeneousHull : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.span { r : A | ∃ (i : ι) (x : I), (DirectSum.decompose 𝒜 (x : A) i : A) = r }, by
    refine Ideal.homogeneous_span _ _ fun x hx => ?_
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.isHomogeneousElem_coe⟩

theorem Ideal.le_toIdeal_homogeneousHull : I ≤ (Ideal.homogeneousHull 𝒜 I).toIdeal := by
  intro r hr
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r]
  refine Ideal.sum_mem _ ?_
  intro j _
  apply Ideal.subset_span
  use j
  use ⟨r, hr⟩

theorem Ideal.homogeneousHull_mono : Monotone (Ideal.homogeneousHull 𝒜) := fun I J I_le_J => by
  apply Ideal.span_mono
  rintro r ⟨hr1, ⟨x, hx⟩, rfl⟩
  exact ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩

variable {I 𝒜}

theorem Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self (h : I.IsHomogeneous 𝒜) :
    (Ideal.homogeneousHull 𝒜 I).toIdeal = I := by
  apply le_antisymm _ (Ideal.le_toIdeal_homogeneousHull _ _)
  apply Ideal.span_le.2
  rintro _ ⟨i, x, rfl⟩
  exact h _ x.prop

@[simp]
theorem HomogeneousIdeal.homogeneousHull_toIdeal_eq_self (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.homogeneousHull 𝒜 = I :=
  HomogeneousIdeal.toIdeal_injective <| I.isHomogeneous.toIdeal_homogeneousHull_eq_self

variable (I 𝒜)

theorem Ideal.toIdeal_homogeneousHull_eq_iSup :
    (I.homogeneousHull 𝒜).toIdeal = ⨆ i, Ideal.span (GradedRing.proj 𝒜 i '' I) := by
  rw [← Ideal.span_iUnion]
  apply congr_arg Ideal.span _
  ext1
  simp only [Set.mem_iUnion, Set.mem_image, mem_setOf_eq, GradedRing.proj_apply, SetLike.exists,
    exists_prop, SetLike.mem_coe]

theorem Ideal.homogeneousHull_eq_iSup :
    I.homogeneousHull 𝒜 =
      ⨆ i, ⟨Ideal.span (GradedRing.proj 𝒜 i '' I), Ideal.homogeneous_span 𝒜 _ (by
        rintro _ ⟨x, -, rfl⟩
        apply SetLike.isHomogeneousElem_coe)⟩ := by
  ext1
  rw [Ideal.toIdeal_homogeneousHull_eq_iSup, toIdeal_iSup]

end HomogeneousHull

section GaloisConnection

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

theorem Ideal.homogeneousHull.gc : GaloisConnection (Ideal.homogeneousHull 𝒜) toIdeal := fun _ J =>
  ⟨le_trans (Ideal.le_toIdeal_homogeneousHull _ _),
    fun H => J.homogeneousHull_toIdeal_eq_self ▸ Ideal.homogeneousHull_mono 𝒜 H⟩

/-- `Ideal.homogeneousHull 𝒜` and `toIdeal : HomogeneousIdeal 𝒜 → Ideal A` form a Galois
insertion. -/
def Ideal.homogeneousHull.gi : GaloisInsertion (Ideal.homogeneousHull 𝒜) toIdeal where
  choice I H := ⟨I, le_antisymm H (I.le_toIdeal_homogeneousHull 𝒜) ▸ isHomogeneous _⟩
  gc := Ideal.homogeneousHull.gc 𝒜
  le_l_u _ := Ideal.le_toIdeal_homogeneousHull _ _
  choice_eq I H := le_antisymm (I.le_toIdeal_homogeneousHull 𝒜) H

theorem Ideal.homogeneousHull_eq_sInf (I : Ideal A) :
    Ideal.homogeneousHull 𝒜 I = sInf { J : HomogeneousIdeal 𝒜 | I ≤ J.toIdeal } :=
  Eq.symm <| IsGLB.sInf_eq <| (Ideal.homogeneousHull.gc 𝒜).isLeast_l.isGLB

end GaloisConnection

section IrrelevantIdeal

namespace HomogeneousIdeal

variable [Semiring A]
variable [DecidableEq ι]
variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

open GradedRing SetLike.GradedMonoid DirectSum

/-- For a graded ring `⨁ᵢ 𝒜ᵢ` graded by a `CanonicallyOrderedAddCommMonoid ι`, the irrelevant ideal
refers to `⨁_{i>0} 𝒜ᵢ`, or equivalently `{a | a₀ = 0}`. This definition is used in `Proj`
construction where `ι` is always `ℕ` so the irrelevant ideal is simply elements with `0` as
0-th coordinate.
-/
def irrelevant : HomogeneousIdeal 𝒜 :=
  ⟨RingHom.ker (GradedRing.projZeroRingHom 𝒜), fun i r (hr : (decompose 𝒜 r 0 : A) = 0) => by
    change (decompose 𝒜 (decompose 𝒜 r _ : A) 0 : A) = 0
    by_cases h : i = 0
    · rw [h, hr, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
    · rw [decompose_of_mem_ne 𝒜 (SetLike.coe_mem _) h]⟩

local notation 𝒜"₊" => irrelevant 𝒜

@[simp]
theorem mem_irrelevant_iff (a : A) :
    a ∈ 𝒜₊ ↔ proj 𝒜 0 a = 0 :=
  Iff.rfl

@[simp]
theorem toIdeal_irrelevant :
    𝒜₊.toIdeal = RingHom.ker (GradedRing.projZeroRingHom 𝒜) :=
  rfl

lemma mem_irrelevant_of_mem {x : A} {i : ι} (hi : 0 < i) (hx : x ∈ 𝒜 i) : x ∈ 𝒜₊ := by
  rw [mem_irrelevant_iff, GradedRing.proj_apply, DirectSum.decompose_of_mem _ hx,
    DirectSum.of_eq_of_ne _ _ _ (by aesop), ZeroMemClass.coe_zero]

/-- `irrelevant 𝒜 = ⨁_{i>0} 𝒜ᵢ` -/
lemma irrelevant_eq_iSup : 𝒜₊.toAddSubmonoid = ⨆ i > 0, .ofClass (𝒜 i) := by
  refine le_antisymm (fun x hx ↦ ?_) <| iSup₂_le fun i hi x hx ↦ mem_irrelevant_of_mem _ hi hx
  classical rw [← DirectSum.sum_support_decompose 𝒜 x]
  refine sum_mem fun j hj ↦ ?_
  by_cases hj₀ : j = 0
  · classical exact (DFinsupp.mem_support_iff.mp hj <| hj₀ ▸ (by simpa using hx)).elim
  · exact AddSubmonoid.mem_iSup_of_mem j <| AddSubmonoid.mem_iSup_of_mem (pos_of_ne_zero hj₀) <|
      Subtype.prop _

open AddSubmonoid Set in
lemma irrelevant_eq_closure : 𝒜₊.toAddSubmonoid = .closure (⋃ i > 0, 𝒜 i) := by
  rw [irrelevant_eq_iSup]
  exact le_antisymm (iSup_le fun i ↦ iSup_le fun hi _ hx ↦ subset_closure <| mem_biUnion hi hx) <|
    closure_le.mpr <| iUnion_subset fun i ↦ iUnion_subset fun hi ↦ le_biSup (ofClass <| 𝒜 ·) hi

open AddSubmonoid Set in
lemma irrelevant_eq_span : 𝒜₊.toIdeal = .span (⋃ i > 0, 𝒜 i) :=
  le_antisymm ((irrelevant_eq_closure 𝒜).trans_le <| closure_le.mpr Ideal.subset_span) <|
    Ideal.span_le.mpr <| iUnion_subset fun _ ↦ iUnion_subset fun hi _ hx ↦
    mem_irrelevant_of_mem _ hi hx

lemma toAddSubmonoid_irrelevant_le {P : AddSubmonoid A} :
    𝒜₊.toAddSubmonoid ≤ P ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ P := by
  rw [irrelevant_eq_iSup, iSup₂_le_iff]

lemma toIdeal_irrelevant_le {I : Ideal A} :
    𝒜₊.toIdeal ≤ I ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ I.toAddSubmonoid :=
  toAddSubmonoid_irrelevant_le _

lemma irrelevant_le {P : HomogeneousIdeal 𝒜} :
    𝒜₊ ≤ P ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ P.toAddSubmonoid :=
  toIdeal_irrelevant_le _

end HomogeneousIdeal

end IrrelevantIdeal
