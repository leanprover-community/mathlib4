/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Module.GradedModule

/-!
# Homogeneous submodules of a graded module

This file defines homogeneous submodule of a graded module `⨁ᵢ ℳᵢ` over graded ring `⨁ᵢ 𝒜ᵢ` and
operations on them.

## Main definitions

For any `p : Submodule A M`:
* `Submodule.IsHomogeneous ℳ p`: The property that a submodule is closed under `GradedModule.proj`.
* `HomogeneousSubmodule A ℳ`: The structure extending submodules which satisfy
  `Submodule.IsHomogeneous`.
* `Submodule.homogeneousCore p 𝒜 ℳ`: The largest homogeneous submodule smaller than `p`.
* `Submodule.homogeneousHull p 𝒜 ℳ`: The smallest homogeneous ideal larger than `p`.

## Main statements

* `HomogeneousSubmodule.completeLattice`: `Submodule.IsHomogeneous` is preserved by `⊥`, `⊤`, `⊔`,
  `⊓`, `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `Submodule.homogeneousCore.gi`: `Submodule.homogeneousCore` forms a galois insertion with
  coercion.
* `Submodule.homogeneousHull.gi`: `Submodule.homogeneousHull` forms a galois insertion with
  coercion.

## Implementation notes

We introduce `Submodule.homogeneousCore'` earlier than might be expected so that we can get access
to `Submodule.IsHomogeneous.iff_exists` as quickly as possible.

The **notion** of homogeneous submodule does not rely on a graded ring, only a decomposition of the
the module. However, most interesting properties of homogeneous submodules do reply on the base ring
is a graded ring. For technical reasons, we make `HomogeneousSubmodule` depend on a graded ring.
For example, if the definition of a homogeneous submodule does not depend on a graded ring, the
instance that `HomogeneousSubmodule` is a complete lattice can not be synthesized due to
synthesation order.

## Tags

graded algebra, homogeneous
-/

open SetLike DirectSum Pointwise Set

variable {ιA ιM σA σM A M : Type*}

variable [Semiring A] [AddCommMonoid M] [Module A M]

section HomogeneousDef

/-- An `p : Submodule A M` is homogeneous if for every `m ∈ p`, all homogeneous components
  of `m` are in `I`. -/
def Submodule.IsHomogeneous (p : Submodule A M) (ℳ : ιM → σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ] : Prop :=
  ∀ (i : ιM) ⦃m : M⦄, m ∈ p → (DirectSum.decompose ℳ m i : M) ∈ p

theorem Submodule.IsHomogeneous.mem_iff {p}
    (ℳ : ιM → σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
    (hp : Submodule.IsHomogeneous (A := A) p ℳ) {x} :
    x ∈ p ↔ ∀ i, (decompose ℳ x i : M) ∈ p := by
  classical
  refine ⟨fun hx i ↦ hp i hx, fun hx ↦ ?_⟩
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact Submodule.sum_mem _ (fun i _ ↦ hx i)

/-- For any `Semiring A`, we collect the homogeneous submodule of `A`-modules into a type. -/
structure HomogeneousSubmodule (𝒜 : ιA → σA) (ℳ : ιM → σM)
    [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
    [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]
    extends Submodule A M where
  is_homogeneous' : toSubmodule.IsHomogeneous ℳ

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)
variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

variable {𝒜 ℳ} in
theorem HomogeneousSubmodule.isHomogeneous (I : HomogeneousSubmodule 𝒜 ℳ) :
    I.toSubmodule.IsHomogeneous ℳ :=
  I.is_homogeneous'

theorem HomogeneousSubmodule.toSubmodule_injective :
    Function.Injective
      (HomogeneousSubmodule.toSubmodule : HomogeneousSubmodule 𝒜 ℳ → Submodule A M) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]

instance HomogeneousSubmodule.setLike : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
  coe p := p.toSubmodule
  coe_injective' _ _ h := HomogeneousSubmodule.toSubmodule_injective 𝒜 ℳ <| SetLike.coe_injective h

@[ext]
theorem HomogeneousSubmodule.ext
    {I J : HomogeneousSubmodule 𝒜 ℳ} (h : I.toSubmodule = J.toSubmodule) : I = J :=
  HomogeneousSubmodule.toSubmodule_injective _ _ h

/--
The set-theoretic extensionality of `HomogeneousSubmodule`.
-/
theorem HomogeneousSubmodule.ext' {I J : HomogeneousSubmodule 𝒜 ℳ}
    (h : ∀ i, ∀ x ∈ ℳ i, x ∈ I ↔ x ∈ J) :
    I = J := by
  ext
  rw [I.isHomogeneous.mem_iff, J.isHomogeneous.mem_iff]
  apply forall_congr'
  exact fun i ↦ h i _ (decompose ℳ _ i).2

@[simp]
theorem HomogeneousSubmodule.mem_iff {I : HomogeneousSubmodule 𝒜 ℳ} {x : M} :
    x ∈ I.toSubmodule (A := A) ↔ x ∈ I :=
  Iff.rfl

end HomogeneousDef

section HomogeneousCore

variable (ℳ : ιM → σM) [SetLike σM M]

variable (A) in
/-- For any `p : Submodule A M`, not necessarily homogeneous, `p.homogeneousCore' ℳ`
is the largest homogeneous `A`-submodule contained in `p`, as an `A`-submodule. -/
def Submodule.homogeneousCore' (p : Submodule A M)  : Submodule A M :=
  Submodule.span A ((↑) '' (((↑) : Subtype (Homogeneous ℳ) → M) ⁻¹' p))

theorem Submodule.homogeneousCore'_mono :
    Monotone (Submodule.homogeneousCore' A ℳ) :=
  fun _ _ I_le_J => Submodule.span_mono <| Set.image_subset _ fun _ => @I_le_J _

theorem Submodule.homogeneousCore'_le (p : Submodule A M) : p.homogeneousCore' A ℳ ≤ p :=
  Submodule.span_le.2 <| image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousSubmoduleDefs

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)
variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

theorem Submodule.isHomogeneous_iff_forall_subset (p : Submodule A M) :
    p.IsHomogeneous ℳ ↔ ∀ i, (p : Set M) ⊆ GradedModule.proj ℳ i ⁻¹' (p : Set M) :=
  Iff.rfl

theorem Submodule.isHomogeneous_iff_subset_iInter (p : Submodule A M) :
    p.IsHomogeneous ℳ ↔ (p : Set M) ⊆ ⋂ i, GradedModule.proj ℳ i ⁻¹' ↑p :=
  subset_iInter_iff.symm

variable (p : Submodule A M)

include 𝒜 in
theorem Submodule.smul_homogeneous_element_mem_of_mem (r : A) (x : M)
    (hx₁ : Homogeneous ℳ x) (hx₂ : x ∈ p) (j : ιM) :
    GradedModule.proj ℳ j (r • x) ∈ p := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_smul, map_sum]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  obtain ⟨i, hi⟩ := hx₁
  rw [GradedModule.proj_apply, decompose_of_mem ℳ (GradedSMul.smul_mem (SetLike.coe_mem _) hi),
    coe_of_apply]
  aesop

include 𝒜 in
theorem Submodule.homogeneous_span (s : Set M) (h : ∀ x ∈ s, Homogeneous ℳ x) :
    (Submodule.span A s).IsHomogeneous ℳ := by
  rintro i r hr
  rw [mem_span_set] at hr
  obtain ⟨c, hc, rfl⟩ := hr
  rw [Finsupp.sum, decompose_sum, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  exact Submodule.sum_mem _ fun z hz1 ↦ Submodule.smul_homogeneous_element_mem_of_mem 𝒜 ℳ _ _ _
    (h _ (hc hz1)) (Submodule.subset_span (hc hz1)) _

/-- For any `p : Submodule A M`, not necessarily homogeneous, `p.homogeneousCore' ℳ`
is the largest homogeneous `A`-submodule contained in `p`. -/
def Submodule.homogeneousCore : HomogeneousSubmodule 𝒜 ℳ :=
  ⟨p.homogeneousCore' A ℳ, Submodule.homogeneous_span 𝒜 ℳ _ fun _ h => by aesop⟩

theorem Submodule.homogeneousCore_mono : Monotone (Submodule.homogeneousCore 𝒜 ℳ) :=
  Submodule.homogeneousCore'_mono ℳ

theorem Submodule.toSubmodule_homogeneousCore_le : (p.homogeneousCore 𝒜 ℳ).toSubmodule ≤ p :=
  Submodule.homogeneousCore'_le _ _

theorem Submodule.mem_homogeneousCore_of_homogeneous_of_mem {x : M} (h : Homogeneous ℳ x)
    (hmem : x ∈ p) : x ∈ p.homogeneousCore 𝒜 ℳ :=
  Submodule.subset_span ⟨⟨x, h⟩, hmem, rfl⟩

theorem Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self (h : p.IsHomogeneous ℳ) :
    (p.homogeneousCore 𝒜 ℳ).toSubmodule = p :=
  le_antisymm (p.homogeneousCore'_le ℳ) <| fun x hx ↦ by
  classical
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨⟨_, homogeneous_coe _⟩, h _ hx, rfl⟩

@[simp]
theorem HomogeneousSubmodule.toSubmodule_homogeneousCore_eq_self (p : HomogeneousSubmodule 𝒜 ℳ) :
    p.toSubmodule.homogeneousCore 𝒜 ℳ = p := by
  ext1
  convert Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self 𝒜 ℳ _ p.isHomogeneous

theorem Submodule.IsHomogeneous.iff_eq :
    p.IsHomogeneous ℳ ↔ (p.homogeneousCore 𝒜 ℳ).toSubmodule = p :=
  ⟨fun hI => hI.toSubmodule_homogeneousCore_eq_self 𝒜 ℳ, fun hI => hI ▸ (p.homogeneousCore 𝒜 ℳ).2⟩

include 𝒜 in
theorem Submodule.IsHomogeneous.iff_exists :
    p.IsHomogeneous ℳ ↔ ∃ S : Set {x // Homogeneous ℳ x}, p = Submodule.span A ((↑) '' S) := by
  rw [Submodule.IsHomogeneous.iff_eq 𝒜, eq_comm]
  exact ((Set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm

end IsHomogeneousSubmoduleDefs

section Operations

namespace Submodule.IsHomogeneous

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)
variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

theorem bot : Submodule.IsHomogeneous (A := A) ⊥ ℳ := fun i r hr => by
  simp only [Submodule.mem_bot] at hr
  rw [hr, decompose_zero, zero_apply]
  apply Submodule.zero_mem

theorem top : Submodule.IsHomogeneous (A := A) ⊤ ℳ :=
  fun i r _ => by simp only [Submodule.mem_top]

theorem inf {I J : Submodule A M} (HI : I.IsHomogeneous ℳ) (HJ : J.IsHomogeneous ℳ) :
    (I ⊓ J).IsHomogeneous ℳ := fun _ _ hr => ⟨HI _ hr.1, HJ _ hr.2⟩

include 𝒜 in
theorem sup {I J : Submodule A M} (HI : I.IsHomogeneous ℳ) (HJ : J.IsHomogeneous ℳ) :
    (I ⊔ J).IsHomogeneous ℳ := by
  rw [iff_exists 𝒜 ℳ] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  refine ⟨s₁ ∪ s₂, ?_⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm

include 𝒜 in
protected theorem iSup {κ : Sort*} {f : κ → Submodule A M} (h : ∀ i, (f i).IsHomogeneous ℳ) :
    (⨆ i, f i).IsHomogeneous ℳ := by
  simp_rw [iff_exists 𝒜 ℳ] at h ⊢
  choose s hs using h
  refine ⟨⋃ i, s i, ?_⟩
  simp_rw [Set.image_iUnion, Submodule.span_iUnion]
  congr
  exact funext hs

protected theorem iInf {κ : Sort*} {f : κ → Submodule A M} (h : ∀ i, (f i).IsHomogeneous ℳ) :
    (⨅ i, f i).IsHomogeneous ℳ := by
  intro i x hx
  simp only [Submodule.mem_iInf] at hx ⊢
  exact fun j => h _ _ (hx j)

include 𝒜 in
theorem iSup₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Submodule A M}
    (h : ∀ i j, (f i j).IsHomogeneous ℳ) : (⨆ (i) (j), f i j).IsHomogeneous ℳ :=
  IsHomogeneous.iSup 𝒜 ℳ fun i => IsHomogeneous.iSup 𝒜 ℳ <| h i

theorem iInf₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Submodule A M}
    (h : ∀ i j, (f i j).IsHomogeneous ℳ) : (⨅ (i) (j), f i j).IsHomogeneous ℳ :=
  IsHomogeneous.iInf ℳ fun i => IsHomogeneous.iInf ℳ <| h i

include 𝒜 in
theorem sSup {ℐ : Set (Submodule A M)} (h : ∀ I ∈ ℐ, I.IsHomogeneous ℳ) :
    (sSup ℐ).IsHomogeneous ℳ := by
  rw [sSup_eq_iSup]
  exact iSup₂ 𝒜 ℳ h

theorem sInf {ℐ : Set (Submodule A M)} (h : ∀ I ∈ ℐ, I.IsHomogeneous ℳ) :
    (sInf ℐ).IsHomogeneous ℳ := by
  rw [sInf_eq_iInf]
  exact iInf₂ ℳ h

end Submodule.IsHomogeneous

namespace HomogeneousSubmodule

variable {𝒜 : ιA → σA} {ℳ : ιM → σM}

variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

instance : PartialOrder (HomogeneousSubmodule 𝒜 ℳ) :=
  SetLike.instPartialOrder

instance : Top (HomogeneousSubmodule 𝒜 ℳ) :=
  ⟨⟨⊤, Submodule.IsHomogeneous.top ℳ⟩⟩

instance : Bot (HomogeneousSubmodule 𝒜 ℳ) :=
  ⟨⟨⊥, Submodule.IsHomogeneous.bot ℳ⟩⟩

instance sup : Sup (HomogeneousSubmodule 𝒜 ℳ) :=
  ⟨fun I J => ⟨I.toSubmodule ⊔ J.toSubmodule, I.2.sup 𝒜 ℳ (HJ := J.isHomogeneous)⟩⟩

instance : Inf (HomogeneousSubmodule 𝒜 ℳ) :=
  ⟨fun I J => ⟨_, I.2.inf (HJ := J.isHomogeneous)⟩⟩

instance supSet : SupSet (HomogeneousSubmodule 𝒜 ℳ) :=
  ⟨fun S => ⟨⨆ s ∈ S, toSubmodule s,
    Submodule.IsHomogeneous.iSup₂ 𝒜 ℳ fun s _ => s.2⟩⟩

instance : InfSet (HomogeneousSubmodule 𝒜 ℳ) :=
  ⟨fun S => ⟨⨅ s ∈ S, toSubmodule s, Submodule.IsHomogeneous.iInf₂ ℳ fun s _ => s.isHomogeneous⟩⟩

@[simp]
theorem coe_top : ((⊤ : HomogeneousSubmodule 𝒜 ℳ) : Set M) = univ :=
  rfl

@[simp]
theorem coe_bot : ((⊥ : HomogeneousSubmodule 𝒜 ℳ) : Set M) = 0 :=
  rfl

@[simp]
theorem coe_sup (I J : HomogeneousSubmodule 𝒜 ℳ) : ↑(I ⊔ J) = (I + J : Set M) :=
  Submodule.coe_sup _ _

@[simp, nolint simpNF]
theorem coe_inf (I J : HomogeneousSubmodule 𝒜 ℳ) : (↑(I ⊓ J) : Set M) = ↑I ∩ ↑J :=
  rfl

@[simp]
theorem toSubmodule_top : (⊤ : HomogeneousSubmodule 𝒜 ℳ).toSubmodule = (⊤ : Submodule A M) :=
  rfl

@[simp]
theorem toSubmodule_bot : (⊥ : HomogeneousSubmodule 𝒜 ℳ).toSubmodule = (⊥ : Submodule A M) :=
  rfl

@[simp]
theorem toSubmodule_sup (I J : HomogeneousSubmodule 𝒜 ℳ) :
    (I ⊔ J).toSubmodule = I.toSubmodule ⊔ J.toSubmodule := rfl

@[simp, nolint simpNF]
theorem toSubmodule_inf (I J : HomogeneousSubmodule 𝒜 ℳ) :
    (I ⊓ J).toSubmodule = I.toSubmodule ⊓ J.toSubmodule := rfl

@[simp]
theorem toSubmodule_sSup (ℐ : Set (HomogeneousSubmodule 𝒜 ℳ)) :
    (sSup ℐ).toSubmodule = ⨆ s ∈ ℐ, toSubmodule s := rfl

@[simp]
theorem toSubmodule_sInf (ℐ : Set (HomogeneousSubmodule 𝒜 ℳ)) :
    (sInf ℐ).toSubmodule = ⨅ s ∈ ℐ, toSubmodule s := rfl

@[simp]
theorem toSubmodule_iSup {κ : Sort*} (s : κ → HomogeneousSubmodule 𝒜 ℳ) :
    (⨆ i, s i).toSubmodule = ⨆ i, (s i).toSubmodule := by
  rw [iSup, toSubmodule_sSup, iSup_range]

@[simp, nolint simpNF]
theorem toSubmodule_iInf {κ : Sort*} (s : κ → HomogeneousSubmodule 𝒜 ℳ) :
    (⨅ i, s i).toSubmodule = ⨅ i, (s i).toSubmodule := by
  rw [iInf, toSubmodule_sInf, iInf_range]

-- @[simp] -- Porting note: simp can prove this
theorem toSubmodule_iSup₂ {κ : Sort*} {κ' : κ → Sort*}
    (s : ∀ i, κ' i → HomogeneousSubmodule 𝒜 ℳ) :
    (⨆ (i) (j), s i j).toSubmodule = ⨆ (i) (j), (s i j).toSubmodule := by
  simp_rw [toSubmodule_iSup]

-- @[simp] -- Porting note: simp can prove this
theorem toSubmodule_iInf₂ {κ : Sort*} {κ' : κ → Sort*}
    (s : ∀ i, κ' i → HomogeneousSubmodule 𝒜 ℳ) :
    (⨅ (i) (j), s i j).toSubmodule = ⨅ (i) (j), (s i j).toSubmodule := by
  simp_rw [toSubmodule_iInf]

@[simp]
theorem eq_top_iff (I : HomogeneousSubmodule 𝒜 ℳ) : I = ⊤ ↔ I.toSubmodule = ⊤ :=
  (toSubmodule_injective 𝒜 ℳ).eq_iff.symm

@[simp]
theorem eq_bot_iff (I : HomogeneousSubmodule 𝒜 ℳ) : I = ⊥ ↔ I.toSubmodule = ⊥ :=
  (toSubmodule_injective 𝒜 ℳ).eq_iff.symm

instance completeLattice : CompleteLattice (HomogeneousSubmodule 𝒜 ℳ) :=
  (toSubmodule_injective 𝒜 ℳ).completeLattice _ toSubmodule_sup toSubmodule_inf toSubmodule_sSup
    toSubmodule_sInf toSubmodule_top toSubmodule_bot

instance : Add (HomogeneousSubmodule 𝒜 ℳ) := ⟨(· ⊔ ·)⟩

@[simp]
theorem toSubmodule_add (I J : HomogeneousSubmodule 𝒜 ℳ) :
    (I + J).toSubmodule = I.toSubmodule + J.toSubmodule := rfl

instance : Inhabited (HomogeneousSubmodule 𝒜 ℳ) where default := ⊥

end HomogeneousSubmodule

end Operations

section homogeneousCore

open HomogeneousSubmodule

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)

variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

variable (p : Submodule A M)

theorem Submodule.homogeneousCore.gc :
    GaloisConnection toSubmodule (Submodule.homogeneousCore 𝒜 ℳ) := fun I _ =>
  ⟨fun H => I.toSubmodule_homogeneousCore_eq_self (𝒜 := 𝒜) ▸ Submodule.homogeneousCore_mono 𝒜 ℳ H,
    fun H => le_trans H (Submodule.homogeneousCore'_le _ _)⟩

/-- `toSubmodule : HomogeneousSubmodule A ℳ → Submodule A M` and `Submodule.homogeneousCore 𝒜 ℳ`
forms a galois coinsertion. -/
def Submodule.homogeneousCore.gi :
    GaloisCoinsertion toSubmodule (Submodule.homogeneousCore 𝒜 ℳ) where
  choice I HI :=
    ⟨I, le_antisymm (I.toSubmodule_homogeneousCore_le 𝒜 ℳ) HI ▸
      HomogeneousSubmodule.isHomogeneous _⟩
  gc := Submodule.homogeneousCore.gc 𝒜 ℳ
  u_l_le _ := Submodule.homogeneousCore'_le _ _
  choice_eq I H := le_antisymm H (I.toSubmodule_homogeneousCore_le _ _)

theorem Submodule.homogeneousCore_eq_sSup :
    p.homogeneousCore 𝒜 ℳ = sSup { q : HomogeneousSubmodule 𝒜 ℳ | q.toSubmodule ≤ p } :=
  Eq.symm <| IsLUB.sSup_eq <| (Submodule.homogeneousCore.gc 𝒜 ℳ).isGreatest_u.isLUB

include 𝒜 in
theorem Submodule.homogeneousCore'_eq_sSup :
    p.homogeneousCore' A ℳ = sSup { q : Submodule A M | q.IsHomogeneous ℳ ∧ q ≤ p } := by
  refine (IsLUB.sSup_eq <| IsGreatest.isLUB ?_).symm
  have coe_mono : Monotone (toSubmodule : HomogeneousSubmodule 𝒜 ℳ → Submodule A M) := fun x y => id
  convert coe_mono.map_isGreatest (Submodule.homogeneousCore.gc 𝒜 ℳ).isGreatest_u using 1
  ext x
  rw [mem_image, mem_setOf_eq]
  refine ⟨fun hI => ⟨⟨x, hI.1⟩, ⟨hI.2, rfl⟩⟩, ?_⟩
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact ⟨x.isHomogeneous, hx⟩

end homogeneousCore

section homogeneousHull

open HomogeneousSubmodule

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)

variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

variable (p : Submodule A M)

/-- For any `p : Submodule A M`, not necessarily homogeneous, `p.homogeneousHull 𝒜 ℳ` is the
smallest  homogeneous `A`-submodule containing `p`. -/
def Submodule.homogeneousHull : HomogeneousSubmodule 𝒜 ℳ :=
  ⟨Submodule.span A { r : M | ∃ (i : ιM) (x : p), (DirectSum.decompose ℳ (x : M) i : M) = r }, by
    refine Submodule.homogeneous_span 𝒜 ℳ _ fun x hx => ?_
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.homogeneous_coe⟩

theorem Submodule.le_toSubmodule_homogeneousHull :
    p ≤ (Submodule.homogeneousHull 𝒜 ℳ p).toSubmodule := by
  intro r hr
  classical
  rw [← DirectSum.sum_support_decompose ℳ r]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.subset_span ⟨j, ⟨⟨r, hr⟩, rfl⟩⟩

theorem Submodule.homogeneousHull_mono :
    Monotone (Submodule.homogeneousHull 𝒜 ℳ) := fun I J I_le_J => by
  apply Submodule.span_mono
  rintro r ⟨hr1, ⟨x, hx⟩, rfl⟩
  exact ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩

variable {𝒜 ℳ p}
theorem Submodule.IsHomogeneous.toSubmodule_homogeneousHull_eq_self (h : p.IsHomogeneous ℳ) :
    (Submodule.homogeneousHull 𝒜 ℳ p).toSubmodule = p := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.le_toSubmodule_homogeneousHull _ _ _)
  rintro _ ⟨i, x, rfl⟩
  exact h _ x.prop

@[simp]
theorem HomogeneousSubmodule.homogeneousHull_toSubmodule_eq_self (p : HomogeneousSubmodule 𝒜 ℳ) :
    p.toSubmodule.homogeneousHull 𝒜 ℳ = p :=
  HomogeneousSubmodule.toSubmodule_injective _ _ <| p.2.toSubmodule_homogeneousHull_eq_self

variable (p)
theorem Submodule.toSubmodule_homogeneousHull_eq_iSup :
    (p.homogeneousHull 𝒜 ℳ).toSubmodule = ⨆ i, Submodule.span A (GradedModule.proj ℳ i '' p) := by
  rw [← Submodule.span_iUnion]
  apply congr_arg (Submodule.span A ·) _
  aesop

theorem Submodule.homogeneousHull_eq_iSup :
    p.homogeneousHull 𝒜 ℳ =
      ⨆ i, ⟨Submodule.span A (GradedModule.proj ℳ i '' p), Submodule.homogeneous_span 𝒜 ℳ _ (by
        rintro _ ⟨x, -, rfl⟩
        apply SetLike.homogeneous_coe)⟩ := by
  ext1
  rw [Submodule.toSubmodule_homogeneousHull_eq_iSup, toSubmodule_iSup]

end homogeneousHull

section GaloisConnection

open HomogeneousSubmodule

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)

variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

theorem Submodule.homogeneousHull.gc :
    GaloisConnection (Submodule.homogeneousHull 𝒜 ℳ) toSubmodule := fun _ J =>
  ⟨le_trans (Submodule.le_toSubmodule_homogeneousHull _ _ _),
    fun H => J.homogeneousHull_toSubmodule_eq_self (𝒜 := 𝒜) ▸ Submodule.homogeneousHull_mono 𝒜 ℳ H⟩

/-- `Submodule.homogeneousHull 𝒜 ℳ` and `toSubmodule : HomogeneousSubmodule A ℳ → Submodule A M`
form a galois insertion. -/
def Submodule.homogeneousHull.gi : GaloisInsertion (Submodule.homogeneousHull 𝒜 ℳ) toSubmodule where
  choice I H := ⟨I, le_antisymm H (I.le_toSubmodule_homogeneousHull 𝒜 ℳ) ▸ isHomogeneous _⟩
  gc := Submodule.homogeneousHull.gc 𝒜 ℳ
  le_l_u _ := Submodule.le_toSubmodule_homogeneousHull 𝒜 _ _
  choice_eq I H := le_antisymm (I.le_toSubmodule_homogeneousHull 𝒜 ℳ) H

theorem Submodule.homogeneousHull_eq_sInf (p : Submodule A M) :
    p.homogeneousHull 𝒜 ℳ = sInf { q | p ≤ q.toSubmodule } :=
  Eq.symm <| IsGLB.sInf_eq <| (Submodule.homogeneousHull.gc 𝒜 ℳ).isLeast_l.isGLB

end GaloisConnection
