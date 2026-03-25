/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.Algebra.Module.GradedModule

/-!
# Homogeneous submodules of a graded module

This file defines homogeneous submodule of a graded module `⨁ᵢ ℳᵢ` over graded ring `⨁ᵢ 𝒜ᵢ` and
operations on them.

## Main definitions

For any `p : Submodule A M`:
* `Submodule.IsHomogeneous ℳ p`: The property that a submodule is closed under `GradedModule.proj`.
* `HomogeneousSubmodule 𝒜 ℳ`: The structure extending submodules which satisfy
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
module. However, most interesting properties of homogeneous submodules do rely on the base ring
being a graded ring. For technical reasons, we make `HomogeneousSubmodule` depend on a graded ring.
For example, if the definition of a homogeneous submodule does not depend on a graded ring, the
instance that `HomogeneousSubmodule` is a complete lattice cannot be synthesized due to
synthesization order.

## Tags

graded algebra, homogeneous
-/

@[expose] public section

open SetLike DirectSum Pointwise Set

variable {ιA ιM σA σM A M : Type*}

variable [Semiring A] [AddCommMonoid M] [Module A M]

section HomogeneousDef

/--
An `A`-submodule `p ⊆ M` is homogeneous if for every `m ∈ p`, all homogeneous components of `m` are
in `p`.
-/
def Submodule.IsHomogeneous (p : Submodule A M) (ℳ : ιM → σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ] : Prop :=
  SetLike.IsHomogeneous ℳ p

theorem Submodule.IsHomogeneous.mem_iff {p : Submodule A M}
    (ℳ : ιM → σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
    (hp : p.IsHomogeneous ℳ) {x} :
    x ∈ p ↔ ∀ i, (decompose ℳ x i : M) ∈ p :=
  AddSubmonoidClass.IsHomogeneous.mem_iff ℳ _ hp

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

instance : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
  coe X := X.toSubmodule
  coe_injective' := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ (h : (p : Set M) = q)
    simpa using h

instance : PartialOrder (HomogeneousSubmodule 𝒜 ℳ) := .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M

instance : AddSubmonoidClass (HomogeneousSubmodule 𝒜 ℳ) M where
  zero_mem p := p.toSubmodule.zero_mem
  add_mem hx hy := Submodule.add_mem _ hx hy

instance : SMulMemClass (HomogeneousSubmodule 𝒜 ℳ) A M where
  smul_mem := by
    intro x r m hm
    exact Submodule.smul_mem x.toSubmodule r hm

variable {𝒜 ℳ} in
theorem HomogeneousSubmodule.isHomogeneous (p : HomogeneousSubmodule 𝒜 ℳ) :
    p.toSubmodule.IsHomogeneous ℳ :=
  p.is_homogeneous'

theorem HomogeneousSubmodule.toSubmodule_injective :
    Function.Injective
      (HomogeneousSubmodule.toSubmodule : HomogeneousSubmodule 𝒜 ℳ → Submodule A M) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ fun (h : x = y) ↦ by simp [h]

instance HomogeneousSubmodule.setLike : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
  coe p := p.toSubmodule
  coe_injective' _ _ h := HomogeneousSubmodule.toSubmodule_injective 𝒜 ℳ <| SetLike.coe_injective h

instance : PartialOrder (HomogeneousSubmodule 𝒜 ℳ) := .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M

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
theorem HomogeneousSubmodule.mem_toSubmodule_iff {I : HomogeneousSubmodule 𝒜 ℳ} {x : M} :
    x ∈ I.toSubmodule (A := A) ↔ x ∈ I :=
  Iff.rfl

end HomogeneousDef

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
    (hx₁ : IsHomogeneousElem ℳ x) (hx₂ : x ∈ p) (j : ιM) :
    GradedModule.proj ℳ j (r • x) ∈ p := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_smul, map_sum]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  obtain ⟨i, hi⟩ := hx₁
  rw [GradedModule.proj_apply, decompose_of_mem ℳ (GradedSMul.smul_mem (SetLike.coe_mem _) hi),
    coe_of_apply]
  aesop

include 𝒜 in
theorem Submodule.homogeneous_span (s : Set M) (h : ∀ x ∈ s, IsHomogeneousElem ℳ x) :
    (Submodule.span A s).IsHomogeneous ℳ := by
  rintro i r hr
  rw [mem_span_set] at hr
  obtain ⟨c, hc, rfl⟩ := hr
  rw [decompose_finsuppSum, DirectSum.finsuppSum_apply, AddSubmonoidClass.coe_finsuppSum]
  exact Submodule.finsuppSum_mem _ _ _ _ fun r hr0 ↦
    Submodule.smul_homogeneous_element_mem_of_mem 𝒜 ℳ _ _ _
      (h _ (hc <| by simpa)) (Submodule.subset_span (hc <| by simpa)) _

/-- For any `p : Submodule A M`, not necessarily homogeneous, `p.homogeneousCore' ℳ`
is the largest homogeneous `A`-submodule contained in `p`. -/
def Submodule.homogeneousCore : HomogeneousSubmodule 𝒜 ℳ where
  carrier := { x | ∀ i, (decompose ℳ x i : M) ∈ p }
  add_mem' := by aesop
  zero_mem' := by aesop
  smul_mem' c x hx i := by
    classical rw [← DirectSum.sum_support_decompose ℳ x, Finset.smul_sum, decompose_sum,
      ← DirectSum.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply,
      AddSubmonoidClass.coe_finset_sum]
    exact sum_mem fun j hj ↦ p.smul_homogeneous_element_mem_of_mem 𝒜 ℳ _ _ (by aesop) (hx j) _
  is_homogeneous' _ _ _ _ := by aesop (add norm coe_of_apply)

theorem Submodule.toSubmodule_homogeneousCore_eq_span :
    (p.homogeneousCore 𝒜 ℳ).toSubmodule =
    .span A ((↑) '' (((↑) : Subtype (IsHomogeneousElem ℳ) → M) ⁻¹' p)) := by
  rw [image_preimage_eq_inter_range]
  refine le_antisymm (fun x hx ↦ ?_) <| span_le.mpr ?_
  · classical rw [← DirectSum.sum_support_decompose ℳ x]
    exact sum_mem <| by aesop
  · rintro _ ⟨hxp, ⟨x, i, hxi⟩, rfl⟩ j
    rw [decompose_of_mem ℳ hxi]
    aesop (add norm coe_of_apply)

theorem Submodule.homogeneousCore_mono : Monotone (Submodule.homogeneousCore 𝒜 ℳ) :=
  fun _ _ hpq _ hx i ↦ hpq <| hx i

theorem Submodule.toSubmodule_homogeneousCore_le : (p.homogeneousCore 𝒜 ℳ).toSubmodule ≤ p := by
  intro x hx
  classical rw [← DirectSum.sum_support_decompose ℳ x]
  exact sum_mem fun i hi ↦ hx i

theorem Submodule.mem_homogeneousCore_of_homogeneous_of_mem {x : M} (h : IsHomogeneousElem ℳ x)
    (hmem : x ∈ p) : x ∈ p.homogeneousCore 𝒜 ℳ := by
  obtain ⟨i, hx⟩ := h
  intro j
  rw [decompose_of_mem ℳ hx]
  aesop (add norm coe_of_apply)

theorem Submodule.le_homogeneousCore_of_homogeneous_of_le {q : Submodule A M}
    (hq : q.IsHomogeneous ℳ) (hqp : q ≤ p) : q ≤ (p.homogeneousCore 𝒜 ℳ).toSubmodule :=
  fun _ hx i ↦ hqp <| hq i hx

theorem Submodule.IsHomogeneous.le_toSubmodule_homogeneousCore_iff {p q : Submodule A M}
    (hp : p.IsHomogeneous ℳ) : p ≤ (q.homogeneousCore 𝒜 ℳ).toSubmodule ↔ p ≤ q :=
  ⟨(·.trans <| q.toSubmodule_homogeneousCore_le 𝒜 ℳ),
  q.le_homogeneousCore_of_homogeneous_of_le 𝒜 ℳ hp⟩

variable {p} in
theorem HomogeneousSubmodule.le_homogeneousCore_iff (q : HomogeneousSubmodule 𝒜 ℳ) :
    q ≤ p.homogeneousCore 𝒜 ℳ ↔ q.toSubmodule ≤ p :=
  q.2.le_toSubmodule_homogeneousCore_iff 𝒜 ℳ

theorem Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self (h : p.IsHomogeneous ℳ) :
    (p.homogeneousCore 𝒜 ℳ).toSubmodule = p :=
  le_antisymm (p.toSubmodule_homogeneousCore_le 𝒜 ℳ) fun _ hx i ↦ h i hx

@[simp]
theorem HomogeneousSubmodule.toSubmodule_homogeneousCore_eq_self (p : HomogeneousSubmodule 𝒜 ℳ) :
    p.toSubmodule.homogeneousCore 𝒜 ℳ = p :=
  ext _ _ <| p.2.toSubmodule_homogeneousCore_eq_self 𝒜 ℳ _

theorem Submodule.IsHomogeneous.iff_eq :
    p.IsHomogeneous ℳ ↔ (p.homogeneousCore 𝒜 ℳ).toSubmodule = p :=
  ⟨fun hI => hI.toSubmodule_homogeneousCore_eq_self 𝒜 ℳ, fun hI => hI ▸ (p.homogeneousCore 𝒜 ℳ).2⟩

include 𝒜 in
theorem Submodule.IsHomogeneous.iff_exists :
    p.IsHomogeneous ℳ ↔
    ∃ S : Set {x // IsHomogeneousElem ℳ x}, p = Submodule.span A ((↑) '' S) := by
  rw [iff_eq 𝒜, toSubmodule_homogeneousCore_eq_span, eq_comm]
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

instance : PartialOrder (HomogeneousSubmodule 𝒜 ℳ) := .ofSetLike ..

instance : Top (HomogeneousSubmodule 𝒜 ℳ) :=
  ⟨⟨⊤, Submodule.IsHomogeneous.top ℳ⟩⟩

instance : Bot (HomogeneousSubmodule 𝒜 ℳ) :=
  ⟨⟨⊥, Submodule.IsHomogeneous.bot ℳ⟩⟩

instance sup : Max (HomogeneousSubmodule 𝒜 ℳ) :=
  ⟨fun I J => ⟨I.toSubmodule ⊔ J.toSubmodule, I.2.sup 𝒜 ℳ (HJ := J.isHomogeneous)⟩⟩

instance : Min (HomogeneousSubmodule 𝒜 ℳ) :=
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
  (toSubmodule_injective 𝒜 ℳ).completeLattice _ Iff.rfl Iff.rfl toSubmodule_sup toSubmodule_inf
    toSubmodule_sSup toSubmodule_sInf toSubmodule_top toSubmodule_bot

instance : Add (HomogeneousSubmodule 𝒜 ℳ) := ⟨(· ⊔ ·)⟩

@[simp]
theorem toSubmodule_add (I J : HomogeneousSubmodule 𝒜 ℳ) :
    (I + J).toSubmodule = I.toSubmodule + J.toSubmodule := rfl

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
    GaloisConnection toSubmodule (Submodule.homogeneousCore 𝒜 ℳ) := fun p _ ↦
  (p.le_homogeneousCore_iff 𝒜 ℳ).symm

/-- `toSubmodule : HomogeneousSubmodule A ℳ → Submodule A M` and `Submodule.homogeneousCore 𝒜 ℳ`
forms a galois coinsertion. -/
def Submodule.homogeneousCore.gi :
    GaloisCoinsertion toSubmodule (Submodule.homogeneousCore 𝒜 ℳ) where
  choice I HI :=
    ⟨I, le_antisymm (I.toSubmodule_homogeneousCore_le 𝒜 ℳ) HI ▸
      HomogeneousSubmodule.isHomogeneous _⟩
  gc := Submodule.homogeneousCore.gc 𝒜 ℳ
  u_l_le _ := Submodule.toSubmodule_homogeneousCore_le _ _ _
  choice_eq I H := le_antisymm H (I.toSubmodule_homogeneousCore_le _ _)

theorem HomogeneousSubmodule.toSubmodule_le_toSubmodule_iff {p q : HomogeneousSubmodule 𝒜 ℳ} :
    p.toSubmodule ≤ q.toSubmodule ↔ p ≤ q :=
  (Submodule.homogeneousCore.gi 𝒜 ℳ).l_le_l_iff

theorem Submodule.homogeneousCore_eq_sSup :
    p.homogeneousCore 𝒜 ℳ = sSup { q : HomogeneousSubmodule 𝒜 ℳ | q.toSubmodule ≤ p } :=
  Eq.symm <| IsLUB.sSup_eq <| (Submodule.homogeneousCore.gc 𝒜 ℳ).isGreatest_u.isLUB

include 𝒜 in
theorem Submodule.toSubmodule_homogeneousCore_eq_sSup :
    (p.homogeneousCore 𝒜 ℳ).toSubmodule =
    sSup { q : Submodule A M | q.IsHomogeneous ℳ ∧ q ≤ p } := by
  rw [Submodule.homogeneousCore_eq_sSup, toSubmodule_sSup]
  exact le_antisymm (iSup_le fun q ↦ iSup_le fun hqp ↦ le_sSup ⟨q.2, hqp⟩) <|
    sSup_le fun q hq ↦ le_biSup HomogeneousSubmodule.toSubmodule (i := ⟨q, hq.1⟩) hq.2

end homogeneousCore

section homogeneousHull

open HomogeneousSubmodule

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)

variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

variable (p : Submodule A M)

/-- For any `p : Submodule A M`, not necessarily homogeneous, `p.homogeneousHull 𝒜 ℳ` is the
smallest homogeneous `A`-submodule containing `p`. -/
def Submodule.homogeneousHull : HomogeneousSubmodule 𝒜 ℳ :=
  ⟨Submodule.span A { r : M | ∃ (i : ιM) (x : p), (DirectSum.decompose ℳ (x : M) i : M) = r }, by
    refine Submodule.homogeneous_span 𝒜 ℳ _ fun x hx => ?_
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.isHomogeneousElem_coe⟩

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

variable {p}

theorem Submodule.IsHomogeneous.homogeneousHull_le_iff
    {q : Submodule A M} (hq : q.IsHomogeneous ℳ) :
    (p.homogeneousHull 𝒜 ℳ).toSubmodule ≤ q ↔ p ≤ q := by
  refine ⟨(p.le_toSubmodule_homogeneousHull 𝒜 ℳ|>.trans ·), fun hpq ↦ span_le.mpr ?_⟩
  rintro - ⟨i, x, rfl⟩
  exact hq i <| hpq x.2

theorem Submodule.IsHomogeneous.toSubmodule_homogeneousHull_eq_self (h : p.IsHomogeneous ℳ) :
    (Submodule.homogeneousHull 𝒜 ℳ p).toSubmodule = p :=
  le_antisymm ((h.homogeneousHull_le_iff 𝒜 ℳ).mpr le_rfl) <| le_toSubmodule_homogeneousHull _ _ _

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
        apply SetLike.isHomogeneousElem_coe)⟩ := by
  ext1
  rw [Submodule.toSubmodule_homogeneousHull_eq_iSup, toSubmodule_iSup]

variable {𝒜 ℳ}

theorem HomogeneousSubmodule.homogeneousHull_le_iff
    {p : Submodule A M} {q : HomogeneousSubmodule 𝒜 ℳ} :
    p.homogeneousHull 𝒜 ℳ ≤ q ↔ p ≤ q.toSubmodule :=
  Submodule.IsHomogeneous.homogeneousHull_le_iff 𝒜 ℳ q.isHomogeneous

@[simp]
theorem HomogeneousSubmodule.homogeneousHull_toSubmodule_eq_self (p : HomogeneousSubmodule 𝒜 ℳ) :
    p.toSubmodule.homogeneousHull 𝒜 ℳ = p :=
  ext _ _ <| p.2.toSubmodule_homogeneousHull_eq_self 𝒜 ℳ

end homogeneousHull

section GaloisConnection

open HomogeneousSubmodule

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)

variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

theorem Submodule.homogeneousHull.gc :
    GaloisConnection (Submodule.homogeneousHull 𝒜 ℳ) toSubmodule := fun _ _ =>
  homogeneousHull_le_iff

/-- `Submodule.homogeneousHull 𝒜 ℳ` and `toSubmodule : HomogeneousSubmodule A ℳ → Submodule A M`
form a galois insertion. -/
def Submodule.homogeneousHull.gi :
    GaloisInsertion (Submodule.homogeneousHull 𝒜 ℳ) toSubmodule where
  choice I H := ⟨I, le_antisymm H (I.le_toSubmodule_homogeneousHull 𝒜 ℳ) ▸ isHomogeneous _⟩
  gc := Submodule.homogeneousHull.gc 𝒜 ℳ
  le_l_u _ := Submodule.le_toSubmodule_homogeneousHull 𝒜 _ _
  choice_eq I H := le_antisymm (I.le_toSubmodule_homogeneousHull 𝒜 ℳ) H

theorem Submodule.homogeneousHull_eq_sInf (p : Submodule A M) :
    p.homogeneousHull 𝒜 ℳ = sInf { q | p ≤ q.toSubmodule } :=
  Eq.symm <| IsGLB.sInf_eq <| (Submodule.homogeneousHull.gc 𝒜 ℳ).isLeast_l.isGLB

end GaloisConnection
