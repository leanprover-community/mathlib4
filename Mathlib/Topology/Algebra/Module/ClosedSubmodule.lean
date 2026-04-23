/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Sets.Closeds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Closed submodules of a topological module

This file builds the frame of closed `R`-submodules of a topological module `M`.

One can turn `s : Submodule R E` + `hs : IsClosed s` into `s : ClosedSubmodule R E` in a tactic
block by doing `lift s to ClosedSubmodule R E using hs`.

## TODO

Actually provide the `Order.Frame (ClosedSubmodule R M)` instance.
-/

@[expose] public section

open Function Order TopologicalSpace

variable {ι : Sort*} {R M N O : Type*} [Semiring R]
  [AddCommMonoid M] [TopologicalSpace M] [Module R M]
  [AddCommMonoid N] [TopologicalSpace N] [Module R N]
  [AddCommMonoid O] [TopologicalSpace O] [Module R O]

variable (R M) in
/-- The type of closed submodules of a topological module. -/
@[ext]
structure ClosedSubmodule extends Submodule R M, Closeds M where

namespace ClosedSubmodule
variable {s t : ClosedSubmodule R M} {x : M}

attribute [coe] toSubmodule toCloseds

/-- Reinterpret a closed submodule as a submodule. -/
add_decl_doc toSubmodule

/-- Reinterpret a closed submodule as a closed set. -/
add_decl_doc toCloseds

lemma toSubmodule_injective : Injective (toSubmodule : ClosedSubmodule R M → Submodule R M) :=
  fun s t h ↦ by cases s; congr!

instance : SetLike (ClosedSubmodule R M) M where
  coe s := s.1
  coe_injective' _ _ h := toSubmodule_injective <| SetLike.coe_injective h

instance : PartialOrder (ClosedSubmodule R M) := .ofSetLike (ClosedSubmodule R M) M

lemma toCloseds_injective : Injective (toCloseds : ClosedSubmodule R M → Closeds M) :=
  fun _s _t h ↦ SetLike.coe_injective congr(($h : Set M))

instance : AddSubmonoidClass (ClosedSubmodule R M) M where
  zero_mem s := s.zero_mem
  add_mem {s} := s.add_mem

instance : SMulMemClass (ClosedSubmodule R M) R M where
  smul_mem {s} r := s.smul_mem r

instance : Coe (ClosedSubmodule R M) (Submodule R M) where
  coe := toSubmodule

@[simp] lemma carrier_eq_coe (s : ClosedSubmodule R M) : s.carrier = s := rfl

@[simp] lemma mem_mk {s : Submodule R M} {hs} : x ∈ mk s hs ↔ x ∈ s := .rfl

@[simp, norm_cast]
lemma coe_toSubmodule (s : ClosedSubmodule R M) : (s.toSubmodule : Set M) = s := rfl

@[simp]
lemma mem_toSubmodule_iff (x : M) (s : ClosedSubmodule R M) : x ∈ s.toSubmodule ↔ x ∈ s := by
  rfl

@[simp]
lemma coe_toCloseds (s : ClosedSubmodule R M) : (s.toCloseds : Set M) = s := rfl

lemma isClosed (s : ClosedSubmodule R M) : IsClosed (s : Set M) := s.isClosed'

initialize_simps_projections ClosedSubmodule (carrier → coe, as_prefix coe)

instance : CanLift (Submodule R M) (ClosedSubmodule R M) toSubmodule (IsClosed (X := M) ·) where
  prf s hs := ⟨⟨s, hs⟩, rfl⟩

@[simp, norm_cast] lemma toSubmodule_le_toSubmodule {s t : ClosedSubmodule R M} :
    s.toSubmodule ≤ t.toSubmodule ↔ s ≤ t := .rfl

/-- The preimage of a closed submodule under a continuous linear map as a closed submodule. -/
@[simps!]
def comap (f : M →L[R] N) (s : ClosedSubmodule R N) : ClosedSubmodule R M where
  toSubmodule := .comap (f : M →ₗ[R] N) s
  isClosed' := by simpa using s.isClosed.preimage f.continuous

@[simp]
lemma mem_comap {f : M →L[R] N} {s : ClosedSubmodule R N} {x : M} : x ∈ s.comap f ↔ f x ∈ s := .rfl

@[simp] lemma toSubmodule_comap (f : M →L[R] N) (s : ClosedSubmodule R N) :
    (s.comap f).toSubmodule = s.toSubmodule.comap (f : M →ₗ[R] N) := rfl

@[simp] lemma comap_id (s : ClosedSubmodule R M) : s.comap (.id _ _) = s := rfl

lemma comap_comap (g : N →L[R] O) (f : M →L[R] N) (s : ClosedSubmodule R O) :
    (s.comap g).comap f = s.comap (g.comp f) := rfl

instance instInf : Min (ClosedSubmodule R M) where
  min s t := ⟨s ⊓ t, s.isClosed.inter t.isClosed⟩

instance instInfSet : InfSet (ClosedSubmodule R M) where
  sInf S := ⟨⨅ s ∈ S, s, by simpa using isClosed_biInter fun x hx ↦ x.isClosed⟩

@[simp, norm_cast]
lemma toSubmodule_sInf (S : Set (ClosedSubmodule R M)) :
    toSubmodule (sInf S) = ⨅ s ∈ S, s.toSubmodule := rfl

@[simp, norm_cast]
lemma toSubmodule_iInf (f : ι → ClosedSubmodule R M) :
    toSubmodule (⨅ i, f i) = ⨅ i, (f i).toSubmodule := by rw [iInf, toSubmodule_sInf, iInf_range]

@[simp, norm_cast]
lemma coe_sInf (S : Set (ClosedSubmodule R M)) : ↑(sInf S) = ⨅ s ∈ S, (s : Set M) := by
  simp [← coe_toSubmodule]

@[simp, norm_cast]
lemma coe_iInf (f : ι → ClosedSubmodule R M) : ↑(⨅ i, f i) = ⨅ i, (f i : Set M) := by
  simp [← coe_toSubmodule]

@[simp] lemma mem_sInf {S : Set (ClosedSubmodule R M)} : x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s := by
  simp [← SetLike.mem_coe]

@[simp] lemma mem_iInf {f : ι → ClosedSubmodule R M} : x ∈ ⨅ i, f i ↔ ∀ i, x ∈ f i := by
  simp [← SetLike.mem_coe]

instance instSemilatticeInf : SemilatticeInf (ClosedSubmodule R M) :=
  toSubmodule_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

@[simp, norm_cast]
lemma toSubmodule_inf (s t : ClosedSubmodule R M) :
    toSubmodule (s ⊓ t) = s.toSubmodule ⊓ t.toSubmodule := rfl

@[simp, norm_cast] lemma coe_inf (s t : ClosedSubmodule R M) : ↑(s ⊓ t) = (s ⊓ t : Set M) := rfl

@[simp] lemma mem_inf : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := .rfl

instance : CompleteSemilatticeInf (ClosedSubmodule R M) where
  isGLB_sInf _ := .of_image toSubmodule_le_toSubmodule isGLB_biInf

instance : OrderTop (ClosedSubmodule R M) where
  top := ⟨⊤, isClosed_univ⟩
  le_top s := le_top (a := s.toSubmodule)

@[simp, norm_cast] lemma toSubmodule_top : toSubmodule (⊤ : ClosedSubmodule R M) = ⊤ := rfl

@[simp, norm_cast] lemma coe_top : ((⊤ : ClosedSubmodule R M) : Set M) = .univ := rfl

@[simp] lemma mem_top : x ∈ (⊤ : ClosedSubmodule R M) := trivial

section T1Space
variable [T1Space M]

instance instOrderBot : OrderBot (ClosedSubmodule R M) where
  bot := ⟨⊥, isClosed_singleton⟩
  bot_le s := bot_le (a := s.toSubmodule)

@[simp, norm_cast] lemma toSubmodule_bot : toSubmodule (⊥ : ClosedSubmodule R M) = ⊥ := rfl

@[simp, norm_cast] lemma coe_bot : ((⊥ : ClosedSubmodule R M) : Set M) = {0} := rfl

@[simp] lemma mem_bot : x ∈ (⊥ : ClosedSubmodule R M) ↔ x = 0 := .rfl

end T1Space
end ClosedSubmodule

namespace Submodule
variable [ContinuousAdd M] [ContinuousConstSMul R M]

/-- The closure of a submodule as a closed submodule. -/
@[simps!]
protected def closure (s : Submodule R M) : ClosedSubmodule R M where
  toSubmodule := s.topologicalClosure
  isClosed' := isClosed_closure

@[simp] lemma closure_le {s : Submodule R M} {t : ClosedSubmodule R M} : s.closure ≤ t ↔ s ≤ t :=
  t.isClosed.closure_subset_iff

@[simp]
lemma mem_closure_iff {x : M} {s : Submodule R M} : x ∈ s.closure ↔ x ∈ s.topologicalClosure :=
  Iff.rfl

@[simp]
lemma closure_eq {s : ClosedSubmodule R M} : s.closure = s := by
  ext
  simp only [carrier_eq_coe, ClosedSubmodule.coe_toSubmodule, coe_closure, SetLike.mem_coe]
  rw [closure_eq_iff_isClosed.mpr]
  · rfl
  · exact s.isClosed'

lemma closure_eq' {s : Submodule R M} (hs : IsClosed s.carrier) : s.closure = ⟨s, hs⟩ := by
  ext; simp

end Submodule

namespace ClosedSubmodule

variable [ContinuousAdd N] [ContinuousConstSMul R N] {f : M →L[R] N}

lemma closure_toSubmodule_eq {s : ClosedSubmodule R N} : s.toSubmodule.closure = s := by
  ext x; simp

/-- The closure of the image of a closed submodule under a continuous linear map is a closed
submodule.

`ClosedSubmodule.map f` is left-adjoint to `ClosedSubmodule.comap f`.
See `ClosedSubmodule.gc_map_comap`. -/
def map (f : M →L[R] N) (s : ClosedSubmodule R M) : ClosedSubmodule R N :=
  (s.toSubmodule.map (f : M →ₗ[R] N)).closure

@[simp]
lemma map_id [ContinuousAdd M] [ContinuousConstSMul R M] (s : ClosedSubmodule R M) :
    s.map (.id _ _) = s := SetLike.coe_injective <| by simp [map]

lemma map_le_iff_le_comap {s : ClosedSubmodule R M} {t : ClosedSubmodule R N} :
    map f s ≤ t ↔ s ≤ comap f t := by
  simp [map, Submodule.map_le_iff_le_comap]; simp [← toSubmodule_le_toSubmodule]

lemma gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦ map_le_iff_le_comap

variable {s t : ClosedSubmodule R N} {x : N}

instance : Max (ClosedSubmodule R N) where
  max s t := (s.toSubmodule ⊔ t.toSubmodule).closure

@[simp]
lemma toSubmodule_sup :
  toSubmodule (s ⊔ t) = (s.toSubmodule ⊔ t.toSubmodule).closure := rfl

@[simp, norm_cast]
lemma coe_sup :
    ↑(s ⊔ t) = closure (s.toSubmodule ⊔ t.toSubmodule).carrier := by
  simp only [← coe_toSubmodule, toSubmodule_sup]
  simp only [coe_toSubmodule, Submodule.coe_closure, Submodule.carrier_eq_coe]

@[simp] lemma mem_sup :
    x ∈ s ⊔ t ↔ x ∈ closure (s.toSubmodule ⊔ t.toSubmodule).carrier := Iff.rfl

instance : SupSet (ClosedSubmodule R N) where
  sSup S := ⟨(⨆ s ∈ S, s.toSubmodule).closure, isClosed_closure⟩

@[simp]
lemma toSubmodule_sSup (S : Set (ClosedSubmodule R N)) :
    toSubmodule (sSup S) = (⨆ s ∈ S, s.toSubmodule).closure := rfl

@[simp]
lemma toSubmodule_iSup (f : ι → ClosedSubmodule R N) :
    toSubmodule (⨆ i, f i) = (⨆ i, (f i).toSubmodule).closure := by
  rw [iSup, toSubmodule_sSup, iSup_range]

@[simp, norm_cast]
lemma coe_sSup (S : Set (ClosedSubmodule R N)) :
    ↑(sSup S) = closure (⨆ s ∈ S, s.toSubmodule).carrier := by
  simp only [← coe_toSubmodule, toSubmodule_sSup]
  simp only [coe_toSubmodule, Submodule.coe_closure, Submodule.carrier_eq_coe]

@[simp, norm_cast]
lemma coe_iSup (f : ι → ClosedSubmodule R N) :
    ↑(⨆ i, f i) = closure (⨆ i, (f i).toSubmodule).carrier := by
  simp only [← coe_toSubmodule, toSubmodule_iSup, Submodule.carrier_eq_coe]
  rfl

@[simp] lemma mem_sSup {S : Set (ClosedSubmodule R N)} :
    x ∈ sSup S ↔ x ∈ closure (⨆ s ∈ S, s.toSubmodule).carrier := Iff.rfl

@[simp] lemma mem_iSup {f : ι → ClosedSubmodule R N} :
    x ∈ ⨆ i, f i ↔ x ∈ closure (⨆ i, (f i).toSubmodule).carrier := by
  simp [← SetLike.mem_coe]

instance : SemilatticeSup (ClosedSubmodule R N) where
  sup s t := s ⊔ t
  le_sup_left _ _ _ hx := subset_closure <| Submodule.mem_sup_left hx
  le_sup_right _ _ _ hx := subset_closure <| Submodule.mem_sup_right hx
  sup_le _ _ _ ha hb := Submodule.closure_le.mpr <| sup_le_iff.mpr ⟨ha, hb⟩

instance : CompleteSemilatticeSup (ClosedSubmodule R N) where
  isLUB_sSup _ := by
    refine ⟨fun a ha x hx ↦ ?_, fun a h x ↦ ?_⟩
    · exact subset_closure <| Submodule.mem_iSup_of_mem _ <| Submodule.mem_iSup_of_mem ha hx
    · rw [← ClosedSubmodule.closure_toSubmodule_eq (s := a)]
      apply closure_mono
      simp only [Submodule.coe_toAddSubmonoid, coe_toSubmodule]
      intro y hy
      simp only [SetLike.mem_coe, Submodule.mem_iSup] at hy
      exact hy a fun b _ hz ↦ Submodule.mem_iSup _ |>.mp hz _ <| fun hb ↦ h hb

instance : Lattice (ClosedSubmodule R N) where

instance [T1Space N] : CompleteLattice (ClosedSubmodule R N) where

end ClosedSubmodule

namespace ClosedSubmodule

variable (f : M ≃L[R] N)

/-- A continuous equivalence `f` between modules `M` and `N` on `R` induces an equivalence between
closed submodules in `M` and those in `N` through `map f`.
The definition does not use `ClosedSubmodule.map` because that has additional `ContinuousAdd` and
`ContinuousConstSMul` type-class assumptions. -/
def mapEquiv : ClosedSubmodule R M ≃ ClosedSubmodule R N where
  toFun s := ⟨s.toSubmodule.map f.toLinearMap, by simpa using s.isClosed⟩
  invFun t := ⟨t.toSubmodule.map f.symm.toLinearMap, by simpa using t.isClosed⟩
  left_inv := by intro _; ext _; simp
  right_inv := by intro _; ext _; simp

variable (s : ClosedSubmodule R M)

@[simp]
lemma mapEquiv_apply : (s.mapEquiv f).toSubmodule = s.toSubmodule.map f.toLinearMap := rfl

@[simp]
lemma mapEquiv_symm : mapEquiv f.symm = (mapEquiv f).symm := rfl

@[simp]
lemma mem_mapEquiv_iff (x : N) : x ∈ (s.mapEquiv f) ↔ f.symm x ∈ s :=
  Submodule.mem_map_equiv (e := f.toLinearEquiv) s.toSubmodule

lemma mem_mapEquiv_iff' (x : M) : f x ∈ (s.mapEquiv f) ↔ x ∈ s := by
  simp

@[simp]
lemma mapEquiv_bot_eq_bot [T1Space M] [T1Space N] : ((⊥ : ClosedSubmodule R M).mapEquiv f) = ⊥ := by
  ext x; simp

@[simp]
lemma mapEquiv_top_eq_top : ((⊤ : ClosedSubmodule R M).mapEquiv f) = ⊤ := by
  ext x; simp

@[simp]
lemma mapEquiv_inf_eq (f : M ≃L[R] N) {s t : ClosedSubmodule R M} :
    (s ⊓ t).mapEquiv f = s.mapEquiv f ⊓ t.mapEquiv f := by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe, toSubmodule_inf,
    Submodule.coe_inf, Set.mem_inter_iff, mem_mapEquiv_iff, mem_inf]

variable [ContinuousAdd N] [ContinuousConstSMul R N] [ContinuousAdd M] [ContinuousConstSMul R M]

@[simp]
lemma closure_map_eq_mapEquiv_closure (s : Submodule R M) :
    (s.map f.toLinearMap).closure = s.closure.mapEquiv f := by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, Submodule.coe_closure, Submodule.map_coe,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, mapEquiv_apply, Set.mem_image]
  rw [← ContinuousLinearEquiv.image_closure]
  simp

@[simp]
lemma mapEquiv_sup_eq (f : M ≃L[R] N) {s t : ClosedSubmodule R M} :
    (s ⊔ t).mapEquiv f = s.mapEquiv f ⊔ t.mapEquiv f := by
  ext x
  simp only [mapEquiv_apply, toSubmodule_sup, Submodule.carrier_eq_coe, Submodule.map_coe,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, coe_toSubmodule,
    Submodule.coe_closure, Set.mem_image]
  have : f = f.toLinearEquiv.toLinearMap := by
    exact LinearMap.ext (congrFun rfl)
  rw [← this, ← Submodule.coe_closure, ← Submodule.map_sup, Submodule.map_coe]
  simp only [Submodule.coe_closure, ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe,
    ← ContinuousLinearEquiv.image_closure, Set.mem_image]

end ClosedSubmodule

section CompleteSpace

instance {𝕜 H : Type*} [Semiring 𝕜] [AddCommMonoid H] [UniformSpace H] [Module 𝕜 H]
    [CompleteSpace H] (K : ClosedSubmodule 𝕜 H) : CompleteSpace K := by
  apply IsComplete.completeSpace_coe
  rw [← ClosedSubmodule.carrier_eq_coe]
  exact K.isClosed'.isComplete

end CompleteSpace
