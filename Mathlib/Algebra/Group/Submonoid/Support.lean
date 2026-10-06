/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Supports of submonoids

Let `G` be an (additive) group, and let `M` be a submonoid of `G`.
The *support* of `M` is `M ∩ -M`, the largest subgroup of `G` contained in `M`.
A submonoid `C` is *pointed*, or a *positive cone*, if it has zero support.
A submonoid `C` is *spanning* if `M ∪ -M = G`.

The names for these concepts are taken from the theory of convex cones.

## Main definitions

* `AddSubmonoid.support`: the support of a submonoid.
* `AddSubmonoid.IsPointed`: a submonoid with zero support.
* `AddSubmonoid.IsSpanning`: a submonoid satisfying `M ∪ -M = G`.

-/

@[expose] public section

namespace Submonoid

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

/--
The support of a submonoid `M` of a group `G` is `M ∩ M⁻¹`,
the largest subgroup of `G` contained in `M`.
-/
@[to_additive (attr := simps!)
/-- The support of a submonoid `M` of a group `G` is `M ∩ -M`,
the largest subgroup of `G` contained in `M`. -/]
def mulSupport : Subgroup G where
  toSubmonoid := M ⊓ M⁻¹
  inv_mem' := by simp_all

attribute [norm_cast] coe_mulSupport AddSubmonoid.coe_support

variable {M} in
@[to_additive (attr := simp)]
theorem mem_mulSupport {x} : x ∈ M.mulSupport ↔ x ∈ M ∧ x⁻¹ ∈ M := .rfl

@[to_additive (attr := simp)]
theorem mulSupport_toSubmonoid : M.mulSupport.toSubmonoid = M ⊓ M⁻¹ := rfl

/-- The support of a submonoid is the largest subgroup it contains. -/
@[to_additive /-- The support of a submonoid is the largest subgroup it contains. -/]
theorem _root_.Subgroup.gc_toSubmonoid_mulSupport :
    GaloisConnection (α := Subgroup G) Subgroup.toSubmonoid mulSupport :=
  fun _ _ ↦ by
    rw [← Subgroup.toSubmonoid_le]
    grind [mulSupport_toSubmonoid, le_inf_iff, Submonoid.inv_le_inv, Subgroup.toSubmonoid_inv]

/-- The support of a submonoid is the largest subgroup it contains. -/
@[to_additive /-- The support of a submonoid is the largest subgroup it contains. -/]
def _root_.Subgroup.gciToSubmonoidMulSupport :
    GaloisCoinsertion (α := Subgroup G) Subgroup.toSubmonoid mulSupport :=
  Subgroup.gc_toSubmonoid_mulSupport.toGaloisCoinsertion <| by
    simp [← Subgroup.toSubmonoid_le]

/-- A submonoid is pointed if it has zero support. -/
@[to_additive /-- A submonoid is pointed if it has zero support. -/]
def IsMulPointed := ∀ x ∈ M, x⁻¹ ∈ M → x = 1

namespace IsMulPointed

variable {M}

@[to_additive (attr := deprecated "Trivially true" (since := "2026-09-28"))]
theorem mk (h : ∀ x ∈ M, x⁻¹ ∈ M → x = 1) : M.IsMulPointed := h

@[to_additive]
theorem eq_one_of_mem_of_inv_mem (hM : M.IsMulPointed)
    {x : G} (hx₁ : x ∈ M) (hx₂ : x⁻¹ ∈ M) : x = 1 := hM _ hx₁ hx₂

@[to_additive (attr := deprecated (since := "2026-09-28"))]
alias eq_one_of_mem_of_inv_mem₂ := eq_one_of_mem_of_inv_mem

@[to_additive]
theorem _root_.isMulPointed_iff_mulSupport_eq_bot : M.IsMulPointed ↔ M.mulSupport = ⊥ := by
  simp_rw [Subgroup.ext_iff, IsMulPointed, mem_mulSupport]
  grind [one_mem, inv_one, Subgroup.mem_bot]

@[to_additive (attr := simp)] alias ⟨mulSupport_eq_bot, _⟩ := isMulPointed_iff_mulSupport_eq_bot

@[to_additive] alias ⟨_, of_mulSupport_eq_bot⟩ := isMulPointed_iff_mulSupport_eq_bot

end IsMulPointed

/-- A submonoid `M` of a group `G` is spanning if `M` generates `G` as a subgroup. -/
@[to_additive
/-- A submonoid `M` of a group `G` is spanning if `M` generates `G` as a subgroup. -/]
def IsMulSpanning := ∀ a : G, a ∈ M ∨ a⁻¹ ∈ M

namespace IsMulSpanning

variable {M}

@[to_additive (attr := deprecated "Trivially true" (since := "2026-09-28"))]
theorem mk (h : ∀ a : G, a ∈ M ∨ a⁻¹ ∈ M) : M.IsMulSpanning := h

@[to_additive]
theorem mem_or_inv_mem (hM : M.IsMulSpanning) (a : G) : a ∈ M ∨ a⁻¹ ∈ M := hM a

@[to_additive]
theorem of_le {N : Submonoid G} (hM : M.IsMulSpanning) (h : M ≤ N) : N.IsMulSpanning := by
  grind [IsMulSpanning, IsConcreteLE.le_iff]

@[to_additive]
theorem maximal_isMulPointed (hMp : M.IsMulPointed) (hMs : M.IsMulSpanning) :
    Maximal IsMulPointed M := by
  grind [Maximal, IsConcreteLE.le_iff, IsMulPointed, IsMulSpanning, one_mem, inv_one]

end IsMulSpanning

variable {H : Type*} [Group H] (f : G →* H) (M N : Submonoid G) (M' : Submonoid H)

@[to_additive (attr := simp)]
theorem _root_.Subgroup.mulSupport_eq (H : Subgroup G) : H.mulSupport = H :=
  Subgroup.gciToSubmonoidMulSupport.u_l_eq H

@[to_additive (attr := simp)]
theorem mulSupport_bot : (⊥ : Submonoid G).mulSupport = ⊥ := by
  simpa using (⊥ : Subgroup G).mulSupport_eq

@[to_additive (attr := simp)]
theorem mulSupport_top : (⊤ : Submonoid G).mulSupport = ⊤ :=
  Subgroup.gc_toSubmonoid_mulSupport.u_top

variable {M N} in
@[to_additive]
theorem mulSupport_mono (h : M ≤ N) : M.mulSupport ≤ N.mulSupport :=
  Subgroup.gc_toSubmonoid_mulSupport.monotone_u h

@[to_additive (attr := simp)]
theorem mulSupport_inf : (M ⊓ N).mulSupport = M.mulSupport ⊓ N.mulSupport :=
  Subgroup.gc_toSubmonoid_mulSupport.u_inf

@[to_additive (attr := simp)]
theorem mulSupport_sInf (s : Set (Submonoid G)) :
    (sInf s).mulSupport = ⨅ M ∈ s, M.mulSupport :=
  Subgroup.gc_toSubmonoid_mulSupport.u_sInf

@[to_additive (attr := simp)]
theorem mulSupport_iInf {ι : Type*} (f : ι → Submonoid G) :
    (iInf f).mulSupport = ⨅ i, (f i).mulSupport :=
  Subgroup.gc_toSubmonoid_mulSupport.u_iInf

variable {M'} in
@[to_additive]
theorem IsMulSpanning.comap (hM' : M'.IsMulSpanning) : (M'.comap f).IsMulSpanning := by
  grind [IsMulSpanning, mem_comap]

@[to_additive (attr := simp)]
theorem mulSupport_comap : (M'.comap f).mulSupport = M'.mulSupport.comap f := by ext; simp

variable {f M} in
@[to_additive]
theorem IsMulSpanning.map (hM : M.IsMulSpanning) (hf : Function.Surjective f) :
    (M.map f).IsMulSpanning := fun x ↦ by grind [IsMulSpanning, mem_map, hf x]

@[to_additive]
theorem map_mulSupport_le : M.mulSupport.map f ≤ (M.map f).mulSupport :=
  fun _ ⟨a, _⟩ ↦ ⟨⟨a, by simp_all⟩, ⟨a⁻¹, by simp_all⟩⟩

variable {f M} in
@[to_additive]
theorem mulSupport_map (hsupp : f.ker ≤ M.mulSupport) :
    (M.map f).mulSupport = M.mulSupport.map f := by
  refine le_antisymm (fun _ ⟨⟨a, _⟩, ⟨b, ⟨hb₁, _⟩⟩⟩ ↦ ?_) (map_mulSupport_le f M)
  have : (b * a)⁻¹ * b ∈ M := mul_mem (hsupp (by simp_all)).2 hb₁
  exact ⟨a, by simp_all⟩

end Submonoid
