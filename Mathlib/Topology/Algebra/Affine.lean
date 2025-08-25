/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Attila Gáspár
-/
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Topological properties of affine spaces and maps

This file defines topological torsors of additive groups and proves some basic results.
-/

open Topology

section AddTorsor

variable {V P α : Type*} [AddGroup V] [TopologicalSpace V] [AddTorsor V P] [TopologicalSpace P]

variable (P) in
/-- A topological torsor over a topological additive group is a torsor where `+ᵥ` and `-ᵥ` are
continuous. -/
class IsTopologicalAddTorsor extends ContinuousVAdd V P where
  continuous_vsub : Continuous (fun x : P × P => x.1 -ᵥ x.2)

export IsTopologicalAddTorsor (continuous_vsub)

attribute [fun_prop] continuous_vsub

variable [IsTopologicalAddTorsor P]

theorem Filter.Tendsto.vsub {l : Filter α} {f g : α → P} {x y : P} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (f -ᵥ g) l (𝓝 (x -ᵥ y)) :=
  (continuous_vsub.tendsto (x, y)).comp (hf.prodMk_nhds hg)

variable [TopologicalSpace α]

@[fun_prop]
theorem Continuous.vsub {f g : α → P} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ f x -ᵥ g x) :=
  continuous_vsub.comp₂ hf hg

@[fun_prop]
nonrec theorem ContinuousAt.vsub {f g : α → P} {x : α} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) :
    ContinuousAt (fun x ↦ f x -ᵥ g x) x :=
  hf.vsub hg

@[fun_prop]
nonrec theorem ContinuousWithinAt.vsub {f g : α → P} {x : α} {s : Set α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x ↦ f x -ᵥ g x) s x :=
  hf.vsub hg

@[fun_prop]
theorem ContinuousOn.vsub {f g : α → P} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x ↦ f x -ᵥ g x) s := fun x hx ↦
  (hf x hx).vsub (hg x hx)

include P in
variable (V P) in
/-- The underlying group of a topological torsor is a topological group. This is not an instance, as
`P` cannot be inferred. -/
theorem IsTopologicalAddTorsor.to_isTopologicalAddGroup : IsTopologicalAddGroup V where
  continuous_add := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, x]
      equals (x.1 +ᵥ x.2 +ᵥ p) -ᵥ p => rw [vadd_vadd, vadd_vsub]
    fun_prop
  continuous_neg := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, v]
      equals p -ᵥ (v +ᵥ p) => rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub]
    fun_prop

/-- The map `v ↦ v +ᵥ p` as a homeomorphism between `V` and `P`. -/
@[simps!]
def Homeomorph.vaddConst (p : P) : V ≃ₜ P where
  __ := Equiv.vaddConst p
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

section Pointwise

open Pointwise

theorem IsClosed.vadd_right_of_isCompact {s : Set V} {t : Set P} (hs : IsClosed s)
    (ht : IsCompact t) : IsClosed (s +ᵥ t) := by
  have ⟨p⟩ : Nonempty P := inferInstance
  have cont : Continuous (· -ᵥ p) := by fun_prop
  have := IsTopologicalAddTorsor.to_isTopologicalAddGroup V P
  convert (hs.add_right_of_isCompact <| ht.image cont).preimage cont
  rw [Set.eq_preimage_iff_image_eq <| by exact (Equiv.vaddConst p).symm.bijective,
    ← Set.image2_vadd, Set.image_image2, ← Set.image2_add, Set.image2_image_right]
  simp only [vadd_vsub_assoc]

end Pointwise

end AddTorsor

section AddGroup

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

instance : IsTopologicalAddTorsor G where
  toContinuousVAdd := inferInstance
  continuous_vsub := by simp only [vsub_eq_sub, sub_eq_add_neg]; fun_prop

end AddGroup

section Prod

variable
  {V W P Q : Type*}
  [AddCommGroup V] [TopologicalSpace V]
  [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]
  [AddCommGroup W] [TopologicalSpace W]
  [AddTorsor W Q] [TopologicalSpace Q] [IsTopologicalAddTorsor Q]

instance : IsTopologicalAddTorsor (P × Q) where
  continuous_vadd := Continuous.prodMk (by fun_prop) (by fun_prop)
  continuous_vsub := Continuous.prodMk (by fun_prop) (by fun_prop)

end Prod

section Pi

variable
  {ι : Type*} {V P : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, TopologicalSpace (V i)]
  [∀ i, AddTorsor (V i) (P i)] [∀ i, TopologicalSpace (P i)] [∀ i, IsTopologicalAddTorsor (P i)]

instance : IsTopologicalAddTorsor ((i : ι) → P i) where
  continuous_vadd := continuous_pi <| by simp only [Pi.vadd_apply']; fun_prop
  continuous_vsub := continuous_pi <| by simp only [Pi.vsub_apply]; fun_prop

end Pi

section Affine

variable
  {R V P W Q α : Type*}
  [AddCommGroup V] [TopologicalSpace V]
  [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]
  [AddCommGroup W] [TopologicalSpace W]
  [AddTorsor W Q] [TopologicalSpace Q] [IsTopologicalAddTorsor Q]

section Ring

variable [Ring R] [Module R V] [Module R W]

attribute [local instance] AffineSubspace.toAddTorsor

instance {s : AffineSubspace R P} [Nonempty s] : IsTopologicalAddTorsor s where
  continuous_vadd := by
    rw [IsEmbedding.subtypeVal.continuous_iff, Function.comp_def]
    fun_prop
  continuous_vsub := by
    rw [IsEmbedding.subtypeVal.continuous_iff, Function.comp_def]
    fun_prop

theorem AffineSubspace.isClosed_direction_iff [T1Space W] (s : AffineSubspace R Q) :
    IsClosed (s.direction : Set W) ↔ IsClosed (s : Set Q) := by
  rcases s.eq_bot_or_nonempty with (rfl | ⟨x, hx⟩); · simp
  rw [← (Homeomorph.vaddConst x).symm.isClosed_image,
    AffineSubspace.coe_direction_eq_vsub_set_right hx]
  rfl

/-- If `f` is an affine map, then its linear part is continuous iff `f` is continuous. -/
theorem AffineMap.continuous_linear_iff {f : P →ᵃ[R] Q} : Continuous f.linear ↔ Continuous f := by
  inhabit P
  have :
    (f.linear : V → W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_continuous_iff, Homeomorph.comp_continuous_iff']

/-- An affine map is continuous iff its underlying linear map is continuous. See also
`AffineMap.continuous_linear_iff`. -/
@[deprecated AffineMap.continuous_linear_iff (since := "2025-08-15")]
theorem AffineMap.continuous_iff {f : P →ᵃ[R] Q} : Continuous f ↔ Continuous f.linear :=
  continuous_linear_iff.symm

/-- If `f` is an affine map, then its linear part is an open map iff `f` is an open map. -/
theorem AffineMap.isOpenMap_linear_iff {f : P →ᵃ[R] Q} : IsOpenMap f.linear ↔ IsOpenMap f := by
  inhabit P
  have :
    (f.linear : V → W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_isOpenMap_iff, Homeomorph.comp_isOpenMap_iff']

variable [TopologicalSpace R] [ContinuousSMul R V]

/-- The line map is continuous. -/
@[continuity]
theorem AffineMap.lineMap_continuous {p q : P} :
    Continuous (lineMap p q : R →ᵃ[R] P) := by
  eta_expand
  simp only [lineMap_apply]
  fun_prop

theorem Filter.Tendsto.lineMap {l : Filter α} {f₁ f₂ : α → P} {g : α → R} {p₁ p₂ : P} {c : R}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) l (𝓝 <| AffineMap.lineMap p₁ p₂ c) :=
  (hg.smul (h₂.vsub h₁)).vadd h₁

theorem Filter.Tendsto.midpoint [Invertible (2 : R)] {l : Filter α} {f₁ f₂ : α → P} {p₁ p₂ : P}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) :
    Tendsto (fun x => midpoint R (f₁ x) (f₂ x)) l (𝓝 <| midpoint R p₁ p₂) :=
  h₁.lineMap h₂ tendsto_const_nhds

end Ring

section CommRing

variable [CommRing R] [Module R V] [ContinuousConstSMul R V]

@[continuity]
theorem AffineMap.homothety_continuous (x : P) (t : R) :
    Continuous <| homothety x t := by
  eta_expand
  simp only [homothety_apply]
  fun_prop

open AffineMap

variable (R) [TopologicalSpace R] [Module R W] [ContinuousSMul R W]

theorem eventually_homothety_mem_of_mem_interior (x : Q) {s : Set Q} {y : Q} (hy : y ∈ interior s) :
    ∀ᶠ δ in 𝓝 (1 : R), homothety x δ y ∈ s := by
  have cont : Continuous (fun δ : R => homothety x δ y) := by
    simp only [homothety_apply]
    fun_prop
  filter_upwards [cont.tendsto' 1 y (by simp) |>.eventually (isOpen_interior.eventually_mem hy)]
    with _ h using interior_subset h

theorem eventually_homothety_image_subset_of_finite_subset_interior (x : Q) {s : Set Q} {t : Set Q}
    (ht : t.Finite) (h : t ⊆ interior s) : ∀ᶠ δ in 𝓝 (1 : R), homothety x δ '' t ⊆ s := by
  suffices ∀ y ∈ t, ∀ᶠ δ in 𝓝 (1 : R), homothety x δ y ∈ s by
    simp only [Set.image_subset_iff]
    exact (Filter.eventually_all_finite ht).mpr this
  intro y hy
  exact eventually_homothety_mem_of_mem_interior R x (h hy)

end CommRing

section Field

variable [Field R] [Module R V] [ContinuousConstSMul R V]

theorem AffineMap.homothety_isOpenMap (x : P) (t : R) (ht : t ≠ 0) :
    IsOpenMap <| homothety x t := by
  apply IsOpenMap.of_inverse (homothety_continuous x t⁻¹) <;> intro e <;>
    simp [← AffineMap.comp_apply, ← homothety_mul, ht]

end Field

end Affine
