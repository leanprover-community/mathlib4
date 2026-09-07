/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Invertibility of continuous linear maps

In this file, we define the predicate `ContinuousLinearMap.IsInvertible`, expressing that a given
continuous (semi)linear map is the forward direction of a `ContinuousLinearEquiv` (in other words,
it has a continuous inverse).
-/

@[expose] public section

open scoped Ring

namespace ContinuousLinearMap

variable {R : Type*} {M M₂ M₃ : Type*}
  [TopologicalSpace M] [TopologicalSpace M₂] [TopologicalSpace M₃]

variable [Semiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid M₃] [Module R M₃]

/-- A continuous linear map is invertible if it is the forward direction of a continuous linear
equivalence. -/
def IsInvertible (f : M →L[R] M₂) : Prop :=
  ∃ (A : M ≃L[R] M₂), A = f

open scoped Classical in
/-- Introduce a function `inverse` from `M →L[R] M₂` to `M₂ →L[R] M`, which sends `f` to `f.symm` if
`f` is a continuous linear equivalence and to `0` otherwise.  This definition is somewhat ad hoc,
but one needs a fully (rather than partially) defined inverse function for some purposes, including
for calculus. -/
noncomputable def inverse : (M →L[R] M₂) → M₂ →L[R] M := fun f =>
  if h : f.IsInvertible then ((Classical.choose h).symm : M₂ →L[R] M) else 0

@[simp] lemma isInvertible_equiv {f : M ≃L[R] M₂} : IsInvertible (f : M →L[R] M₂) := ⟨f, rfl⟩

/-- By definition, if `f` is invertible then `inverse f = f.symm`. -/
@[simp]
theorem inverse_equiv (e : M ≃L[R] M₂) : inverse (e : M →L[R] M₂) = e.symm := by
  simp [inverse]

/-- By definition, if `f` is not invertible then `inverse f = 0`. -/
@[simp] lemma inverse_of_not_isInvertible
    {f : M →L[R] M₂} (hf : ¬ f.IsInvertible) : f.inverse = 0 :=
  dite_eq_right hf

lemma IsInvertible.of_inverse {f : M →L[R] M₂} {g : M₂ →L[R] M}
    (hf : f ∘L g = .id R M₂) (hg : g ∘L f = .id R M) :
    f.IsInvertible :=
  ⟨ContinuousLinearEquiv.equivOfInverse' _ _ hf hg, rfl⟩

lemma inverse_eq {f : M →L[R] M₂} {g : M₂ →L[R] M}
    (hf : f ∘L g = .id R M₂) (hg : g ∘L f = .id R M) :
    f.inverse = g := by
  rw [← ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse' f g hf hg, inverse_equiv]
  simp

@[simp]
theorem isInvertible_zero_iff :
    IsInvertible (0 : M →L[R] M₂) ↔ Subsingleton M ∧ Subsingleton M₂ := by
  refine ⟨fun ⟨e, he⟩ ↦ ?_, ?_⟩
  · have A : Subsingleton M := by
      refine ⟨fun x y ↦ e.injective ?_⟩
      simp [he, ← ContinuousLinearEquiv.coe_coe]
    exact ⟨A, e.toEquiv.symm.subsingleton⟩
  · rintro ⟨hM, hM₂⟩
    refine .of_inverse (g := 0) ?_ ?_ <;> exact Subsingleton.elim _ _

@[simp] theorem inverse_zero : inverse (0 : M →L[R] M₂) = 0 := by
  by_cases h : IsInvertible (0 : M →L[R] M₂)
  · rcases isInvertible_zero_iff.1 h with ⟨hM, hM₂⟩
    exact Subsingleton.elim _ _
  · exact inverse_of_not_isInvertible h

lemma IsInvertible.comp {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hg : g.IsInvertible) (hf : f.IsInvertible) : (g ∘L f).IsInvertible := by
  rcases hg with ⟨N, rfl⟩
  rcases hf with ⟨M, rfl⟩
  exact ⟨M.trans N, rfl⟩

lemma IsInvertible.inverse_apply_eq {f : M →L[R] M₂} {x : M} {y : M₂} (hf : f.IsInvertible) :
    f.inverse y = x ↔ y = f x := by
  rcases hf with ⟨M, rfl⟩
  simp only [inverse_equiv, ContinuousLinearEquiv.coe_coe]
  exact ContinuousLinearEquiv.symm_apply_eq M

@[simp] lemma isInvertible_equiv_comp {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂} :
    ((e : M₂ →L[R] M₃) ∘L f).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = e.symm ∘L ((e : M₂ →L[R] M₃) ∘L f) := by ext; simp
    rw [this, ← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma isInvertible_comp_equiv {e : M₃ ≃L[R] M} {f : M →L[R] M₂} :
    (f ∘L (e : M₃ →L[R] M)).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = (f ∘L (e : M₃ →L[R] M)) ∘L e.symm := by ext; simp
    rw [this, ← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma inverse_equiv_comp {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂} :
    (e ∘L f).inverse = f.inverse ∘L (e.symm : M₃ →L[R] M₂) := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, zero_comp]

@[simp] lemma inverse_comp_equiv {e : M₃ ≃L[R] M} {f : M →L[R] M₂} :
    (f ∘L e).inverse = (e.symm : M →L[R] M₃) ∘L f.inverse := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, comp_zero]

lemma IsInvertible.inverse_comp_of_left {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hg : g.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hg with ⟨N, rfl⟩
  simp

lemma IsInvertible.inverse_comp_apply_of_left {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : M₃}
    (hg : g.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hg.inverse_comp_of_left, comp_apply]

lemma IsInvertible.inverse_comp_of_right {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hf : f.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hf with ⟨M, rfl⟩
  simp

lemma IsInvertible.inverse_comp_apply_of_right {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : M₃}
    (hf : f.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hf.inverse_comp_of_right, comp_apply]

@[simp]
theorem ringInverse_equiv (e : M ≃L[R] M) : (↑e)⁻¹ʳ = inverse (e : M →L[R] M) := by
  suffices ((ContinuousLinearEquiv.unitsEquiv _ _).symm e : M →L[R] M)⁻¹ʳ = inverse ↑e by
    convert! this
  simp
  rfl

/-- The function `ContinuousLinearEquiv.inverse` can be written in terms of `Ring.inverse` for the
ring of self-maps of the domain. -/
theorem inverse_eq_ringInverse (e : M ≃L[R] M₂) (f : M →L[R] M₂) :
    inverse f = ((e.symm : M₂ →L[R] M).comp f)⁻¹ʳ ∘L e.symm := by
  by_cases h₁ : f.IsInvertible
  · obtain ⟨e', he'⟩ := h₁
    rw [← he']
    change _ = (e'.trans e.symm : M →L[R] M)⁻¹ʳ ∘L (e.symm : M₂ →L[R] M)
    ext
    simp
  · suffices ¬IsUnit ((e.symm : M₂ →L[R] M).comp f) by simp [this, h₁]
    contrapose h₁
    rcases h₁ with ⟨F, hF⟩
    use (ContinuousLinearEquiv.unitsEquiv _ _ F).trans e
    ext
    dsimp
    rw [hF]
    simp

theorem ringInverse_eq_inverse : Ring.inverse = inverse (R := R) (M := M) := by
  ext
  simp [inverse_eq_ringInverse (ContinuousLinearEquiv.refl R M)]

@[simp] theorem inverse_id : (ContinuousLinearMap.id R M).inverse = .id R M := by
  rw [← ringInverse_eq_inverse]
  exact Ring.inverse_one _

namespace IsInvertible

variable {f : M →L[R] M₂}

@[simp]
theorem self_comp_inverse (hf : f.IsInvertible) : f ∘L f.inverse = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
theorem self_apply_inverse (hf : f.IsInvertible) (y : M₂) : f (f.inverse y) = y := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
theorem inverse_comp_self (hf : f.IsInvertible) : f.inverse ∘L f = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
theorem inverse_apply_self (hf : f.IsInvertible) (y : M) : f.inverse (f y) = y := by
  rcases hf with ⟨e, rfl⟩
  simp

protected theorem bijective (hf : f.IsInvertible) : Function.Bijective f := by
  rcases hf with ⟨e, rfl⟩
  simp [ContinuousLinearEquiv.bijective]

protected theorem injective (hf : f.IsInvertible) : Function.Injective f :=
  hf.bijective.injective

protected theorem surjective (hf : f.IsInvertible) : Function.Surjective f :=
  hf.bijective.surjective

protected theorem inverse (hf : f.IsInvertible) : f.inverse.IsInvertible := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
protected theorem inverse_inverse (hf : f.IsInvertible) : f.inverse.inverse = f := by
  rcases hf with ⟨e, rfl⟩
  simp

protected theorem of_isInvertible_inverse (hf : f.inverse.IsInvertible) : f.IsInvertible := by
  by_contra H
  obtain ⟨_, _⟩ : Subsingleton M₂ ∧ Subsingleton M := by simpa [inverse, H] using hf
  simp_all [Subsingleton.elim f 0]

end IsInvertible

@[simp]
theorem isInvertible_inverse_iff {f : M →L[R] M₂} :
    f.inverse.IsInvertible ↔ f.IsInvertible :=
  ⟨.of_isInvertible_inverse, .inverse⟩

theorem isInvertible_iff_isHomeomorph {f : M →L[R] M₂} :
    f.IsInvertible ↔ IsHomeomorph f :=
  ⟨fun ⟨e, he⟩ ↦ he ▸ e.isHomeomorph,
    fun hf ↦ ⟨.ofIsHomeomorph (.ofBijective f.toLinearMap hf.bijective) hf, rfl⟩⟩

alias ⟨IsInvertible.isHomeomorph, IsInvertible.of_isHomeomorph⟩ := isInvertible_iff_isHomeomorph

end ContinuousLinearMap
