/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
module

-- public import Mathlib.LinearAlgebra.Basis.Basic
-- public import Mathlib.LinearAlgebra.BilinearMap
-- public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Sesquilinear maps

This file provides properties about sesquilinear maps and forms. The maps considered are of the
form `M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M`, where `I₁ : R₁ →+* R` and `I₂ : R₂ →+* R` are ring homomorphisms and
`M₁` is a module over `R₁`, `M₂` is a module over `R₂` and `M` is a module over `R`.
Sesquilinear forms are the special case that `M₁ = M₂`, `M = R₁ = R₂ = R`, and `I₁ = RingHom.id R`.
Taking additionally `I₂ = RingHom.id R`, then one obtains bilinear forms.

Sesquilinear maps are a special case of the bilinear maps defined in `BilinearMap.lean`, and many
basic lemmas about construction and elementary calculations are found there.

## Main declarations

* `IsSymm`, `IsAlt`: states that a sesquilinear form is symmetric and alternating, respectively
* `orthogonalBilin` provides the orthogonal complement with respect to a sesquilinear map

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form, Sesquilinear map
-/

@[expose] public section

open Module

variable {R R₁ R₂ M M₁ M₂ : Type*}

namespace Submodule

/-! ### The orthogonal complement -/

variable [CommSemiring R] [CommSemiring R₁] [CommSemiring R₂]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R₁ M₁]
variable [AddCommMonoid M₂] [Module R₂ M₂]
variable {I₁ : R₁ →+* R} {I₂ : R₂ →+* R}
variable {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M}
variable {S T : Submodule R₁ M₁}

variable (B S) in
/-- The orthogonal complement of a submodule `N` with respect to some bilinear map is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear maps this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonalBilin : Submodule R₂ M₂ where
  carrier := {y | ∀ x ∈ S, B x y = 0}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by simp [hu _ hx, hv _ hx]
  smul_mem' c y hy x hx := by simp [hy _ hx]

@[simp] theorem mem_orthogonalBilin {m : M₂} :
  m ∈ S.orthogonalBilin B ↔ ∀ n ∈ S, B n m = 0 := .rfl

@[simp high] theorem mem_orthogonalBilin_span (s : Set M₁) {y : M₂} :
    y ∈ orthogonalBilin B (span R₁ s) ↔ ∀ ⦃x⦄, x ∈ s → B x y = 0 := by
  constructor <;> intro h x hx
  · exact h _ (subset_span hx)
  induction hx using span_induction with
  | mem _ hxs => exact h hxs
  | zero => simp
  | add _ _ _ _ hy hz => simp [hy, hz]
  | smul _ _ _ hy => simp [hy]

theorem orthogonalBilin_le (h : S ≤ T) : T.orthogonalBilin B ≤ S.orthogonalBilin B :=
  fun _ hn l hl ↦ hn l (h hl)

variable {I₂ : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}

theorem le_orthogonalBilin_orthogonalBilin (b : B.IsRefl) :
    S ≤ (S.orthogonalBilin B).orthogonalBilin B := fun n hn _m hm ↦ b _ _ (hm n hn)













end Submodule










namespace LinearMap

section Orthogonal

variable {K K₁ V V₁ V₂ : Type*}

variable [Field K] [AddCommGroup V] [Module K V] [Field K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [AddCommGroup V₂] [Module K V₂] {J : K →+* K} {J₁ : K₁ →+* K} {J₁' : K₁ →+* K}

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
theorem span_singleton_inf_orthogonal_eq_bot (B : V₁ →ₛₗ[J₁] V₁ →ₛₗ[J₁'] V₂) (x : V₁)
    (hx : B x x ≠ 0) : (K₁ ∙ x) ⊓ Submodule.orthogonalBilin B  (K₁ ∙ x)= ⊥ := by
  rw [← Finset.coe_singleton]
  refine eq_bot_iff.2 fun y h ↦ ?_
  obtain ⟨μ, -, rfl⟩ := Submodule.mem_span_finset.1 h.1
  replace h := h.2 x (by simp [Submodule.mem_span] : x ∈ Submodule.span K₁ ({x} : Finset V₁))
  rw [Finset.sum_singleton] at h ⊢
  suffices hμzero : μ x = 0 by rw [hμzero, zero_smul, Submodule.mem_bot]
  rw [map_smulₛₗ] at h
  exact Or.elim (smul_eq_zero.mp h)
      (fun y ↦ by simpa using y)
      (fun hfalse ↦ False.elim <| hx hfalse)

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
theorem orthogonal_span_singleton_eq_to_lin_ker {B : V →ₗ[K] V →ₛₗ[J] V₂} (x : V) :
    Submodule.orthogonalBilin B (K ∙ x) = LinearMap.ker (B x) := by
  ext y
  simp_rw [Submodule.mem_orthogonalBilin, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h ↦ h x ⟨1, one_smul _ _⟩
  · rintro h _ ⟨z, rfl⟩
    rw [map_smulₛₗ₂, smul_eq_zero]
    exact Or.intro_right _ h

-- todo: Generalize this to sesquilinear maps
theorem span_singleton_sup_orthogonal_eq_top {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : B x x ≠ 0) :
    (K ∙ x) ⊔ Submodule.orthogonalBilin B (K ∙ x) = ⊤ := by
  rw [orthogonal_span_singleton_eq_to_lin_ker]
  exact (B x).span_singleton_sup_ker_eq_top hx

-- todo: Generalize this to sesquilinear maps
/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
theorem isCompl_span_singleton_orthogonal {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : B x x ≠ 0) :
    IsCompl (K ∙ x) (Submodule.orthogonalBilin B (K ∙ x)) :=
  { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot B x hx
    codisjoint := codisjoint_iff.2 <| span_singleton_sup_orthogonal_eq_top hx }

end Orthogonal

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁] {I I' : R →+* R}

/-- The restriction of a reflexive bilinear map `B` onto a submodule `W` is
nondegenerate if `W` has trivial intersection with its orthogonal complement,
that is `Disjoint W (W.orthogonalBilin B)`. -/
theorem nondegenerate_restrict_of_disjoint_orthogonal {B : M →ₗ[R] M →ₗ[R] M₁} (hB : B.IsRefl)
    {W : Submodule R M} (hW : Disjoint W (W.orthogonalBilin B)) :
    (B.domRestrict₁₂ W W).Nondegenerate := by
  rw [(hB.domRestrict W).nondegenerate_iff_separatingLeft]
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero, ← Submodule.mem_bot R]
  refine hW.le_bot ⟨hx, fun y hy ↦ ?_⟩
  specialize b₁ ⟨y, hy⟩
  simp_rw [domRestrict₁₂_apply] at b₁
  exact hB.eq_zero b₁

end CommRing

end LinearMap
