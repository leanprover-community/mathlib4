/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.Quotient

/-! # Exactness of a pair

* For two maps `f : M → N` and `g : N → P`, with `Zero P`,
`Function.Exact f g` says that `Set.range f = Set.preimage g {0}`

* For linear maps `f : M →ₗ[R] N`  and `g : N →ₗ[R] P`,
`Exact f g` says that `range f = ker g`

## TODO :

* add the cases of `AddMonoidHom`

* generalize to `SemilinearMap`, even `SemilinearMapClass`

* add the multiplicative case (`Function.Exact` will become `Function.AddExact`?)
-/


namespace Function

variable {R M M' N N' P P' : Type*}

section Function

variable (f : M → N) (g : N → P)

/-- The maps `f` and `g` form an exact pair :
  `g y = 0` iff `y` belongs to the image of `f` -/
def Exact [Zero P] : Prop := ∀ y, g y = 0 ↔ y ∈ Set.range f

variable {f g}

lemma Exact.apply_apply_eq_zero [Zero P] (h : Exact f g) (x : M) :
    g (f x) = 0 := (h _).mpr <| Set.mem_range_self _

lemma Exact.comp_eq_zero [Zero P] (h : Exact f g) : g.comp f = 0 :=
  funext h.apply_apply_eq_zero

lemma Exact.of_comp_of_mem_range [Zero P] (h1 : g ∘ f = 0)
    (h2 : ∀ x, g x = 0 → x ∈ Set.range f) : Exact f g :=
  fun y => Iff.intro (h2 y) <|
    Exists.rec ((forall_apply_eq_imp_iff (p := (g · = 0))).mpr (congrFun h1) y)

end Function

section LinearMap

open LinearMap

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

lemma Exact.linearMap_ker_eq (hfg : Exact f g) : ker g = range f :=
  SetLike.ext hfg

lemma _root_.LinearMap.exact_iff :
    Exact f g ↔ LinearMap.ker g = LinearMap.range f :=
  Iff.symm SetLike.ext_iff

lemma _root_.LinearMap.exact_of_comp_eq_zero_of_ker_le_range
    (h1 : g ∘ₗ f = 0) (h2 : ker g ≤ range f) : Exact f g :=
  Exact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

lemma _root_.LinearMap.exact_of_comp_of_mem_range
    (h1 : g ∘ₗ f = 0) (h2 : ∀ x, g x = 0 → x ∈ range f) : Exact f g :=
  exact_of_comp_eq_zero_of_ker_le_range h1 h2

lemma Exact.linearMap_comp_eq_zero (h : Exact f g) : g.comp f = 0 :=
  DFunLike.coe_injective h.comp_eq_zero

lemma Surjective.comp_exact_iff_exact {p : M' →ₗ[R] M} (h : Surjective p) :
    Exact (f ∘ₗ p) g ↔ Exact f g :=
  iff_of_eq <| forall_congr fun x =>
    congrArg (g x = 0 ↔ x ∈ ·) (h.range_comp f)

lemma Injective.comp_exact_iff_exact {i : P →ₗ[R] P'} (h : Injective i) :
    Exact f (i ∘ₗ g) ↔ Exact f g :=
  forall_congr' fun _ => iff_congr (LinearMap.map_eq_zero_iff _ h) Iff.rfl

lemma _root_.LinearEquiv.conj_exact_iff_exact (e : N ≃ₗ[R] N') :
    Exact (e ∘ₗ f) (g ∘ₗ (e.symm : N' →ₗ[R] N)) ↔ Exact f g := by
  simp_rw [exact_iff, ker_comp, ← e.map_eq_comap, range_comp]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

variable
    {f₁₂ : M →ₗ[R] N} {f₂₃ : N →ₗ[R] P} {g₁₂ : M' →ₗ[R] N'}
    {g₂₃ : N' →ₗ[R] P'} {e₁ : M ≃ₗ[R] M'} {e₂ : N ≃ₗ[R] N'} {e₃ : P ≃ₗ[R] P'}

lemma Exact.of_ladder_linearEquiv_of_exact
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃)
    (H : Exact f₁₂ f₂₃) : Exact g₁₂ g₂₃ := by
  rw [← LinearEquiv.eq_comp_toLinearMap_symm] at h₁₂ h₂₃
  rwa [h₁₂, h₂₃, comp_assoc, LinearEquiv.conj_exact_iff_exact,
    e₁.symm.surjective.comp_exact_iff_exact,
    e₃.injective.comp_exact_iff_exact]

lemma Exact.iff_of_ladder_linearEquiv
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) :
    Exact g₁₂ g₂₃ ↔ Exact f₁₂ f₂₃ where
  mp := have h₂₁ := (e₂.eq_toLinearMap_symm_comp (f₁₂ ∘ₗ e₁.symm) g₁₂).mpr <|
          Eq.trans (comp_assoc _ _ _).symm <|
            (e₁.comp_toLinearMap_symm_eq g₁₂ (e₂ ∘ₗ f₁₂)).mpr h₁₂.symm
        have h₃₂ := (e₃.eq_toLinearMap_symm_comp (f₂₃ ∘ₗ e₂.symm) g₂₃).mpr <|
          Eq.trans (comp_assoc _ _ _).symm <|
            (e₂.comp_toLinearMap_symm_eq g₂₃ (e₃ ∘ₗ f₂₃)).mpr h₂₃.symm
        of_ladder_linearEquiv_of_exact h₂₁ h₃₂
  mpr := of_ladder_linearEquiv_of_exact h₁₂ h₂₃

end LinearMap

section Ring

open LinearMap Submodule

variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]

/-- A necessary and sufficient condition for an exact sequence to descend to a quotient. -/
lemma Exact.exact_mapQ_iff {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hfg : Exact f g) {p q r} (hpq : p ≤ comap f q) (hqr : q ≤ comap g r) :
    Exact (mapQ p q f hpq) (mapQ q r g hqr) ↔ range g ⊓ r ≤ map g q := by
  rw [exact_iff, ← (comap_injective_of_surjective (mkQ_surjective _)).eq_iff]
  dsimp only [mapQ]
  rw [← ker_comp, range_liftQ, liftQ_mkQ, ker_comp, range_comp, comap_map_eq,
    ker_mkQ, ker_mkQ, ← hfg.linearMap_ker_eq, sup_comm,
    ← LE.le.le_iff_eq (sup_le hqr (ker_le_comap g)),
    ← comap_map_eq, ← map_le_iff_le_comap, map_comap_eq]

end Ring

end Function
