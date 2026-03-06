/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Refinements

In order to prove injectivity/surjectivity/exactness properties for diagrams
in the category of abelian groups, we often need to do diagram chases.
Some of these can be carried out in more general abelian categories:
for example, a morphism `X ⟶ Y` in an abelian category `C` is a
monomorphism if and only if for all `A : C`, the induced map
`(A ⟶ X) → (A ⟶ Y)` of abelian groups is a monomorphism, i.e. injective.
Alternatively, the Yoneda presheaf functor which sends `X` to the
presheaf of maps `A ⟶ X` for all `A : C` preserves and reflects
monomorphisms.

However, if `p : X ⟶ Y` is an epimorphism in `C` and `A : C`,
`(A ⟶ X) → (A ⟶ Y)` may fail to be surjective (unless `p` is a split
epimorphism).

In this file, the basic result is `epi_iff_surjective_up_to_refinements`
which states that if `f : X ⟶ Y` is a morphism in an abelian category,
then it is an epimorphism if and only if for all `y : A ⟶ Y`,
there exists an epimorphism `π : A' ⟶ A` and `x : A' ⟶ X` such
that `π ≫ y = x ≫ f`. In other words, if we allow a precomposition
with an epimorphism, we may lift a morphism to `Y` to a morphism to `X`.
Following unpublished notes by George Bergman, we shall say that the
precomposition by an epimorphism `π ≫ y` is a refinement of `y`. Then,
we get that an epimorphism is a morphism that is "surjective up to refinements".
(This result is similar to the fact that a morphism of sheaves on
a topological space or a site is epi iff sections can be lifted
locally. Then, arguing "up to refinements" is very similar to
arguing locally for a Grothendieck topology (TODO: indeed,
show that it corresponds to the "refinements" topology on an
abelian category `C` that is defined by saying that
a sieve is covering if it contains an epimorphism)).

Similarly, it is possible to show that a short complex in an abelian
category is exact if and only if it is exact up to refinements
(see `ShortComplex.exact_iff_exact_up_to_refinements`).

As it is outlined in the documentation of the file
`Mathlib/CategoryTheory/Abelian/Pseudoelements.lean`, the Freyd-Mitchell
embedding theorem implies the existence of a faithful and exact functor `ι`
from an abelian category `C` to the category of abelian groups. If we
define a pseudo-element of `X : C` to be an element in `ι.obj X`, one
may do diagram chases in any abelian category using these pseudo-elements.
However, using this approach would require proving this embedding theorem!
Currently, mathlib contains a weaker notion of pseudo-elements
`Mathlib/CategoryTheory/Abelian/Pseudoelements.lean`. Some theorems can be obtained
using this notion, but there is the issue that for this notion
of pseudo-elements a morphism `X ⟶ Y` in `C` is not determined by
its action on pseudo-elements (see also `Counterexamples/Pseudoelement.lean`).
On the contrary, the approach consisting of working up to refinements
does not require the introduction of other types: we only need to work
with morphisms `A ⟶ X` in `C` which we may consider as being
"sort of elements of `X`". One may carry diagram-chasing by tracking
these morphisms and sometimes introducing an auxiliary epimorphism `A' ⟶ A`.

## References
* George Bergman, A note on abelian categories – translating element-chasing proofs,
  and exact embedding in abelian groups (1974)
  http://math.berkeley.edu/~gbergman/papers/unpub/elem-chase.pdf

-/

public section

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type*} [Category* C] [Abelian C] {X Y : C} (S : ShortComplex C)
  {S₁ S₂ : ShortComplex C}

lemma epi_iff_surjective_up_to_refinements (f : X ⟶ Y) :
    Epi f ↔ ∀ ⦃A : C⦄ (y : A ⟶ Y),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f := by
  constructor
  · intro _ A a
    exact ⟨pullback a f, pullback.fst a f, inferInstance, pullback.snd a f, pullback.condition⟩
  · intro hf
    obtain ⟨A, π, hπ, a', fac⟩ := hf (𝟙 Y)
    rw [comp_id] at fac
    exact epi_of_epi_fac fac.symm

lemma surjective_up_to_refinements_of_epi (f : X ⟶ Y) [Epi f] {A : C} (y : A ⟶ Y) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f :=
  (epi_iff_surjective_up_to_refinements f).1 inferInstance y

lemma ShortComplex.exact_iff_exact_up_to_refinements :
    S.Exact ↔ ∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂) (_ : x₂ ≫ S.g = 0),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  rw [S.exact_iff_epi_toCycles, epi_iff_surjective_up_to_refinements]
  constructor
  · intro hS A a ha
    obtain ⟨A', π, hπ, x₁, fac⟩ := hS (S.liftCycles a ha)
    exact ⟨A', π, hπ, x₁, by simpa only [assoc, liftCycles_i, toCycles_i] using fac =≫ S.iCycles⟩
  · intro hS A a
    obtain ⟨A', π, hπ, x₁, fac⟩ := hS (a ≫ S.iCycles) (by simp)
    exact ⟨A', π, hπ, x₁, by simp only [← cancel_mono S.iCycles, assoc, toCycles_i, fac]⟩

variable {S}

lemma ShortComplex.Exact.exact_up_to_refinements
    (hS : S.Exact) {A : C} (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hS
  exact hS x₂ hx₂

lemma ShortComplex.eq_liftCycles_homologyπ_up_to_refinements {A : C} (γ : A ⟶ S.homology) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (z : A' ⟶ S.X₂) (hz : z ≫ S.g = 0),
      π ≫ γ = S.liftCycles z hz ≫ S.homologyπ := by
  obtain ⟨A', π, hπ, z, hz⟩ := surjective_up_to_refinements_of_epi S.homologyπ γ
  refine ⟨A', π, hπ, z ≫ S.iCycles, by simp, ?_⟩
  rw [hz]
  congr 1
  rw [← cancel_mono S.iCycles, liftCycles_i]

set_option backward.isDefEq.respectTransparency false in
lemma Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements {f : X ⟶ Y}
    {c : CokernelCofork f} (hc : IsColimit c) {A : C} (y : A ⟶ Y) :
    y ≫ c.π = 0 ↔ ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f := by
  refine ⟨fun hy ↦ ?_, ?_⟩
  · have h := (ShortComplex.mk _ _ c.condition).exact_of_g_is_cokernel
      (IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by simp)))
    rw [ShortComplex.exact_iff_exact_up_to_refinements] at h
    obtain ⟨A', π, hπ, x₁, fac⟩ := h y hy
    exact ⟨A', π, hπ, x₁, fac⟩
  · rintro ⟨A', π, hπ, x, fac⟩
    simp [← cancel_epi π, reassoc_of% fac, condition]

set_option backward.isDefEq.respectTransparency false in
lemma ShortComplex.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
    {A : C} (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) :
    S.liftCycles x₂ hx₂ ≫ S.homologyπ = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  have := CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
        S.homologyIsCokernel (S.liftCycles x₂ hx₂)
  dsimp at this
  simp [this, ← cancel_mono S.iCycles]

lemma ShortComplex.liftCycles_comp_homologyπ_eq_iff_up_to_refinements
    {A : C} (x₂ x₂' : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) (hx₂' : x₂' ≫ S.g = 0) :
    S.liftCycles x₂ hx₂ ≫ S.homologyπ = S.liftCycles x₂' hx₂' ≫ S.homologyπ ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = π ≫ x₂' + x₁ ≫ S.f := by
  suffices S.liftCycles x₂ hx₂ ≫ S.homologyπ = S.liftCycles x₂' hx₂' ≫ S.homologyπ ↔
      S.liftCycles (x₂ - x₂') (by simp [hx₂, hx₂']) ≫ S.homologyπ = 0 by
    simp [this, S.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements,
      sub_eq_iff_eq_add']
  rw [← sub_eq_zero, ← sub_comp, sub_liftCycles]

lemma ShortComplex.comp_homologyπ_eq_zero_iff_up_to_refinements
    {A : C} (z₂ : A ⟶ S.cycles) :
    z₂ ≫ S.homologyπ = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ z₂ = x₁ ≫ S.toCycles := by
  obtain ⟨x₂, hx₂, rfl⟩ : ∃ (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0), z₂ = S.liftCycles x₂ hx₂ :=
    ⟨z₂ ≫ S.iCycles, by simp, by simp [← cancel_mono S.iCycles, liftCycles_i]⟩
  simp [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements, ← cancel_mono S.iCycles]

lemma ShortComplex.comp_homologyπ_eq_iff_up_to_refinements
    {A : C} (z₂ z₂' : A ⟶ S.cycles) :
    z₂ ≫ S.homologyπ = z₂' ≫ S.homologyπ ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁),
        π ≫ z₂ = π ≫ z₂' + x₁ ≫ S.toCycles := by
  obtain ⟨x₂, hx₂, rfl⟩ : ∃ (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0), z₂ = S.liftCycles x₂ hx₂ :=
    ⟨z₂ ≫ S.iCycles, by simp, by simp [← cancel_mono S.iCycles]⟩
  obtain ⟨x₂', hx₂', rfl⟩ : ∃ (x₂' : A ⟶ S.X₂) (hx₂' : x₂' ≫ S.g = 0), z₂' =
    S.liftCycles x₂' hx₂' := ⟨z₂' ≫ S.iCycles, by simp,
      by simp [← cancel_mono S.iCycles]⟩
  simp [liftCycles_comp_homologyπ_eq_iff_up_to_refinements, ← cancel_mono S.iCycles]

lemma ShortComplex.comp_pOpcycles_eq_zero_iff_up_to_refinements
    {A : C} (x₂ : A ⟶ S.X₂) :
    x₂ ≫ S.pOpcycles = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f :=
  CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
    S.opcyclesIsCokernel x₂

variable {K L} in
lemma ShortComplex.mono_homologyMap_iff_up_to_refinements (φ : S₁ ⟶ S₂) :
    Mono (homologyMap φ) ↔
      ∀ ⦃A : C⦄ (x₂ : A ⟶ S₁.X₂) (_ : x₂ ≫ S₁.g = 0) (y₁ : A ⟶ S₂.X₁)
          (_ : x₂ ≫ φ.τ₂ = y₁ ≫ S₂.f),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S₁.X₁),
          π ≫ x₂ = x₁ ≫ S₁.f := by
  refine ⟨fun h A x₂ hx₂ y₁ fac ↦ ?_, fun h ↦ ?_⟩
  · suffices S₁.liftCycles x₂ hx₂ ≫ S₁.homologyπ = 0 by
      rwa [← S₁.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements]
    simp only [← cancel_mono (homologyMap φ), zero_comp, assoc,
      homologyπ_naturality, liftCycles_comp_cyclesMap_assoc,
      S₂.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements]
    exact ⟨A, 𝟙 A, inferInstance, y₁, by simpa using fac⟩
  · rw [Preadditive.mono_iff_cancel_zero]
    intro A γ hγ
    obtain ⟨A₁, π₁, hπ₁, z, hz, fac⟩ := S₁.eq_liftCycles_homologyπ_up_to_refinements γ
    rw [← cancel_epi π₁, fac, comp_zero]
    replace hγ := π₁ ≫= hγ
    simp only [reassoc_of% fac, homologyπ_naturality, liftCycles_comp_cyclesMap_assoc,
      comp_zero, comp_homologyπ_eq_zero_iff_up_to_refinements] at hγ
    obtain ⟨A₂, π₂, hπ₂, y, hy⟩ := hγ
    replace hy := hy =≫ S₂.iCycles
    simp only [assoc, liftCycles_i, toCycles_i] at hy
    obtain ⟨A₃, π₃, hπ₃, x₁, hx₁⟩ :=
      h (π₂ ≫ z) (by rw [assoc, hz, comp_zero]) y (by simpa)
    rw [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements]
    exact ⟨A₃, π₃ ≫ π₂, epi_comp _ _, x₁, by simpa⟩

variable {K L} in
lemma ShortComplex.epi_homologyMap_iff_up_to_refinements (φ : S₁ ⟶ S₂) :
    Epi (homologyMap φ) ↔
      ∀ ⦃A : C⦄ (y₂ : A ⟶ S₂.X₂) (_ : y₂ ≫ S₂.g = 0),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₂ : A' ⟶ S₁.X₂) (_ : x₂ ≫ S₁.g = 0)
          (y₁ : A' ⟶ S₂.X₁), π ≫ y₂ = x₂ ≫ φ.τ₂ + y₁ ≫ S₂.f := by
  rw [epi_iff_surjective_up_to_refinements]
  constructor
  · intro h A y₂ hy₂
    obtain ⟨A₁, π₁, hπ₁, γ, hγ⟩ := h (S₂.liftCycles y₂ hy₂ ≫ S₂.homologyπ)
    obtain ⟨A₂, π₂, hπ₂, x₂, hx₂, fac⟩ := S₁.eq_liftCycles_homologyπ_up_to_refinements γ
    replace hγ := π₂ ≫= hγ
    simp only [reassoc_of% fac, homologyπ_naturality, liftCycles_comp_cyclesMap_assoc,
      comp_liftCycles_assoc, liftCycles_comp_homologyπ_eq_iff_up_to_refinements] at hγ
    obtain ⟨A₃, π₃, hπ₃, x₁, hx₁⟩ := hγ
    exact ⟨A₃, π₃ ≫ π₂ ≫ π₁, inferInstance, π₃ ≫ x₂, by simp only [assoc, hx₂, comp_zero],
      x₁, by simpa only [assoc] using hx₁⟩
  · intro h A γ
    obtain ⟨A₁, π₁, hπ₁, y₂, hy₂, fac⟩ := S₂.eq_liftCycles_homologyπ_up_to_refinements γ
    obtain ⟨A₂, π₂, hπ₂, x₂, hx₂, y₁, hy₁⟩ := h y₂ hy₂
    refine ⟨A₂, π₂ ≫ π₁, inferInstance, S₁.liftCycles x₂ hx₂ ≫ S₁.homologyπ, ?_⟩
    simp only [assoc, fac, homologyπ_naturality, liftCycles_comp_cyclesMap_assoc,
      comp_liftCycles_assoc, liftCycles_comp_homologyπ_eq_iff_up_to_refinements]
    exact ⟨A₂, 𝟙 _, inferInstance, y₁, by simpa only [id_comp] using hy₁⟩

end CategoryTheory
