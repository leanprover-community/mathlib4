import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact

-- It seems I have rediscovered the point of view on "pseudoelements"
-- described in the first page of:
--
-- George Bergman, A note on abelian categories –
-- translating element-chasing proofs, and exact embedding
-- in abelian groups (1974)
-- http://math.berkeley.edu/~gbergman/papers/unpub/elem-chase.pdf
--

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type _} [Category C] [Abelian C] {X Y : C} (S : ShortComplex C)
  {S₁ S₂ : ShortComplex C}

attribute [local instance] epi_comp

-- see also `Preadditive.mono_iff_cancel_zero`

lemma epi_iff_surjective_up_to_refinements (f : X ⟶ Y) :
    Epi f ↔ ∀ ⦃A : C⦄ (a : A ⟶ Y),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (a' : A' ⟶ X), π ≫ a = a' ≫ f := by
  constructor
  . intro _ A a
    exact ⟨pullback a f, pullback.fst, inferInstance, pullback.snd, pullback.condition⟩
  . intro hf
    obtain ⟨A, π, hπ, a', fac⟩ := hf (𝟙 Y)
    rw [comp_id] at fac
    exact epi_of_epi_fac fac.symm

lemma surjective_up_to_refinements_of_epi (f : X ⟶ Y) [Epi f] :
    ∀ ⦃A : C⦄ (a : A ⟶ Y),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (a' : A' ⟶ X), π ≫ a = a' ≫ f :=
  (epi_iff_surjective_up_to_refinements f).1 inferInstance

lemma ShortComplex.exact_iff_exact_up_to_refinements :
    S.Exact ↔ ∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂) (_ : x₂ ≫ S.g = 0),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  rw [S.exact_iff_epi_toCycles, epi_iff_surjective_up_to_refinements]
  constructor
  . intro hS
    intro _ a ha
    obtain ⟨A', π, hπ, x₁, fac⟩ := hS (S.liftCycles a ha)
    exact ⟨A', π, hπ, x₁, by simpa only [assoc, liftCycles_i, toCycles_i] using fac =≫ S.iCycles⟩
  . intro hS
    intro _ a
    obtain ⟨A', π, hπ, x₁, fac⟩ := hS (a ≫ S.iCycles) (by simp)
    exact ⟨A', π, hπ, x₁, by simp only [← cancel_mono S.iCycles, assoc, toCycles_i, fac]⟩

variable {S}

lemma ShortComplex.Exact.exact_up_to_refinements (hS : S.Exact) :
    ∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂) (_ : x₂ ≫ S.g = 0),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  simpa only [ShortComplex.exact_iff_exact_up_to_refinements] using hS

variable (S)

lemma Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements {f : X ⟶ Y}
    {c : CokernelCofork f} (hc : IsColimit c) {A : C} (y : A ⟶ Y) :
    y ≫ c.π = 0 ↔ ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f := by
  constructor
  . intro hy
    let T := ShortComplex.mk _ _ c.condition
    have hT := T.exact_of_g_is_cokernel
      (IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by simp)))
    rw [T.exact_iff_exact_up_to_refinements] at hT
    obtain ⟨A', π, hπ, x₁, fac⟩ := hT y hy
    exact ⟨A', π, hπ, x₁, fac⟩
  . rintro ⟨A', π, hπ, x, fac⟩
    dsimp
    simp only [← cancel_epi π, comp_zero, reassoc_of% fac, condition]

lemma ShortComplex.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
    {A : C} (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) :
    S.liftCycles x₂ hx₂ ≫ S.homologyπ = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  constructor
  . intro h
    erw [CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
      S.homologyIsCokernel] at h
    obtain ⟨A', π, hπ, x₁, fac⟩ := h
    refine' ⟨A', π, hπ, x₁, _⟩
    simpa only [assoc, liftCycles_i, toCycles_i] using fac =≫ S.iCycles
  . intro ⟨A, π, hπ, x₁, fac⟩
    simp only [← cancel_epi π, S.comp_liftCycles_assoc, comp_zero]
    exact S.liftCycles_homologyπ_eq_zero_of_boundary _ x₁ fac

lemma ShortComplex.liftCycles_comp_homologyπ_eq_iff_up_to_refinements
    {A : C} (x₂ x₂' : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) (hx₂' : x₂' ≫ S.g = 0) :
    S.liftCycles x₂ hx₂ ≫ S.homologyπ = S.liftCycles x₂' hx₂' ≫ S.homologyπ ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = π ≫ x₂' + x₁ ≫ S.f := by
  suffices S.liftCycles x₂ hx₂ ≫ S.homologyπ = S.liftCycles x₂' hx₂' ≫ S.homologyπ ↔
      S.liftCycles (x₂ - x₂') (by simp only [sub_comp, hx₂, hx₂', sub_zero]) ≫ S.homologyπ = 0 by
    simp only [this, S.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements, comp_sub,
      sub_eq_iff_eq_add']
  rw [← sub_eq_zero, ← sub_comp, sub_liftCycles]

lemma ShortComplex.comp_homologyπ_eq_zero_iff_up_to_refinements
    {A : C} (z₂ : A ⟶ S.cycles) : z₂ ≫ S.homologyπ = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ z₂ = x₁ ≫ S.toCycles := by
  obtain ⟨x₂, hx₂, rfl⟩ : ∃ (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0), z₂ = S.liftCycles x₂ hx₂ :=
    ⟨z₂ ≫ S.iCycles, by simp, by simp only [← cancel_mono S.iCycles, liftCycles_i]⟩
  simp only [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements,
    ← cancel_mono S.iCycles, assoc, liftCycles_i, toCycles_i]

lemma ShortComplex.comp_homologyπ_eq_iff_up_to_refinements
    {A : C} (z₂ z₂' : A ⟶ S.cycles) : z₂ ≫ S.homologyπ = z₂' ≫ S.homologyπ ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁),
        π ≫ z₂ = π ≫ z₂' + x₁ ≫ S.toCycles := by
  obtain ⟨x₂, hx₂, rfl⟩ : ∃ (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0), z₂ = S.liftCycles x₂ hx₂ :=
    ⟨z₂ ≫ S.iCycles, by simp, by simp only [← cancel_mono S.iCycles, liftCycles_i]⟩
  obtain ⟨x₂', hx₂', rfl⟩ : ∃ (x₂' : A ⟶ S.X₂) (hx₂' : x₂' ≫ S.g = 0), z₂' =
    S.liftCycles x₂' hx₂' := ⟨z₂' ≫ S.iCycles, by simp,
      by simp only [← cancel_mono S.iCycles, liftCycles_i]⟩
  simp only [liftCycles_comp_homologyπ_eq_iff_up_to_refinements,
    ← cancel_mono S.iCycles, liftCycles_i, assoc, add_comp, toCycles_i]

lemma ShortComplex.eq_liftCycles_homologyπ_up_to_refinements {A : C} (γ : A ⟶ S.homology) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (z : A' ⟶ S.X₂) (hz : z ≫ S.g = 0),
      π ≫ γ = S.liftCycles z hz ≫ S.homologyπ := by
  obtain ⟨A', π, hπ, z, hz⟩ := surjective_up_to_refinements_of_epi S.homologyπ γ
  refine' ⟨A', π, hπ, z ≫ S.iCycles, by simp, _⟩
  rw [hz]
  congr 1
  rw [← cancel_mono S.iCycles, liftCycles_i]

lemma ShortComplex.mono_homologyMap_iff_up_to_refinements (φ : S₁ ⟶ S₂) :
    Mono (homologyMap φ) ↔
      ∀ ⦃A : C⦄ (x₂ : A ⟶ S₁.X₂) (_ : x₂ ≫ S₁.g = 0) (y₁ : A ⟶ S₂.X₁)
          (_ : x₂ ≫ φ.τ₂ = y₁ ≫ S₂.f),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S₁.X₁),
          π ≫ x₂ = x₁ ≫ S₁.f := by
  constructor
  . intro h A x₂ hx₂ y₁ fac
    suffices S₁.liftCycles x₂ hx₂ ≫ S₁.homologyπ = 0 by
      simpa only [S₁.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements] using this
    simp only [← cancel_mono (homologyMap φ), zero_comp, assoc,
      homologyπ_naturality, liftCycles_comp_cyclesMap_assoc,
      S₂.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements]
    exact ⟨A, 𝟙 A, inferInstance, y₁, by simpa using fac⟩
  . intro h
    rw [Preadditive.mono_iff_cancel_zero]
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
      h (π₂ ≫ z) (by rw [assoc, hz, comp_zero]) y (by simpa only [assoc] using hy)
    rw [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements]
    exact ⟨A₃, π₃ ≫ π₂, epi_comp _ _, x₁, by simpa only [assoc] using hx₁⟩

lemma ShortComplex.epi_homologyMap_iff_up_to_refinements (φ : S₁ ⟶ S₂) :
    Epi (homologyMap φ) ↔
      ∀ ⦃A : C⦄ (y₂ : A ⟶ S₂.X₂) (_ : y₂ ≫ S₂.g = 0),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₂ : A' ⟶ S₁.X₂) (_ : x₂ ≫ S₁.g = 0)
          (y₁ : A' ⟶ S₂.X₁), π ≫ y₂ = x₂ ≫ φ.τ₂ + y₁ ≫ S₂.f := by
  constructor
  . intro h
    rw [epi_iff_surjective_up_to_refinements] at h
    intro A y₂ hy₂
    obtain ⟨A₁, π₁, hπ₁, γ, hγ⟩ := h (S₂.liftCycles y₂ hy₂ ≫ S₂.homologyπ)
    obtain ⟨A₂, π₂, hπ₂, x₂, hx₂, fac⟩ := S₁.eq_liftCycles_homologyπ_up_to_refinements γ
    replace hγ := π₂ ≫= hγ
    simp only [reassoc_of% fac, homologyπ_naturality, liftCycles_comp_cyclesMap_assoc,
      comp_liftCycles_assoc, liftCycles_comp_homologyπ_eq_iff_up_to_refinements] at hγ
    obtain ⟨A₃, π₃, hπ₃, x₁, hx₁⟩ := hγ
    exact ⟨A₃, π₃ ≫ π₂ ≫ π₁, inferInstance, π₃ ≫ x₂, by simp only [assoc, hx₂, comp_zero],
      x₁, by simpa only [assoc] using hx₁⟩
  . intro h
    rw [epi_iff_surjective_up_to_refinements]
    intro A γ
    obtain ⟨A₁, π₁, hπ₁, y₂, hy₂, fac⟩ := S₂.eq_liftCycles_homologyπ_up_to_refinements γ
    obtain ⟨A₂, π₂, hπ₂, x₂, hx₂, y₁, hy₁⟩ := h y₂ hy₂
    refine' ⟨A₂, π₂ ≫ π₁, inferInstance, S₁.liftCycles x₂ hx₂ ≫ S₁.homologyπ, _⟩
    simp only [assoc, fac, homologyπ_naturality, liftCycles_comp_cyclesMap_assoc,
      comp_liftCycles_assoc, liftCycles_comp_homologyπ_eq_iff_up_to_refinements]
    exact ⟨A₂, 𝟙 _, inferInstance, y₁, by simpa only [id_comp] using hy₁⟩

lemma ShortComplex.comp_pOpcycles_eq_zero_iff_up_to_refinements
    {A : C} (x₂ : A ⟶ S.X₂) :
      x₂ ≫ S.pOpcycles = 0 ↔
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  constructor
  · exact (exact_of_g_is_cokernel (ShortComplex.mk S.f S.pOpcycles (by simp))
      (S.opcyclesIsCokernel)).exact_up_to_refinements _
  · rintro ⟨A', π, _, x₁, h⟩
    rw [← cancel_epi π, comp_zero, reassoc_of% h, f_pOpcycles, comp_zero]

end CategoryTheory
