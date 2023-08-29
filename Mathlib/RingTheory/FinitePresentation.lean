/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.Ideal.QuotientOperations

#align_import ring_theory.finite_presentation from "leanprover-community/mathlib"@"da420a8c6dd5bdfb85c4ced85c34388f633bc6ff"

/-!
# Finiteness conditions in commutative algebra

In this file we define several notions of finiteness that are common in commutative algebra.

## Main declarations

- `Module.Finite`, `RingHom.Finite`, `AlgHom.Finite`
  all of these express that some object is finitely generated *as module* over some base ring.
- `Algebra.FiniteType`, `RingHom.FiniteType`, `AlgHom.FiniteType`
  all of these express that some object is finitely generated *as algebra* over some base ring.
- `Algebra.FinitePresentation`, `RingHom.FinitePresentation`, `AlgHom.FinitePresentation`
  all of these express that some object is finitely presented *as algebra* over some base ring.

-/

set_option autoImplicit true

open Function (Surjective)

open BigOperators Polynomial

section ModuleAndAlgebra

universe w₁ w₂ w₃

-- Porting Note : `M, N` is never used
variable (R : Type w₁) (A : Type w₂) (B : Type w₃)

/-- An algebra over a commutative semiring is `Algebra.FinitePresentation` if it is the quotient of
a polynomial ring in `n` variables by a finitely generated ideal. -/
def Algebra.FinitePresentation [CommSemiring R] [Semiring A] [Algebra R A] : Prop :=
  ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), Surjective f ∧ f.toRingHom.ker.FG
#align algebra.finite_presentation Algebra.FinitePresentation

namespace Algebra

variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

namespace FiniteType

variable {R A B}

/-- A finitely presented algebra is of finite type. -/
theorem of_finitePresentation : FinitePresentation R A → FiniteType R A := by
  rintro ⟨n, f, hf⟩
  -- ⊢ FiniteType R A
  apply FiniteType.iff_quotient_mvPolynomial''.2
  -- ⊢ ∃ n f, Surjective ↑f
  exact ⟨n, f, hf.1⟩
  -- 🎉 no goals
#align algebra.finite_type.of_finite_presentation Algebra.FiniteType.of_finitePresentation

end FiniteType

namespace FinitePresentation

variable {R A B}

/-- An algebra over a Noetherian ring is finitely generated if and only if it is finitely
presented. -/
theorem of_finiteType [IsNoetherianRing R] : FiniteType R A ↔ FinitePresentation R A := by
  refine' ⟨fun h => _, Algebra.FiniteType.of_finitePresentation⟩
  -- ⊢ FinitePresentation R A
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  -- ⊢ FinitePresentation R A
  refine' ⟨n, f, hf, _⟩
  -- ⊢ Ideal.FG (RingHom.ker ↑f)
  have hnoet : IsNoetherianRing (MvPolynomial (Fin n) R) := by infer_instance
  -- ⊢ Ideal.FG (RingHom.ker ↑f)
  -- Porting note: rewrote code to help typeclass inference
  rw [isNoetherianRing_iff] at hnoet
  -- ⊢ Ideal.FG (RingHom.ker ↑f)
  letI : Module (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) := Semiring.toModule
  -- ⊢ Ideal.FG (RingHom.ker ↑f)
  have := hnoet.noetherian (RingHom.ker f.toRingHom)
  -- ⊢ Ideal.FG (RingHom.ker ↑f)
  convert this
  -- 🎉 no goals
#align algebra.finite_presentation.of_finite_type Algebra.FinitePresentation.of_finiteType

/-- If `e : A ≃ₐ[R] B` and `A` is finitely presented, then so is `B`. -/
theorem equiv (hfp : FinitePresentation R A) (e : A ≃ₐ[R] B) : FinitePresentation R B := by
  obtain ⟨n, f, hf⟩ := hfp
  -- ⊢ FinitePresentation R B
  use n, AlgHom.comp (↑e) f
  -- ⊢ Surjective ↑(AlgHom.comp (↑e) f) ∧ Ideal.FG (RingHom.ker ↑(AlgHom.comp (↑e)  …
  constructor
  -- ⊢ Surjective ↑(AlgHom.comp (↑e) f)
  · rw [AlgHom.coe_comp]
    -- ⊢ Surjective (↑↑e ∘ ↑f)
    exact Function.Surjective.comp e.surjective hf.1
    -- 🎉 no goals
  suffices hker : (RingHom.ker (AlgHom.comp (e : A →ₐ[R] B) f).toRingHom) = RingHom.ker f.toRingHom
  -- ⊢ Ideal.FG (RingHom.ker ↑(AlgHom.comp (↑e) f))
  · rw [hker]
    -- ⊢ Ideal.FG (RingHom.ker ↑f)
    exact hf.2
    -- 🎉 no goals
  · have hco : (AlgHom.comp (e : A →ₐ[R] B) f).toRingHom = RingHom.comp (e.toRingEquiv : A ≃+* B)
      f.toRingHom := by
      have h : (AlgHom.comp (e : A →ₐ[R] B) f).toRingHom =
        e.toAlgHom.toRingHom.comp f.toRingHom := rfl
      have h1 : ↑e.toRingEquiv = e.toAlgHom.toRingHom := rfl
      rw [h, h1]
    rw [RingHom.ker_eq_comap_bot, hco, ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot,
      RingHom.ker_coe_equiv (AlgEquiv.toRingEquiv e), RingHom.ker_eq_comap_bot]
#align algebra.finite_presentation.equiv Algebra.FinitePresentation.equiv

variable (R)

/-- The ring of polynomials in finitely many variables is finitely presented. -/
protected theorem mvPolynomial (ι : Type u_2) [Finite ι] :
    FinitePresentation R (MvPolynomial ι R) := by
  cases nonempty_fintype ι
  -- ⊢ FinitePresentation R (MvPolynomial ι R)
  let eqv := (MvPolynomial.renameEquiv R <| Fintype.equivFin ι).symm
  -- ⊢ FinitePresentation R (MvPolynomial ι R)
  exact
    ⟨Fintype.card ι, eqv, eqv.surjective,
      ((RingHom.injective_iff_ker_eq_bot _).1 eqv.injective).symm ▸ Submodule.fg_bot⟩
#align algebra.finite_presentation.mv_polynomial Algebra.FinitePresentation.mvPolynomial

/-- `R` is finitely presented as `R`-algebra. -/
theorem self : FinitePresentation R R :=
  -- Porting note: replaced `PEmpty` with `Empty`
  equiv (FinitePresentation.mvPolynomial R Empty) (MvPolynomial.isEmptyAlgEquiv R Empty)
#align algebra.finite_presentation.self Algebra.FinitePresentation.self

/-- `R[X]` is finitely presented as `R`-algebra. -/
theorem polynomial : FinitePresentation R R[X] :=
  -- Porting note: replaced `PUnit` with `Unit`
  equiv (FinitePresentation.mvPolynomial R Unit) (MvPolynomial.pUnitAlgEquiv R)
#align algebra.finite_presentation.polynomial Algebra.FinitePresentation.polynomial

variable {R}

/-- The quotient of a finitely presented algebra by a finitely generated ideal is finitely
presented. -/
protected theorem quotient {I : Ideal A} (h : I.FG) (hfp : FinitePresentation R A) :
    FinitePresentation R (A ⧸ I) := by
  obtain ⟨n, f, hf⟩ := hfp
  -- ⊢ FinitePresentation R (A ⧸ I)
  refine' ⟨n, (Ideal.Quotient.mkₐ R I).comp f, _, _⟩
  -- ⊢ Surjective ↑(AlgHom.comp (Ideal.Quotient.mkₐ R I) f)
  · exact (Ideal.Quotient.mkₐ_surjective R I).comp hf.1
    -- 🎉 no goals
  · refine' Ideal.fg_ker_comp _ _ hf.2 _ hf.1
    -- ⊢ Ideal.FG (RingHom.ker ↑(Ideal.Quotient.mkₐ R I))
    simp [h]
    -- 🎉 no goals
#align algebra.finite_presentation.quotient Algebra.FinitePresentation.quotient

/-- If `f : A →ₐ[R] B` is surjective with finitely generated kernel and `A` is finitely presented,
then so is `B`. -/
theorem of_surjective {f : A →ₐ[R] B} (hf : Function.Surjective f) (hker : f.toRingHom.ker.FG)
    (hfp : FinitePresentation R A) : FinitePresentation R B :=
  equiv (hfp.quotient hker) (Ideal.quotientKerAlgEquivOfSurjective hf)
#align algebra.finite_presentation.of_surjective Algebra.FinitePresentation.of_surjective

theorem iff :
    FinitePresentation R A ↔
      ∃ (n : _) (I : Ideal (MvPolynomial (Fin n) R)) (_ : (_ ⧸ I) ≃ₐ[R] A), I.FG := by
  constructor
  -- ⊢ FinitePresentation R A → ∃ n I x, Ideal.FG I
  · rintro ⟨n, f, hf⟩
    -- ⊢ ∃ n I x, Ideal.FG I
    exact ⟨n, RingHom.ker f.toRingHom, Ideal.quotientKerAlgEquivOfSurjective hf.1, hf.2⟩
    -- 🎉 no goals
  · rintro ⟨n, I, e, hfg⟩
    -- ⊢ FinitePresentation R A
    exact equiv ((FinitePresentation.mvPolynomial R _).quotient hfg) e
    -- 🎉 no goals
#align algebra.finite_presentation.iff Algebra.FinitePresentation.iff

/-- An algebra is finitely presented if and only if it is a quotient of a polynomial ring whose
variables are indexed by a fintype by a finitely generated ideal. -/
theorem iff_quotient_mvPolynomial' :
    FinitePresentation R A ↔
      ∃ (ι : Type*) (_ : Fintype ι) (f : MvPolynomial ι R →ₐ[R] A),
        Surjective f ∧ f.toRingHom.ker.FG := by
  constructor
  -- ⊢ FinitePresentation R A → ∃ ι x f, Surjective ↑f ∧ Ideal.FG (RingHom.ker ↑f)
  · rintro ⟨n, f, hfs, hfk⟩
    -- ⊢ ∃ ι x f, Surjective ↑f ∧ Ideal.FG (RingHom.ker ↑f)
    set ulift_var := MvPolynomial.renameEquiv R Equiv.ulift
    -- ⊢ ∃ ι x f, Surjective ↑f ∧ Ideal.FG (RingHom.ker ↑f)
    refine'
      ⟨ULift (Fin n), inferInstance, f.comp ulift_var.toAlgHom, hfs.comp ulift_var.surjective,
        Ideal.fg_ker_comp _ _ _ hfk ulift_var.surjective⟩
    erw [RingHom.ker_coe_equiv ulift_var.toRingEquiv]
    -- ⊢ Ideal.FG ⊥
    exact Submodule.fg_bot
    -- 🎉 no goals
    -- Porting note: was
    -- convert Submodule.fg_bot
    -- exact RingHom.ker_coe_equiv ulift_var.toRingEquiv
  · rintro ⟨ι, hfintype, f, hf⟩
    -- ⊢ FinitePresentation R A
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    -- ⊢ FinitePresentation R A
    refine'
      ⟨Fintype.card ι, f.comp equiv.symm, hf.1.comp (AlgEquiv.symm equiv).surjective,
        Ideal.fg_ker_comp _ f _ hf.2 equiv.symm.surjective⟩
    erw [RingHom.ker_coe_equiv equiv.symm.toRingEquiv]
    -- ⊢ Ideal.FG ⊥
    exact Submodule.fg_bot
    -- 🎉 no goals
    -- Porting note: was
    -- convert Submodule.fg_bot
    -- exact RingHom.ker_coe_equiv equiv.symm.toRingEquiv
#align algebra.finite_presentation.iff_quotient_mv_polynomial' Algebra.FinitePresentation.iff_quotient_mvPolynomial'

-- Porting note : make universe level explicit to ensure `ι, ι'` has the same universe level
/-- If `A` is a finitely presented `R`-algebra, then `MvPolynomial (Fin n) A` is finitely presented
as `R`-algebra. -/
theorem mvPolynomial_of_finitePresentation (hfp : FinitePresentation.{w₁, w₂} R A)
    (ι : Type v) [Finite ι] :
    FinitePresentation.{w₁, max v w₂} R (MvPolynomial ι A) := by
  rw [iff_quotient_mvPolynomial'] at hfp ⊢
  -- ⊢ ∃ ι_1 x f, Surjective ↑f ∧ Ideal.FG (RingHom.ker ↑f)
  classical
  -- Porting note : use the same universe level
  obtain ⟨(ι' : Type v), _, f, hf_surj, hf_ker⟩ := hfp
  let g := (MvPolynomial.mapAlgHom f).comp (MvPolynomial.sumAlgEquiv R ι ι').toAlgHom
  cases nonempty_fintype (Sum ι ι')
  refine
    ⟨Sum ι ι', by infer_instance, g,
      (MvPolynomial.map_surjective f.toRingHom hf_surj).comp (AlgEquiv.surjective _),
      Ideal.fg_ker_comp _ _ ?_ ?_ (AlgEquiv.surjective _)⟩
  · erw [RingHom.ker_coe_equiv (MvPolynomial.sumAlgEquiv R ι ι').toRingEquiv]
    exact Submodule.fg_bot
    -- Porting note: was
    -- convert Submodule.fg_bot
    -- exact RingHom.ker_coe_equiv (MvPolynomial.sumAlgEquiv R ι ι').toRingEquiv
  · rw [AlgHom.toRingHom_eq_coe, MvPolynomial.mapAlgHom_coe_ringHom, MvPolynomial.ker_map]
    exact hf_ker.map MvPolynomial.C
#align algebra.finite_presentation.mv_polynomial_of_finite_presentation Algebra.FinitePresentation.mvPolynomial_of_finitePresentation

/-- If `A` is an `R`-algebra and `S` is an `A`-algebra, both finitely presented, then `S` is
  finitely presented as `R`-algebra. -/
theorem trans [Algebra A B] [IsScalarTower R A B] (hfpA : FinitePresentation R A)
    (hfpB : FinitePresentation A B) : FinitePresentation R B := by
  obtain ⟨n, I, e, hfg⟩ := iff.1 hfpB
  -- ⊢ FinitePresentation R B
  exact equiv ((mvPolynomial_of_finitePresentation hfpA _).quotient hfg) (e.restrictScalars R)
  -- 🎉 no goals
#align algebra.finite_presentation.trans Algebra.FinitePresentation.trans

open MvPolynomial

-- We follow the proof of https://stacks.math.columbia.edu/tag/0561
-- TODO: extract out helper lemmas and tidy proof.
theorem of_restrict_scalars_finitePresentation [Algebra A B] [IsScalarTower R A B]
    (hRB : FinitePresentation.{w₁, w₃} R B) [hRA : FiniteType R A] :
    FinitePresentation.{w₂, w₃} A B := by
  classical
  obtain ⟨n, f, hf, s, hs⟩ := hRB
  letI RX := MvPolynomial (Fin n) R
  letI AX := MvPolynomial (Fin n) A
  refine' ⟨n, MvPolynomial.aeval (f ∘ X), _, _⟩
  · rw [← Algebra.range_top_iff_surjective, ← Algebra.adjoin_range_eq_range_aeval,
      Set.range_comp f MvPolynomial.X, eq_top_iff, ← @adjoin_adjoin_of_tower R A B,
      adjoin_image, adjoin_range_X, Algebra.map_top, (Algebra.range_top_iff_surjective _).mpr hf]
    exact fun {x} => subset_adjoin ⟨⟩
  · obtain ⟨t, ht⟩ := hRA.out
    have := fun i : t => hf (algebraMap A B i)
    choose t' ht' using this
    have ht'' : Algebra.adjoin R (algebraMap A AX '' t ∪ Set.range (X : _ → AX)) = ⊤ := by
      rw [adjoin_union_eq_adjoin_adjoin, ← Subalgebra.restrictScalars_top R (A := AX)
        (S := { x // x ∈ adjoin R ((algebraMap A AX) '' t) })]
      refine congrArg (Subalgebra.restrictScalars R) ?_
      congr 1
      rw [adjoin_algebraMap, ht]
      apply Subalgebra.restrictScalars_injective R
      rw [← adjoin_restrictScalars, adjoin_range_X, Subalgebra.restrictScalars_top,
        Subalgebra.restrictScalars_top]
    letI g : t → AX := fun x => MvPolynomial.C (x : A) - map (algebraMap R A) (t' x)
    refine' ⟨s.image (map (algebraMap R A)) ∪ t.attach.image g, _⟩
    rw [Finset.coe_union, Finset.coe_image, Finset.coe_image, Finset.attach_eq_univ,
      Finset.coe_univ, Set.image_univ]
    let s₀ := (MvPolynomial.map (algebraMap R A)) '' s ∪ Set.range g
    let I := RingHom.ker (MvPolynomial.aeval (R := A) (f ∘ MvPolynomial.X))
    change Ideal.span s₀ = I
    have leI : Ideal.span ((MvPolynomial.map (algebraMap R A)) '' s ∪ Set.range g) ≤
      RingHom.ker (MvPolynomial.aeval (R := A) (f ∘ MvPolynomial.X)) := by
      rw [Ideal.span_le]
      rintro _ (⟨x, hx, rfl⟩ | ⟨⟨x, hx⟩, rfl⟩) <;>
      erw [RingHom.mem_ker]
      · rw [MvPolynomial.aeval_map_algebraMap (R := R) (A := A), ← aeval_unique]
        have := Ideal.subset_span hx
        rwa [hs] at this
      · rw [map_sub, MvPolynomial.aeval_map_algebraMap, ← aeval_unique,
          MvPolynomial.aeval_C, ht', Subtype.coe_mk, sub_self]
    apply leI.antisymm
    intro x hx
    rw [RingHom.mem_ker] at hx
    let s₀ := (MvPolynomial.map (algebraMap R A)) '' ↑s ∪ Set.range g
    change x ∈ Ideal.span s₀
    have : x ∈ (MvPolynomial.map (algebraMap R A) : _ →+* AX).range.toAddSubmonoid ⊔
      (Ideal.span s₀).toAddSubmonoid := by
      have : x ∈ (⊤ : Subalgebra R AX) := trivial
      rw [← ht''] at this
      refine adjoin_induction this ?_ ?_ ?_ ?_
      · rintro _ (⟨x, hx, rfl⟩ | ⟨i, rfl⟩)
        · rw [algebraMap_eq, ← sub_add_cancel (MvPolynomial.C x)
            (map (algebraMap R A) (t' ⟨x, hx⟩)), add_comm]
          apply AddSubmonoid.add_mem_sup
          · exact Set.mem_range_self _
          · apply Ideal.subset_span
            apply Set.mem_union_right
            exact Set.mem_range_self _
        · apply AddSubmonoid.mem_sup_left
          exact ⟨X i, map_X _ _⟩
      · intro r
        apply AddSubmonoid.mem_sup_left
        exact ⟨C r, map_C _ _⟩
      · intro _ _ h₁ h₂
        exact add_mem h₁ h₂
      · intro x₁ x₂ h₁ h₂
        obtain ⟨_, ⟨p₁, rfl⟩, q₁, hq₁, rfl⟩ := AddSubmonoid.mem_sup.mp h₁
        obtain ⟨_, ⟨p₂, rfl⟩, q₂, hq₂, rfl⟩ := AddSubmonoid.mem_sup.mp h₂
        rw [add_mul, mul_add, add_assoc, ← map_mul]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
        · refine' add_mem (Ideal.mul_mem_left _ _ hq₂) (Ideal.mul_mem_right _ _ hq₁)
    obtain ⟨_, ⟨p, rfl⟩, q, hq, rfl⟩ := AddSubmonoid.mem_sup.mp this
    rw [map_add, aeval_map_algebraMap, ← aeval_unique, show MvPolynomial.aeval (f ∘ X) q = 0
      from leI hq, add_zero] at hx
    suffices Ideal.span (s : Set RX) ≤ (Ideal.span s₀).comap (MvPolynomial.map <| algebraMap R A) by
      refine' add_mem _ hq
      rw [hs] at this
      exact this hx
    rw [Ideal.span_le]
    intro x hx
    apply Ideal.subset_span
    apply Set.mem_union_left
    exact Set.mem_image_of_mem _ hx
#align algebra.finite_presentation.of_restrict_scalars_finite_presentation Algebra.FinitePresentation.of_restrict_scalars_finitePresentation

-- TODO: extract out helper lemmas and tidy proof.
/-- This is used to prove the strictly stronger `ker_fg_of_surjective`. Use it instead. -/
theorem ker_fg_of_mvPolynomial {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A)
    (hf : Function.Surjective f) (hfp : FinitePresentation R A) : f.toRingHom.ker.FG := by
  classical
    obtain ⟨m, f', hf', s, hs⟩ := hfp
    let RXn := MvPolynomial (Fin n) R
    let RXm := MvPolynomial (Fin m) R
    have := fun i : Fin n => hf' (f <| X i)
    choose g hg using this
    have := fun i : Fin m => hf (f' <| X i)
    choose h hh using this
    let aeval_h : RXm →ₐ[R] RXn := aeval h
    let g' : Fin n → RXn := fun i => X i - aeval_h (g i)
    refine' ⟨Finset.univ.image g' ∪ s.image aeval_h, _⟩
    simp only [Finset.coe_image, Finset.coe_union, Finset.coe_univ, Set.image_univ]
    have hh' : ∀ x, f (aeval_h x) = f' x := by
      intro x
      rw [← f.coe_toRingHom, map_aeval]
      simp_rw [AlgHom.coe_toRingHom, hh]
      rw [AlgHom.comp_algebraMap, ← aeval_eq_eval₂Hom,
        -- Porting note: added line below
        ← funext fun i => Function.comp_apply (f := ↑f') (g := MvPolynomial.X),
        ← aeval_unique]
    let s' := Set.range g' ∪ aeval_h '' s
    have leI : Ideal.span s' ≤ RingHom.ker f.toRingHom := by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨x, hx, rfl⟩)
      · change f (g' i) = 0
        rw [map_sub, ← hg, hh', sub_self]
      · change f (aeval_h x) = 0
        rw [hh']
        change x ∈ RingHom.ker f'.toRingHom
        rw [← hs]
        exact Ideal.subset_span hx
    apply leI.antisymm
    intro x hx
    have : x ∈ aeval_h.range.toAddSubmonoid ⊔ (Ideal.span s').toAddSubmonoid := by
      have : x ∈ adjoin R (Set.range X : Set RXn) := by
        rw [adjoin_range_X]
        trivial
      refine adjoin_induction this ?_ ?_ ?_ ?_
      · rintro _ ⟨i, rfl⟩
        rw [← sub_add_cancel (X i) (aeval h (g i)), add_comm]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
        · apply Submodule.subset_span
          apply Set.mem_union_left
          exact Set.mem_range_self _
      · intro r
        apply AddSubmonoid.mem_sup_left
        exact ⟨C r, aeval_C _ _⟩
      · intro _ _ h₁ h₂
        exact add_mem h₁ h₂
      · intro p₁ p₂ h₁ h₂
        obtain ⟨_, ⟨x₁, rfl⟩, y₁, hy₁, rfl⟩ := AddSubmonoid.mem_sup.mp h₁
        obtain ⟨_, ⟨x₂, rfl⟩, y₂, hy₂, rfl⟩ := AddSubmonoid.mem_sup.mp h₂
        rw [mul_add, add_mul, add_assoc, ← map_mul]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
        · exact add_mem (Ideal.mul_mem_right _ _ hy₁) (Ideal.mul_mem_left _ _ hy₂)
    obtain ⟨_, ⟨x, rfl⟩, y, hy, rfl⟩ := AddSubmonoid.mem_sup.mp this
    refine' add_mem _ hy
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_add,
      show f y = 0 from leI hy, add_zero, hh'] at hx
    suffices Ideal.span (s : Set RXm) ≤ (Ideal.span s').comap aeval_h by
      apply this
      rwa [hs]
    rw [Ideal.span_le]
    intro x hx
    apply Submodule.subset_span
    apply Set.mem_union_right
    exact Set.mem_image_of_mem _ hx
#align algebra.finite_presentation.ker_fg_of_mv_polynomial Algebra.FinitePresentation.ker_fg_of_mvPolynomial

/-- If `f : A →ₐ[R] B` is a surjection between finitely-presented `R`-algebras, then the kernel of
`f` is finitely generated. -/
theorem ker_fG_of_surjective (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (hRA : FinitePresentation R A) (hRB : FinitePresentation R B) : f.toRingHom.ker.FG := by
  obtain ⟨n, g, hg, _⟩ := hRA
  -- ⊢ Ideal.FG (RingHom.ker ↑f)
  convert (ker_fg_of_mvPolynomial (f.comp g) (hf.comp hg) hRB).map g.toRingHom
  -- ⊢ RingHom.ker ↑f = Ideal.map (↑g) (RingHom.ker ↑(AlgHom.comp f g))
  simp_rw [RingHom.ker_eq_comap_bot, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  -- ⊢ Ideal.comap ↑f ⊥ = Ideal.map (↑g) (Ideal.comap (RingHom.comp ↑f ↑g) ⊥)
  rw [← Ideal.comap_comap, Ideal.map_comap_of_surjective (g : MvPolynomial (Fin n) R →+* A) hg]
  -- 🎉 no goals
#align algebra.finite_presentation.ker_fg_of_surjective Algebra.FinitePresentation.ker_fG_of_surjective

end FinitePresentation

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is of `RingHom.FinitePresentation` if `B` is finitely presented as
`A`-algebra. -/
def FinitePresentation (f : A →+* B) : Prop :=
  @Algebra.FinitePresentation A B _ _ f.toAlgebra
#align ring_hom.finite_presentation RingHom.FinitePresentation

namespace FiniteType

theorem of_finitePresentation {f : A →+* B} (hf : f.FinitePresentation) : f.FiniteType :=
  @Algebra.FiniteType.of_finitePresentation A B _ _ f.toAlgebra hf
#align ring_hom.finite_type.of_finite_presentation RingHom.FiniteType.of_finitePresentation

end FiniteType

namespace FinitePresentation

variable (A)

theorem id : FinitePresentation (RingHom.id A) :=
  Algebra.FinitePresentation.self A
#align ring_hom.finite_presentation.id RingHom.FinitePresentation.id

variable {A}

theorem comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.FinitePresentation) (hg : Surjective g)
    (hker : g.ker.FG) : (g.comp f).FinitePresentation :=
  letI := f.toAlgebra
  letI := (g.comp f).toAlgebra
  Algebra.FinitePresentation.of_surjective
    (f :=
      { g with
        toFun := g
        commutes' := fun _ => rfl })
    hg hker hf
#align ring_hom.finite_presentation.comp_surjective RingHom.FinitePresentation.comp_surjective

theorem of_surjective (f : A →+* B) (hf : Surjective f) (hker : f.ker.FG) :
    f.FinitePresentation := by
  rw [← f.comp_id]
  -- ⊢ FinitePresentation (comp f (RingHom.id A))
  exact (id A).comp_surjective hf hker
  -- 🎉 no goals
#align ring_hom.finite_presentation.of_surjective RingHom.FinitePresentation.of_surjective

theorem of_finiteType [IsNoetherianRing A] {f : A →+* B} : f.FiniteType ↔ f.FinitePresentation :=
  @Algebra.FinitePresentation.of_finiteType A B _ _ f.toAlgebra _
#align ring_hom.finite_presentation.of_finite_type RingHom.FinitePresentation.of_finiteType

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FinitePresentation) (hf : f.FinitePresentation) :
    (g.comp f).FinitePresentation :=
  -- Porting note : specify `Algebra` instances to get `SMul`
  letI ins1 := RingHom.toAlgebra f
  letI ins2 := RingHom.toAlgebra g
  letI ins3 := RingHom.toAlgebra (g.comp f)
  letI ins4 : IsScalarTower A B C :=
    { smul_assoc := fun a b c => by simp [Algebra.smul_def, mul_assoc]; rfl }
                                    -- ⊢ ↑(algebraMap B C) (↑(algebraMap A B) a) * (↑(algebraMap B C) b * c) = ↑(alge …
                                                                        -- 🎉 no goals
  Algebra.FinitePresentation.trans hf hg
#align ring_hom.finite_presentation.comp RingHom.FinitePresentation.comp

theorem of_comp_finiteType (f : A →+* B) {g : B →+* C} (hg : (g.comp f).FinitePresentation)
    (hf : f.FiniteType) : g.FinitePresentation :=
  -- Porting note : need to specify some instances
  letI ins1 := RingHom.toAlgebra f
  letI ins2 := RingHom.toAlgebra g
  letI ins3 := RingHom.toAlgebra (g.comp f)
  letI ins4 : IsScalarTower A B C :=
    { smul_assoc := fun a b c => by simp [Algebra.smul_def, mul_assoc]; rfl }
                                    -- ⊢ ↑(algebraMap B C) (↑(algebraMap A B) a) * (↑(algebraMap B C) b * c) = ↑(alge …
                                                                        -- 🎉 no goals
  Algebra.FinitePresentation.of_restrict_scalars_finitePresentation (hRA := hf) hg
#align ring_hom.finite_presentation.of_comp_finite_type RingHom.FinitePresentation.of_comp_finiteType

end FinitePresentation

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommRing R]

variable [CommRing A] [CommRing B] [CommRing C]

variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is of `AlgHom.FinitePresentation` if it is of finite
presentation as ring morphism. In other words, if `B` is finitely presented as `A`-algebra. -/
def FinitePresentation (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.FinitePresentation
#align alg_hom.finite_presentation AlgHom.FinitePresentation

namespace FiniteType

theorem of_finitePresentation {f : A →ₐ[R] B} (hf : f.FinitePresentation) : f.FiniteType :=
  RingHom.FiniteType.of_finitePresentation hf
#align alg_hom.finite_type.of_finite_presentation AlgHom.FiniteType.of_finitePresentation

end FiniteType

namespace FinitePresentation

variable (R A)

theorem id : FinitePresentation (AlgHom.id R A) :=
  RingHom.FinitePresentation.id A
#align alg_hom.finite_presentation.id AlgHom.FinitePresentation.id

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FinitePresentation)
    (hf : f.FinitePresentation) : (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.comp hg hf
#align alg_hom.finite_presentation.comp AlgHom.FinitePresentation.comp

theorem comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.FinitePresentation)
    (hg : Surjective g) (hker : g.toRingHom.ker.FG) : (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.comp_surjective hf hg hker
#align alg_hom.finite_presentation.comp_surjective AlgHom.FinitePresentation.comp_surjective

theorem of_surjective (f : A →ₐ[R] B) (hf : Surjective f) (hker : f.toRingHom.ker.FG) :
    f.FinitePresentation := by
  -- Porting note: added `convert`
  convert RingHom.FinitePresentation.of_surjective f hf hker
  -- 🎉 no goals
#align alg_hom.finite_presentation.of_surjective AlgHom.FinitePresentation.of_surjective

theorem of_finiteType [IsNoetherianRing A] {f : A →ₐ[R] B} : f.FiniteType ↔ f.FinitePresentation :=
  RingHom.FinitePresentation.of_finiteType
#align alg_hom.finite_presentation.of_finite_type AlgHom.FinitePresentation.of_finiteType

nonrec theorem of_comp_finiteType (f : A →ₐ[R] B) {g : B →ₐ[R] C}
    (h : (g.comp f).FinitePresentation) (h' : f.FiniteType) : g.FinitePresentation :=
  h.of_comp_finiteType _ h'
#align alg_hom.finite_presentation.of_comp_finite_type AlgHom.FinitePresentation.of_comp_finiteType

end FinitePresentation

end AlgHom
