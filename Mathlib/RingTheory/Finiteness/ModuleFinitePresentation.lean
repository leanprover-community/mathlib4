/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Finitely presented algebras and finitely presented modules

In this file we establish relations between finitely presented as an algebra and
finitely presented as a module.

## Main results:

- `Module.FinitePresentation.of_finite_of_finitePresentation`: If `S` is finite as a module over `R`
  and finitely presented as an algebra over `R`, then it is finitely presented as a module over `R`.
-/

universe u

open Polynomial

attribute [local instance] MvPolynomial.algebraQuotientSpanToMvPolynomial

/-- Use `Module.Free.quotient_span_toMvPolynomial_of_monic` and
`Module.Finite.quotient_span_toMvPolynomial_of_monic` instead. -/
private lemma MvPolynomial.free_and_finite_quotient_of_monic {R ι : Type*} [Finite ι] [CommRing R]
    (p : ι → R[X]) (hp : ∀ i, (p i).Monic) :
    Module.Free R
      (MvPolynomial ι R ⧸ (Ideal.span <| .range fun i ↦ (p i).toMvPolynomial i)) ∧
    Module.Finite R
      (MvPolynomial ι R ⧸ (Ideal.span <| .range fun i ↦ (p i).toMvPolynomial i)) := by
  cases nonempty_fintype ι
  revert p
  refine Fintype.induction_empty_option ?_ ?_ ?_ ι
  · intro α β _ e h p hp
    let q (a : α) : R[X] := p (e a)
    let e : (MvPolynomial α R ⧸ Ideal.span (Set.range fun i ↦ (toMvPolynomial i) (q i))) ≃ₐ[R]
        (MvPolynomial β R ⧸ Ideal.span (Set.range fun i ↦ (toMvPolynomial i) (p i))) :=
      Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv R e) <| by
        rw [Ideal.map_span]
        have : (fun x ↦ (toMvPolynomial (e x)) (p (e x))) =
          (fun x ↦ toMvPolynomial x (p x)) ∘ e := rfl
        simp_rw [RingHom.coe_coe, renameEquiv_apply, ← Set.range_comp, Function.comp_def]
        simp [rename_toMvPolynomial, q, this, Set.range_comp]
    have := (h q (fun a ↦ hp _)).1
    have := (h q (fun a ↦ hp _)).2
    exact ⟨Module.Free.of_equiv e.toLinearEquiv, Module.Finite.equiv e.toLinearEquiv⟩
  · refine fun p _ ↦ ⟨?_, inferInstance⟩
    have : Ideal.span (.range fun i ↦ toMvPolynomial i (p i)) = ⊥ := by simp [Set.range_eq_empty]
    exact Module.Free.of_equiv
      ((Ideal.quotientEquivAlgOfEq R this).trans (AlgEquiv.quotientBot R _)).toLinearEquiv.symm
  · intro α _ hp q hq
    let A := MvPolynomial α R ⧸ (Ideal.span <| Set.range fun i : α ↦ (q i).toMvPolynomial i)
    let B := MvPolynomial (Option α) R ⧸ (Ideal.span <| Set.range fun i ↦ (q i).toMvPolynomial i)
    let P : A[X] := (q none).map (algebraMap R A)
    have : Module.Free R A := (hp _ (fun i ↦ hq i)).1
    have : Module.Finite R A := (hp _ (fun i ↦ hq i)).2
    have : Module.Free A (AdjoinRoot P) := ((hq none).map _).free_adjoinRoot
    have : Module.Finite A (AdjoinRoot P) := ((hq none).map _).finite_adjoinRoot
    have : Module.Free A B := .of_equiv (AdjoinRoot.spanToMvPolynomialEquiv q).toLinearEquiv
    have : Module.Finite A B := .equiv ((AdjoinRoot.spanToMvPolynomialEquiv q).toLinearEquiv)
    exact ⟨Module.Free.trans (R := R) (S := A) (M := B), Module.Finite.trans A B⟩

lemma Module.Free.quotient_span_toMvPolynomial_of_monic {R ι : Type*} [Finite ι] [CommRing R]
    {p : ι → R[X]} (hp : ∀ i, (p i).Monic) :
    Module.Free R
      (MvPolynomial ι R ⧸ (Ideal.span <| Set.range fun i ↦ (p i).toMvPolynomial i)) :=
  (MvPolynomial.free_and_finite_quotient_of_monic p hp).1

lemma Module.Finite.quotient_span_toMvPolynomial_of_monic {R ι : Type*} [Finite ι] [CommRing R]
    {p : ι → R[X]} (hp : ∀ i, (p i).Monic) :
    Module.Finite R
      (MvPolynomial ι R ⧸ (Ideal.span <| Set.range fun i ↦ (p i).toMvPolynomial i)) :=
  (MvPolynomial.free_and_finite_quotient_of_monic p hp).2

/-- If `S` is finite as a module over `R` and finitely presented as an algebra over `R`, then
it is finitely presented as a module over `R`. -/
@[stacks 0564 "The case M = S"]
instance (priority := 900) Module.FinitePresentation.of_finite_of_finitePresentation {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [Algebra.FinitePresentation R S] :
    Module.FinitePresentation R S := by
  obtain ⟨s, hs⟩ : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
  choose p hm hp using fun s : S ↦ Algebra.IsIntegral.isIntegral (R := R) s
  let q (x : s) : MvPolynomial s R := (p x).toMvPolynomial x
  let S' : Type _ := MvPolynomial s R ⧸ (Ideal.span <| .range fun x ↦ q x)
  let f : S' →ₐ[R] S := Ideal.Quotient.liftₐ _ (MvPolynomial.aeval Subtype.val) <| by
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le]
    rintro a ⟨x, rfl⟩
    simpa [q] using hp x
  have hf : Function.Surjective f := by
    apply Ideal.Quotient.lift_surjective_of_surjective
    rw [RingHom.coe_coe, ← AlgHom.range_eq_top, ← Algebra.map_top, eq_top_iff,
      ← Subalgebra.toSubmodule.map_rel_iff, Algebra.top_toSubmodule, Algebra.map_top, ← hs,
      Submodule.span_le]
    intro x hx
    use .X ⟨x, hx⟩
    simp
  let _ : Algebra S' S := f.toRingHom.toAlgebra
  have : Algebra.FinitePresentation S' S := .of_restrict_scalars_finitePresentation R _ _
  have hker : (RingHom.ker f).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId S' S) hf
  have : Module.FinitePresentation S' S :=
    Module.finitePresentation_of_surjective (Algebra.linearMap S' S) hf hker
  have : IsScalarTower R S' S := .of_algHom f
  have : Module.Finite R S' := .quotient_span_toMvPolynomial_of_monic (hm ·)
  have : Module.Free R S' := .quotient_span_toMvPolynomial_of_monic (hm ·)
  have : Module.FinitePresentation R S' :=
    Module.finitePresentation_of_projective R S'
  exact .trans R S S'
