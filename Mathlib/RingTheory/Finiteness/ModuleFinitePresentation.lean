/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Basic

universe u

open TensorProduct

open Polynomial

open MvPolynomial

@[simp]
lemma Polynomial.aeval_quotientMk_X {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (g : R[X]) (I : Ideal S[X]) :
    Polynomial.aeval (Ideal.Quotient.mk I Polynomial.X) g =
      Ideal.Quotient.mk I (Polynomial.map (algebraMap R S) g) := by
  simp [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply, aeval_X_left_of_algebra_apply]

lemma Polynomial.aeval_mk_toMvPolynomial {α R : Type*} [CommRing R]
    (p : α → R[X]) (i : α) (x : R[X]) :
    Polynomial.aeval (Ideal.Quotient.mk (.span (.range fun i ↦ (p i).toMvPolynomial i)) (.X i)) x =
      Ideal.Quotient.mk _ (x.toMvPolynomial i) := by
  simp [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply, toMvPolynomial]

noncomputable instance {S : Type*} [CommRing S] (I : Ideal S) (g : S[X]) :
    Algebra (S ⧸ I) (S[X] ⧸ Ideal.map Polynomial.C I ⊔ Ideal.span {g}) :=
  letI f : (S ⧸ I) →ₐ[S] (S[X] ⧸ Ideal.map Polynomial.C I ⊔ Ideal.span {g}) :=
    Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) fun a ha ↦ by
      rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply S S[X],
        Ideal.Quotient.algebraMap_eq, Polynomial.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem Polynomial.C ha)
  f.toAlgebra

instance {S : Type*} [CommRing S] (I : Ideal S) (g : S[X]) :
    IsScalarTower S (S ⧸ I) (S[X] ⧸ Ideal.map Polynomial.C I ⊔ Ideal.span {g}) :=
  .of_algHom _

/-- `S ⧸ I` adjoined a root of `g : S[X]` is `S ⧸ I`-equivalent to `S[X] ⧸ (I ⊔ g)`. -/
noncomputable
def AdjoinRoot.quotientMkEquiv {S : Type*} [CommRing S] (I : Ideal S) (g : S[X]) :
    AdjoinRoot (g.map (Ideal.Quotient.mk I)) ≃ₐ[S ⧸ I]
      S[X] ⧸ (I.map Polynomial.C ⊔ Ideal.span {g}) :=
  letI u : AdjoinRoot (g.map (Ideal.Quotient.mk I)) →ₐ[S ⧸ I]
      S[X] ⧸ (I.map Polynomial.C ⊔ Ideal.span {g}) :=
    AdjoinRoot.liftHom _ (Ideal.Quotient.mk _ .X) <| by
      simp_rw [← Ideal.Quotient.algebraMap_eq, Polynomial.aeval_map_algebraMap,
        Ideal.Quotient.algebraMap_eq, aeval_quotientMk_X, Ideal.Quotient.eq_zero_iff_mem,
        Algebra.algebraMap_self, Polynomial.map_id]
      exact Ideal.mem_sup_right <| Ideal.subset_span rfl
  letI v : (S[X] ⧸ (I.map Polynomial.C ⊔ Ideal.span {g})) →ₐ[S ⧸ I]
      AdjoinRoot (g.map (Ideal.Quotient.mk I)) :=
    AlgHom.restrictQuotient I <|
    Ideal.Quotient.liftₐ _ (Polynomial.aeval <| .root _) <| by
      simp_rw [← RingHom.mem_ker, ← SetLike.le_def, sup_le_iff]
      refine ⟨?_, ?_⟩
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simp [IsScalarTower.algebraMap_apply S (S ⧸ I), Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      · simp [Ideal.span_le, Set.singleton_subset_iff]
  have h1 : v.comp u = AlgHom.id _ _ := AdjoinRoot.algHom_ext (by simp [u, v])
  have h2 : (u.comp v).restrictScalars S = AlgHom.id S _ :=
    Ideal.Quotient.algHom_ext _ (by ext; simp [u, v])
  { __ := u, invFun := v, left_inv x := DFunLike.congr_fun h1 x,
    right_inv x := DFunLike.congr_fun h2 x }

/-- `S ⧸ I` adjoined a root of `g : S[X]` is `S ⧸ I`-equivalent to `S[X] ⧸ (I ⊔ g)`. -/
noncomputable
def IsAdjoinRoot.quotientMk {S : Type*} [CommRing S] (I : Ideal S) (g : S[X]) :
    IsAdjoinRoot (S[X] ⧸ (I.map Polynomial.C ⊔ Ideal.span {g}))
      (g.map (Ideal.Quotient.mk I)) :=
  .ofAlgEquiv (AdjoinRoot.isAdjoinRoot _) (AdjoinRoot.quotientMkEquiv I g)

namespace MvPolynomial

instance {ι R : Type*} [CommSemiring R] [IsEmpty ι] : Module.Finite R (MvPolynomial ι R) :=
  Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv R ι).toLinearEquiv.symm

section

variable {α R : Type*} [CommRing R] (p : Option α → R[X])

noncomputable instance :
    Algebra (MvPolynomial α R ⧸ (Ideal.span (.range fun i ↦ (p (some i)).toMvPolynomial i)))
      (MvPolynomial (Option α) R ⧸ (Ideal.span (.range fun i ↦ (p i).toMvPolynomial i))) :=
  letI f := Ideal.Quotient.liftₐ _ (aeval fun x ↦ Ideal.Quotient.mk _ <| X (some x)) <| by
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le]
    rintro - ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, aeval_toMvPolynomial]
    rw [Polynomial.aeval_mk_toMvPolynomial, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.subset_span
    use i
  f.toRingHom.toAlgebra

instance : IsScalarTower R
    (MvPolynomial α R ⧸ Ideal.span (Set.range fun i ↦ (toMvPolynomial i) (p (some i))))
    (MvPolynomial (Option α) R ⧸ Ideal.span (Set.range fun i ↦ (toMvPolynomial i) (p i))) :=
  .of_algHom _

attribute [local instance] MvPolynomial.algebraOption

instance : IsScalarTower (MvPolynomial α R)
    (MvPolynomial α R ⧸ Ideal.span (Set.range fun i ↦ (toMvPolynomial i) (p (some i))))
    (MvPolynomial (Option α) R ⧸ Ideal.span (Set.range fun i ↦ (toMvPolynomial i) (p i))) := by
  refine .of_algebraMap_eq' ?_
  ext x
  · simp [RingHom.algebraMap_toAlgebra,
      IsScalarTower.algebraMap_apply R (MvPolynomial (Option α) R)]
  · simp [RingHom.algebraMap_toAlgebra]

end

end MvPolynomial

open MvPolynomial

attribute [local instance] MvPolynomial.algebraOption

/-- If `p` is a family of polynomials, `R[X₁, ..., Xₙ]/(p₁, ..., pₙ)` adjoint `pₙ₊₁`
is isomorphic to `R[X₁, ..., Xₙ₊₁]/(p₁, ..., pₙ₊₁). -/
noncomputable
def AdjoinRoot.spanToMvPolynomialEquiv {α R : Type*} [CommRing R] (p : Option α → R[X]) :
    AdjoinRoot ((p none).map (algebraMap R
      (MvPolynomial α R ⧸ (Ideal.span <| .range fun i ↦ (p (some i)).toMvPolynomial i))))
        ≃ₐ[MvPolynomial α R ⧸ (Ideal.span <| .range fun i ↦ (p (some i)).toMvPolynomial i)]
    MvPolynomial (Option α) R ⧸ (Ideal.span <| .range fun i ↦ (p i).toMvPolynomial i) := by
  letI e := AdjoinRoot.quotientMkEquiv
    (.span (.range fun i ↦ (toMvPolynomial i) (p (some i)))) (Polynomial.map C (p none))
  refine (IsAdjoinRoot.adjoinRootAlgEquiv ?_).trans (e.trans (AlgEquiv.restrictQuotient _ ?_))
  · rw [IsScalarTower.algebraMap_eq R (MvPolynomial α R), Ideal.Quotient.algebraMap_eq,
      MvPolynomial.algebraMap_eq, ← Polynomial.map_map]
    exact AdjoinRoot.isAdjoinRoot _
  refine Ideal.quotientEquivAlg _
    (.span (.range fun i ↦ (toMvPolynomial i) (p i))) (optionEquivLeft' R α).symm ?_
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Ideal.map_span, ← Ideal.span_union,
    ← Set.range_comp, ← Set.range_comp, Function.comp_def, Function.comp_def]
  simp only [RingHom.coe_coe, coe_optionEquivLeft'_symm, optionEquivLeft_symm_apply,
    Polynomial.aevalTower_C, rename_toMvPolynomial, Set.image_singleton, Set.union_singleton,
    Option.range_eq]
  congr 2
  induction p none using Polynomial.induction_on <;> simp_all

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
