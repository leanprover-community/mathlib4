/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.RingOfDefinition.BaseChange
import Mathlib.ToBeMoved

/-!

# Descent of smooth morphisms

If `A` is a smooth `R`-algebra, there exists a subring `R₀` of `R` of finite type over `ℤ` and
a smooth `R₀`-algebra `A₀` such that `A` is `R`-isomorphic to `R ⊗[R₀] A₀`.

-/

universe u v

open TensorProduct

namespace Algebra

variable (R : Type u) [CommRing R]
variable (A : Type u) [CommRing A] [Algebra R A]


namespace Smooth

section

variable {R} {A}
variable {ι : Type u} {f : MvPolynomial ι R →ₐ[R] A} (hf : Function.Surjective f)

local notation "I" => RingHom.ker f

variable (s : Set (MvPolynomial ι R)) (hs : Ideal.span s = RingHom.ker f)
variable (hfin : Set.Finite s)

open RingOfDefinition

variable (σ : A →ₐ[R] MvPolynomial ι R ⧸ RingHom.ker f ^ 2)
variable (hsig : f.kerSquareLift.comp σ = AlgHom.id R A)

private noncomputable def hAux (i : ι) : MvPolynomial ι R :=
  (Quotient.exists_rep (σ (f (MvPolynomial.X i)))).choose

@[simp]
private lemma hAux_eq (i : ι) : hAux σ i = σ (f (MvPolynomial.X i : MvPolynomial ι R)) := by
  simp only [hAux]
  exact Exists.choose_spec (Quotient.exists_rep _)

private noncomputable def sOfh : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  MvPolynomial.aeval (fun j : ι => hAux σ j)

@[simp]
private lemma sOfh_X (i : ι) :
    sOfh σ (MvPolynomial.X i : MvPolynomial ι R) = σ (f (MvPolynomial.X i)) := by
  simp [sOfh]

private lemma sigma_eq_mk_sOfh (p : MvPolynomial ι R) : σ (f p) = sOfh σ p := by
  let u : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I ^ 2 :=
    σ.comp f
  let v : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I ^ 2 :=
    (Ideal.Quotient.mkₐ R (I ^ 2)).comp (sOfh σ)
  suffices h : u = v by
    change u p = v p
    congr
  apply MvPolynomial.algHom_ext (fun i ↦ ?_)
  simp [u, v]

private lemma sOfh_mem_sq (p : MvPolynomial ι R) (hp : p ∈ I) : sOfh σ p ∈ I ^ 2 := by
  suffices h : f p = 0 by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← sigma_eq_mk_sOfh, h, map_zero]
  rwa [← RingHom.mem_ker]

private lemma sOfh_exists_P (p : MvPolynomial ι R) (hp : p ∈ s) :
    ∃ (r : Relation s), r.IsHomogeneous 2 ∧ Relation.eval r = sOfh σ p := by
  apply (Ideal.mem_sq I _ hs.symm _).mp
  apply sOfh_mem_sq
  rw [← hs]
  exact Ideal.subset_span hp

private lemma hAux_sub_X_ex_rep (i : ι) :
    ∃ (r : Relation s), r.IsHomogeneous 1 ∧ Relation.eval r = hAux σ i - MvPolynomial.X i := by
  apply (Ideal.mem_span_iff I _ hs.symm _).mp
  rw [RingHom.mem_ker, map_sub]
  change f (Algebra.Smooth.hAux σ i) - (AlgHom.id R A) (f (MvPolynomial.X i)) = 0
  rw [← hsig, AlgHom.coe_comp, Function.comp_apply]
  erw [← hAux_eq, Ideal.Quotient.lift_mk]
  simp only [sub_self]

private noncomputable def relP (p : s) : Relation s := (sOfh_exists_P s hs σ p p.property).choose

@[simp]
private theorem relP_eval (p : s) : Relation.eval (relP s hs σ p) = sOfh σ p :=
  (sOfh_exists_P s hs σ p p.property).choose_spec.right

private noncomputable def relQ (i : ι) : Relation s :=
  (hAux_sub_X_ex_rep s hs σ hsig i).choose

@[simp]
private theorem relQ_eval (i : ι) :
    Relation.eval (relQ s hs σ hsig i) = Algebra.Smooth.hAux σ i - MvPolynomial.X i :=
  (hAux_sub_X_ex_rep s hs σ hsig i).choose_spec.right

private abbrev coefficientRing : Subring R := Subring.adjoinRelations (Set.range <| relP s hs σ) <|
  Subring.adjoinRelations (Set.range <| relQ s hs σ hsig) <|
  Subring.adjoinCoefficients (Set.range <| hAux σ) <|
  (core s)

private theorem finiteType₀ [Finite ι] :
    FiniteType ℤ (coefficientRing s hs σ hsig) := by
  let R1 := core s
  let R2 := Subring.adjoinCoefficients (Set.range <| hAux σ) <| R1
  let R3 := Subring.adjoinRelations (Set.range <| relQ s hs σ hsig) <| R2
  have : FiniteType ℤ R1 := core_finiteType_of_finite s hfin
  have : FiniteType ℤ R2 := by
    apply R1.adjoinCoefficients_finiteType_of_finite'
    exact Set.finite_range (hAux σ)
  have : FiniteType ℤ R3 := by
    apply R2.adjoinCoefficients_finiteType_of_finite'
    apply Set.coefficients_finite_of_finite
    exact Set.finite_range (relQ s hs σ hsig)
  have : Finite s := hfin
  apply R3.adjoinCoefficients_finiteType_of_finite'
  exact Set.coefficients_finite_of_finite _ (Set.finite_range (relP s hs σ))

private abbrev model : Model I where
  s := s
  hs := hs
  R₀ := coefficientRing s hs σ hsig
  coeffs := inferInstance

local notation "M" => model s hs σ hsig
local notation "R₀" => Model.R₀ M
local notation "I₀" => Model.I₀ M
local notation "s₀" => Model.s₀ M

private noncomputable def hAux₀ (i : ι) : MvPolynomial ι R₀ := (hAux σ i).repr R₀

private lemma hAux₀_eval (a : MvPolynomial ι R₀) (ha : a ∈ I₀) :
    MvPolynomial.aeval (hAux₀ s hs σ hsig) a ∈ I₀ ^ 2 := by
  refine Submodule.span_induction ha (fun p₀ hp₀ ↦ ?_) ?_ (fun x y hx hy ↦ ?_) (fun a x hx ↦ ?_)
  · let p := Model.definingSetEquiv M ⟨p₀, hp₀⟩
    rw [Ideal.mem_sq I₀ s₀ rfl]
    refine ⟨(relP s hs σ p).repr M, ?_, ?_⟩
    · apply (relP s hs σ p).repr_homogeneous M
      exact (sOfh_exists_P s hs σ p p.property).choose_spec.left
    · apply Relation.eval_eq_of_eval_eq
      rw [Relation.repr_map, relP_eval]
      simp only [sOfh, Model.definingSetEquiv_apply, MvPolynomial.map_aeval, hAux₀,
        map_repr, MvPolynomial.coe_eval₂Hom, p]
      simp only [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq, MvPolynomial.eval₂_map,
        MvPolynomial.C_comp_subringSubtype]
  · simp
  · simp only [map_add, Ideal.add_mem _ hx hy]
  · simp only [smul_eq_mul, _root_.map_mul, Ideal.mul_mem_left _ _ hx]

private noncomputable def σ₀ : MvPolynomial ι R₀ ⧸ I₀ →ₐ[R₀]
    MvPolynomial ι R₀ ⧸ RingHom.ker (Ideal.Quotient.mkₐ R₀ I₀) ^ 2 :=
  Ideal.Quotient.liftₐ I₀
    (AlgHom.comp
        (Ideal.Quotient.mkₐ R₀ (RingHom.ker (Ideal.Quotient.mkₐ R₀ I₀) ^ 2))
        (MvPolynomial.aeval (hAux₀ s hs σ hsig)))
    (fun a ha ↦by
      simp only [AlgHom.comp_apply, ← RingHom.mem_ker]
      erw [Ideal.Quotient.mkₐ_ker R₀, Ideal.Quotient.mkₐ_ker R₀]
      apply hAux₀_eval s hs σ hsig a ha)

variable [Fintype ι]

private theorem formallySmooth₀ :
    FormallySmooth R₀ (model s hs σ hsig).A₀ :=
  FormallySmooth.of_split (Ideal.Quotient.mkₐ R₀ I₀) (σ₀ s hs σ hsig)
    (by
      apply (AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective R₀ I₀)).mp
      apply MvPolynomial.algHom_ext (fun i ↦ ?_)
      simp [σ₀]
      erw [Ideal.Quotient.lift_mk]
      simp
      erw [Ideal.Quotient.eq, Ideal.mem_span_iff I₀ s₀ rfl]
      refine ⟨(relQ s hs σ hsig i).repr M, ?_, ?_⟩
      · apply (relQ s hs σ hsig i).repr_homogeneous M
        exact (hAux_sub_X_ex_rep s hs σ hsig i).choose_spec.left
      · apply Relation.eval_eq_of_eval_eq
        rw [Relation.repr_map]
        simp [hAux₀])

private theorem finitePresentation₀ :
    FinitePresentation (model s hs σ hsig).R₀ (model s hs σ hsig).A₀ :=
  (model s hs σ hsig).finitePresentation_of_finite hfin

end

open RingOfDefinition

variable [FinitePresentation R A] [FormallySmooth R A]

theorem descent : ∃ (R₀ : Subring R) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra R₀ A₀)
    (_ : A ≃ₐ[R] R ⊗[R₀] A₀),
    FiniteType ℤ R₀ ∧ FinitePresentation R₀ A₀ ∧ FormallySmooth R₀ A₀ := by
  obtain ⟨ι, hfin, f, hfsurj, s, hs⟩ :=
    (FinitePresentation.iff_quotient_mvPolynomial' (R := R) (A := A)).mp inferInstance
  obtain ⟨σ, hsig⟩ := (FormallySmooth.iff_split_surjection f hfsurj).mp inferInstance
  let M : Model (RingHom.ker f) := model s hs σ hsig
  let e := (model s hs σ hsig).baseChangeIso
  let is := Ideal.quotientKerAlgEquivOfSurjective hfsurj
  refine ⟨M.R₀, M.A₀, inferInstance, inferInstance, is.symm.trans e, ?_, ?_, ?_⟩
  · exact finiteType₀ (f := f) s hs s.finite_toSet σ hsig
  · exact finitePresentation₀ (f := f) s hs s.finite_toSet σ hsig
  · exact formallySmooth₀ (f := f) s hs σ hsig

end Smooth
