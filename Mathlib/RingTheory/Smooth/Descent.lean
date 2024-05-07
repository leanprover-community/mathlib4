/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.RingOfDefinition.Relations

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
variable {ι : Type u}
variable (f : MvPolynomial ι R →ₐ[R] A) (hf : Function.Surjective f)

local notation "I" => RingHom.ker f.toRingHom

variable (s : Set (MvPolynomial ι R)) (hs : Ideal.span s = RingHom.ker f.toRingHom)

open RingOfDefinition

variable (σ : A →ₐ[R] MvPolynomial ι R ⧸ RingHom.ker f.toRingHom ^ 2)
variable (hsig : f.kerSquareLift.comp σ = AlgHom.id R A)

private noncomputable def hAux (i : ι) : MvPolynomial ι R :=
  (Quotient.exists_rep (σ (f (MvPolynomial.X i)))).choose

@[simp]
private lemma hAux_eq (i : ι) : hAux f σ i = σ (f (MvPolynomial.X i : MvPolynomial ι R)) := by
  simp only [hAux]
  exact Exists.choose_spec (Quotient.exists_rep _)

private noncomputable def sOfh : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  MvPolynomial.aeval (fun j : ι => hAux f σ j)

lemma sigma_eq_mk_sOfh (p : MvPolynomial ι R) : σ (f p) = sOfh f σ p := by
  let u : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I ^ 2 :=
    σ.comp f
  let v : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I ^ 2 :=
    (Ideal.Quotient.mkₐ R (I ^ 2)).comp (sOfh f σ)
  suffices h : u = v by
    change u p = v p
    congr
  apply MvPolynomial.algHom_ext
  intro i
  simp [u, v, sOfh]
  sorry

lemma sOfh_mem_sq (p : MvPolynomial ι R) (hp : p ∈ I) : sOfh f σ p ∈ I ^ 2 := by
  suffices h : f p = 0 by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← sigma_eq_mk_sOfh, h, map_zero]
  rwa [← RingHom.mem_ker]

open RingOfDefinition

lemma sOfh_exists_P (p : MvPolynomial ι R) (hp : p ∈ s) :
    ∃ (r : Relation s), r.IsHomogeneous 2 ∧ Relation.eval r = sOfh f σ p :=
  sorry
  --(Ideal.mem_sq I _ hspan.symm _).mp <| sOfh_mem_sq f σ p hp

lemma hAux_sub_X_ex_rep (i : ι) :
    ∃ (r : Relation s),
    r.IsHomogeneous 1 ∧ Relation.eval r = hAux f σ i - MvPolynomial.X i := by
  sorry

noncomputable def relP (p : s) : Relation s :=
  (sOfh_exists_P f s σ p p.property).choose

theorem relP_homogeneous (p : s) : (relP f s σ p).IsHomogeneous 2 :=
  (sOfh_exists_P f s σ p p.property).choose_spec.left

theorem relP_eval (p : s) : Relation.eval (relP f s σ p) = sOfh f σ p :=
  (sOfh_exists_P f s σ p p.property).choose_spec.right

noncomputable def relQ (i : ι) : Relation s :=
  (hAux_sub_X_ex_rep f s σ i).choose

abbrev coefficientRing : Subring R := adjoinRelations (Set.range <| relP f s σ) <|
  adjoinRelations (Set.range <| relQ f s σ) <|
  Subring.adjoinCoefficients (Set.range <| hAux f σ) <|
  (minimalModel s)

abbrev model : Model I where
  s := s
  hs := hs
  R₀ := coefficientRing f s σ
  coeffs := inferInstance

local notation "M" => model f s hs σ
local notation "R₀" => coefficientRing f s σ
local notation "I₀" => Model.I₀ M
local notation "s₀" => Model.s₀ M

example : HasCoefficients s R₀ := inferInstance
example (p : s) : HasRepresentative p.val R₀ := inferInstance

noncomputable def foo (p : s) : MvPolynomial ι R₀ := p.val.descend R₀
noncomputable def hAux₀ (i : ι) : MvPolynomial ι R₀ := (hAux f σ i).descend R₀

set_option maxHeartbeats 500000

noncomputable def σ₀ : MvPolynomial ι R₀ ⧸ I₀ →ₐ[R₀]
    MvPolynomial ι R₀ ⧸ RingHom.ker (Ideal.Quotient.mkₐ R₀ I₀).toRingHom ^ 2 := by
  fapply Ideal.Quotient.liftₐ I₀
  · exact AlgHom.comp
        (Ideal.Quotient.mkₐ R₀ (RingHom.ker (Ideal.Quotient.mkₐ R₀ I₀).toRingHom ^ 2))
        (MvPolynomial.aeval (hAux₀ f s σ))
  . intro a ha
    simp only [AlgHom.comp_apply, ← RingHom.mem_ker]
    erw [Ideal.Quotient.mkₐ_ker R₀ (RingHom.ker (Ideal.Quotient.mkₐ R₀ I₀).toRingHom ^ 2)]
    erw [Ideal.Quotient.mkₐ_ker R₀]
    sorry

variable [Fintype ι]

instance : FormallySmooth (model f s hs σ).R₀ (model f s hs σ).model := by
  fapply FormallySmooth.of_split (Ideal.Quotient.mkₐ R₀ I₀)
  · exact σ₀ f s hs σ
  · sorry

end

open RingOfDefinition

variable [FinitePresentation R A] [FormallySmooth R A]

theorem descent : ∃ (R₀ : Subring R) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra R₀ A₀)
    (_ : A ≃ₐ[R] R ⊗[R₀] A₀),
    FiniteType ℤ R₀ ∧ FinitePresentation R₀ A₀ ∧ FormallySmooth R₀ A₀ := by
  obtain ⟨ι, hfin, f, hfsurj, s, hs⟩ :=
    (FinitePresentation.iff_quotient_mvPolynomial' (R := R) (A := A)).mp inferInstance
  obtain ⟨σ, hsig⟩ := (FormallySmooth.iff_split_surjection f hfsurj).mp inferInstance
  let M : Model (RingHom.ker f) := model f s hs σ
  let f := M.baseChangeIso
  let is := Ideal.quotientKerAlgEquivOfSurjective hfsurj
  refine ⟨M.R₀, M.model, inferInstance, inferInstance, is.symm.trans f, ?_, ?_, ?_⟩
  · sorry
  · sorry
  · fapply FormallySmooth.of_split (Ideal.Quotient.mkₐ M.R₀ M.I₀)
    · sorry
    · sorry

end Smooth
