/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Totally split algebras

An `R`-algebra `S` is finite (totally) split if it is isomorphic to `Fin n → R` for some `n`.
Geometrically, this corresponds to a trivial covering.

Every totally split algebra is finite étale and conversely, every finite étale covering is étale
locally totally split (TODO, @chrisflav).
-/

@[expose] public section

open TensorProduct

/-- `S` is a finite, totally split `R`-algebra if `S` is isomorphic to `Fin n → R` for some `n`.
Geometrically, this is a trivial cover of degree `n`. -/
class Algebra.IsFiniteSplit (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  nonempty_algEquiv_fun (R S) : ∃ n : ℕ, Nonempty (S ≃ₐ[R] Fin n → R)

namespace Algebra.IsFiniteSplit

variable {k R S : Type*} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra R S]

instance {T : Type*} [CommRing T] [Algebra R T] [IsFiniteSplit R S] :
    IsFiniteSplit T (T ⊗[R] S) := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R S
  refine ⟨n, ⟨?_⟩⟩
  exact (TensorProduct.congr AlgEquiv.refl e).trans
    ((TensorProduct.piRight R T T (fun _ : Fin n ↦ R)).trans <|
      AlgEquiv.piCongrRight fun i ↦ TensorProduct.rid R T T)

instance {ι : Type*} [Finite ι] : IsFiniteSplit R (ι → R) where
  nonempty_algEquiv_fun := by
    cases nonempty_fintype ι
    exact ⟨_, ⟨AlgEquiv.piCongrLeft' _ _ (Fintype.equivFin ι)⟩⟩

lemma of_algEquiv {S' : Type*} [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') [IsFiniteSplit R S] :
    IsFiniteSplit R S' := by
  obtain ⟨n, ⟨f⟩⟩ := nonempty_algEquiv_fun R S
  exact ⟨n, ⟨e.symm.trans f⟩⟩

instance : IsFiniteSplit R R :=
  .of_algEquiv (AlgEquiv.funUnique (ι := Fin 1) _ _)

lemma of_subsingleton [Subsingleton R] : IsFiniteSplit R S := by
  have : Subsingleton S := RingHom.codomain_trivial (algebraMap R S)
  exact ⟨0, ⟨default⟩⟩

instance [IsFiniteSplit R S] : Module.Free R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact Module.Free.of_equiv e.symm.toLinearEquiv

instance [IsFiniteSplit R S] : Module.FinitePresentation R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  apply Module.FinitePresentation.of_equiv e.symm.toLinearEquiv

instance [IsFiniteSplit R S] : Etale R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact .of_equiv e.symm

variable (k) in
lemma bijective_algebraMap_quotient [Algebra.IsFiniteSplit k R] (p : Ideal R) [p.IsPrime] :
    Function.Bijective (algebraMap k (R ⧸ p)) := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun k R
  let p' : Ideal (Fin n → k) := p.comap e.symm
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq ⟨p', inferInstance⟩
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  let g : (R ⧸ p) ≃ₐ[k] k :=
    (Ideal.quotientEquivAlg _ p' e <| Ideal.comap_symm e.toRingEquiv).trans <|
    (Ideal.quotientEquivAlgOfEq k congr($(hq).asIdeal).symm).trans <|
    Ideal.quotientKerAlgEquivOfSurjective (f := Pi.evalAlgHom k (fun _ ↦ k) i)
      (Function.surjective_eval _)
  simpa [← g.symm.toAlgHom.comp_algebraMap] using g.symm.bijective

variable (k R) in
/-- If `R` is finite split over a field `k`, the `k`-rational points of `R`
are in one-to-one correspondence with its prime spectrum. -/
noncomputable
def algHomEquivPrimeSpectrum [Algebra.IsFiniteSplit k R] : (R →ₐ[k] k) ≃ PrimeSpectrum R where
  toFun f := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  invFun p := AlgHom.comp
    (AlgEquiv.ofBijective (Algebra.ofId _ _) (bijective_algebraMap_quotient _ _)).symm.toAlgHom
    (Ideal.Quotient.mkₐ _ p.asIdeal)
  left_inv f := by
    ext
    dsimp
    have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    apply (AlgEquiv.ofBijective (ofId k (R ⧸ RingHom.ker f))
      (bijective_algebraMap_quotient _ _)).injective
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.coe_ofBijective, ofId_apply,
      IsScalarTower.algebraMap_apply k R]
    simp [-Ideal.Quotient.mk_algebraMap, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  right_inv p := by
    ext : 1
    dsimp
    rw [← AlgHom.comap_ker, ← RingHom.ker_coe_toRingHom, AlgHomClass.toRingHom_toAlgHom,
      AlgHom.ker_coe_equiv, ← RingHom.ker_eq_comap_bot, ← RingHom.ker_coe_toRingHom,
      Ideal.Quotient.mkₐ_ker]

instance [IsSepClosed k] [EssFiniteType k R] [FormallyEtale k R] : IsFiniteSplit k R := by
  have := Algebra.FormallyUnramified.finite_of_free k R
  have : IsArtinianRing R := isArtinian_of_tower k inferInstance
  exact .of_algEquiv (Algebra.FormallyEtale.equivPiOfIsSepClosed k R).symm

end IsFiniteSplit

end Algebra
