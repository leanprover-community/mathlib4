/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Totally split algebras

An `R`-algebra `S` is finite (totally) split if it is isomorphic to `Fin n → R` for some `n`.
Geometrically, this corresponds to a trivial covering.

Every totally split algebra is finite étale and conversely, every finite étale covering is étale
locally totally split.

## Main results

- `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`: If `S` is finite étale over `R` of
  some constant rank, there exists a faithfully flat, finite étale `R`-algebra `T` such that
  `T ⊗[R] S` is finite split.
-/

universe u

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

lemma of_subsingleton_top [Subsingleton S] : IsFiniteSplit R S :=
  ⟨0, ⟨default⟩⟩

lemma of_subsingleton [Subsingleton R] : IsFiniteSplit R S := by
  have : Subsingleton S := RingHom.codomain_trivial (algebraMap R S)
  exact of_subsingleton_top

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

variable {n : ℕ} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/--
If `S` is finite étale over `R` of (constant) rank `n`, there exists
a finite faithfully flat, étale `R`-algebra `T` such that `T ⊗[R] S` is split of rank `n`
over `T`.
This is the commutative algebra version of
[Lenstra, Galois theory for schemes, 5.10][lenstraGSchemes].
-/
lemma exists_tensorProduct_of_etale [Etale R S] [Module.Finite R S] {n : ℕ}
    (hn : Module.rankAtStalk (R := R) S = n) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T)
      (_ : Module.FaithfullyFlat R T) (_ : Module.Finite R T) (_ : Algebra.Etale R T),
      IsFiniteSplit T (T ⊗[R] S) := by
  induction n generalizing R S with
  | zero =>
    use R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance
    let e : R ⊗[R] S ≃ₐ[R] S := TensorProduct.lid R S
    have : IsFiniteSplit R S := by
      rw [Nat.cast_zero, Module.rankAtStalk_eq_zero_iff_subsingleton] at hn
      exact of_subsingleton_top
    apply IsFiniteSplit.of_algEquiv e.symm
  | succ n ih =>
    cases subsingleton_or_nontrivial R
    · use R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance
      have : IsFiniteSplit R S := .of_subsingleton
      exact .of_algEquiv (TensorProduct.lid R S).symm
    have : Nontrivial S := by
      apply Module.nontrivial_of_rankAtStalk_pos (R := R)
      simp [hn]
    /- Because `S` is unramified over `R`, there exists an `S`-algebra `U` such that
    `S ⊗[R] S ≃ₐ[S] S × U`. -/
    obtain ⟨U, _, _, ⟨e⟩⟩ := Algebra.FormallyUnramified.exists_algEquiv_prod R S
    algebraize [RingHom.snd S U]
    have : IsScalarTower S (S × U) U := IsScalarTower.of_algebraMap_eq' rfl
    have : Etale S U := by
      have : Etale S (S × U) := Etale.of_equiv e
      exact .comp S (S × U) U
    have : Module.Finite S U := by
      have : Module.Finite S (S × U) := Module.Finite.equiv e.toLinearEquiv
      have : Module.Finite (S × U) U :=
        Module.Finite.of_surjective (Algebra.linearMap (S × U) U) (RingHom.snd S U).surjective
      exact Module.Finite.trans (S × U) _
    have (p : PrimeSpectrum S) : Module.rankAtStalk (R := S) (S × U) p = n + 1 := by
      simp [Module.rankAtStalk_eq_of_equiv e.symm.toLinearEquiv, Module.rankAtStalk_baseChange, hn]
    simp_rw [Module.rankAtStalk_prod , Module.rankAtStalk_self, Pi.add_apply, Pi.one_apply] at this
    /- Since the `S`-rank of `S × U = S ⊗[R] S` is `n + 1`, the `S`-rank of `U` is `n`,
    so we may apply the induction hypothesis on `U`. -/
    have : Module.rankAtStalk (R := S) U = n := by
      ext p
      simp only [Pi.natCast_def, Nat.cast_id]
      grind
    /- We obtain a finite étale, faithfully flat `S`-algebra `V` such that `V ⊗[S] U` is finite
    split. We claim that `V` viewed as an `R`-algebra works. -/
    obtain ⟨V, _, _, _, _, _, hV⟩ := ih this
    obtain ⟨n, ⟨f⟩⟩ := hV.nonempty_algEquiv_fun
    algebraize [(algebraMap S V).comp (algebraMap R S)]
    let e : V ⊗[R] S ≃ₐ[V] Unit ⊕ Fin n → V :=
      (Algebra.TensorProduct.cancelBaseChange R S V V S).symm.trans <|
        (TensorProduct.congr AlgEquiv.refl e).trans <|
        (TensorProduct.prodRight S V V S U).trans <|
        (AlgEquiv.prodCongr (TensorProduct.rid S V V) f).trans <|
        (AlgEquiv.prodCongr (AlgEquiv.funUnique _ _ _).symm AlgEquiv.refl).trans
        (AlgEquiv.sumArrowEquivProdArrow Unit (Fin n) V V).symm
    refine ⟨V, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
    · have : Module.FaithfullyFlat R S := by
        apply Module.FaithfullyFlat.of_comap_surjective
        rw [← PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective]
        intro p
        simp [hn]
      exact Module.FaithfullyFlat.trans R S V
    · exact Module.Finite.trans S V
    · exact Algebra.Etale.comp R S V
    · exact .of_algEquiv e.symm

end IsFiniteSplit

end Algebra
