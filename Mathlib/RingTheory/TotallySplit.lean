/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

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

public section

open TensorProduct

/-- `S` is a finite, totally split `R`-algebra if `S` is isomorphic to `Fin n → R` for some `n`.
Geometrically, this is a trivial cover of degree `n`. -/
class Algebra.IsFiniteSplit (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  nonempty_algEquiv_fun (R S) : ∃ n : ℕ, Nonempty (S ≃ₐ[R] Fin n → R)

namespace Algebra.IsFiniteSplit

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

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

variable {n : ℕ} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/--
If `S` is finite étale over `R` of (constant) rank `n`, there exists
a finite faithfully flat, étale `R`-algebra `T` such that `T ⊗[R] S` is split of rank `n`
over `T`.
This is the commutative algebra version of
[Lenstra, Galois theory for schemes, 5.10][lenstraGSchemes].
-/
lemma exists_tensorProduct_of_etale_of_rankAtStalk [Etale R S] [Module.Finite R S] {n : ℕ}
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

attribute [local instance] Module.FinitePresentation.of_finite_of_finitePresentation in
lemma exists_tensorProduct_of_etale [Module.Finite R S] [Etale R S] (p : PrimeSpectrum R) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T), Etale R T ∧
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R T)) ∧
      IsFiniteSplit T (T ⊗[R] S) := by
  wlog h : ∃ (n : ℕ), Module.rankAtStalk (R := R) S = n
  · obtain ⟨r, hr, hn⟩ := Module.exists_notMem_rankAtStalk_eq S p.asIdeal
    obtain ⟨p', rfl⟩ : p ∈ Set.range
        (PrimeSpectrum.comap <| algebraMap R (Localization.Away r)) := by
      rwa [PrimeSpectrum.localization_away_comap_range _ r]
    obtain ⟨T, _, _, _, ⟨q, rfl⟩, h⟩ := this p' ⟨_, hn⟩
    let _ : Algebra R T := Algebra.compHom T (algebraMap R (Localization.Away r))
    have : IsScalarTower R (Localization.Away r) T := IsScalarTower.of_algebraMap_eq' rfl
    let e : T ⊗[Localization.Away r] (Localization.Away r ⊗[R] S) ≃ₐ[T] T ⊗[R] S :=
      TensorProduct.cancelBaseChange ..
    refine ⟨T, inferInstance, inferInstance, ?_, ⟨q, rfl⟩, ?_⟩
    · exact .comp _ (Localization.Away r) _
    · exact IsFiniteSplit.of_algEquiv (S := T ⊗[Localization.Away r] (Localization.Away r ⊗[R] S)) e
  obtain ⟨n, hn⟩ := h
  obtain ⟨S, _, _, _, _, _, hS⟩ := exists_tensorProduct_of_etale_of_rankAtStalk hn
  obtain ⟨p, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := S) p
  exact ⟨S, inferInstance, inferInstance, inferInstance, ⟨p, rfl⟩, hS⟩

end IsFiniteSplit

end Algebra

section

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R S] [Algebra R B]

/-- A homomorphism of `R`-algebras `f : A →ₐ[R] B` is split if there exist `n`, `m` such
that `A ≃ₐ[R] Fin n → R` and `B ≃ₐ[R] Fin m → R` and modulo these isomorphisms, `f` is induced
by a reindexing `σ : Fin m → Fin n`. -/
def AlgHom.IsFiniteSplit (f : A →ₐ[R] B) : Prop :=
  ∃ (n m : ℕ) (eA : A ≃ₐ[R] Fin n → R) (eB : B ≃ₐ[R] Fin m → R) (σ : Fin m → Fin n),
    f = eB.symm.toAlgHom.comp ((AlgHom.compRight R (fun _ ↦ R) σ).comp eA)

lemma AlgHom.IsFiniteSplit.mk (f : A →ₐ[R] B) {E F : Type*} [_root_.Finite E] [_root_.Finite F]
    (eA : A ≃ₐ[R] (E → R)) (eB : B ≃ₐ[R] (F → R)) (σ : F → E)
    (h : eB.toAlgHom.comp f = (AlgHom.compRight R _ σ).comp eA.toAlgHom) :
    f.IsFiniteSplit := by
  cases nonempty_fintype E
  cases nonempty_fintype F
  let eE := Fintype.equivFin E
  let eF := Fintype.equivFin F
  refine ⟨Fintype.card E, Fintype.card F, eA.trans <| .piCongrLeft R (fun _ ↦ R) eE,
    eB.trans <| .piCongrLeft R (fun _ ↦ R) eF, eE ∘ σ ∘ eF.symm, ?_⟩
  ext x
  apply eB.injective
  ext i
  simp [dsimp% congr($h x), AlgHom.compRight]

variable (S) in
lemma AlgHom.IsFiniteSplit.tensorProductMap {f : A →ₐ[R] B} (hf : f.IsFiniteSplit) :
    (Algebra.TensorProduct.map (.id S S) f).IsFiniteSplit := by
  obtain ⟨n, m, eA, eB, σ, hf⟩ := hf
  refine .mk _
    ((Algebra.TensorProduct.congr .refl eA).trans (Algebra.TensorProduct.piScalarRight ..))
    ((Algebra.TensorProduct.congr .refl eB).trans (Algebra.TensorProduct.piScalarRight ..)) σ ?_
  ext
  simp [hf]

variable (S) in
lemma AlgHom.IsFiniteSplit.iff_of_isScalarTower
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (f : A →ₐ[R] B) :
    (Algebra.TensorProduct.map (.id T T) f).IsFiniteSplit ↔
      (Algebra.TensorProduct.map (.id T T)
        (Algebra.TensorProduct.map (.id S S) f)).IsFiniteSplit := by
  refine ⟨fun ⟨n, m, eA, eB, σ, hf⟩ ↦ ?_, fun ⟨n, m, eA, eB, σ, hf⟩ ↦ ?_⟩
  · refine .mk _ ?_ ?_ σ ?_
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eA
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eB
    · ext a i
      simp [dsimp% congr($hf (1 ⊗ₜ a))]
  · refine .mk _ ?_ ?_ σ ?_
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eA
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eB
    · ext a i
      simp [dsimp% congr($hf (1 ⊗ₜ (1 ⊗ₜ a)))]

end

section

variable {R E F : Type*} [_root_.Finite E] [CommRing R]

/--
If `R` has no non-trivial idempotents, any algebra map `(E → R) → (F → R)` is given by
reindexing.
This lemma assumes `Nonempty E`. For a version assuming `Nontrivial R` instead, see
`AlgHom.eq_compRight_of_forall_isIdempotentElem_or`.
-/
lemma AlgHom.eq_compRight_of_forall_or_of_isIdempotentElem_of_nonempty [Nonempty E]
    (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) (f : (E → R) →ₐ[R] F → R) :
    ∃ (σ : F → E), f = .compRight R _ σ := by
  classical
  nontriviality R
  cases nonempty_fintype E
  have hor (i) (j) : f (Pi.single j 1) i = 0 ∨ f (Pi.single j 1) i = 1 := by
    apply H
    rw [IsIdempotentElem, ← Pi.mul_apply, ← map_mul, ← Pi.single_mul_left]
    simp
  have (x : F) : ∃! (y : E), f (Pi.single y 1) x = 1 := by
    refine existsUnique_of_exists_of_unique ?_ fun a b ha hb ↦ ?_
    · by_contra! hc
      replace hc (y : E) : f (Pi.single y 1) x = 0 := by grind
      have : 1 = ∑ y : E, f (Pi.single y 1) x := by
        rw [← Fintype.sum_apply, ← map_sum, Finset.univ_sum_single, ← Pi.one_def, map_one,
          Pi.one_apply]
      simp [hc] at this
    · by_contra! h
      have : f (Pi.single a 1 * Pi.single b 1) x = f 0 x := by simp [← Pi.single_mul_left, h]
      simp [ha, hb] at this
  choose σ hσ hun using this
  use σ
  ext x i
  induction x using Pi.single_induction with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single j r =>
    rw [← mul_one r, ← smul_eq_mul, Pi.single_smul, map_smul, Pi.smul_apply, smul_eq_mul,
      compRight_apply]
    obtain (h | h) := hor i j <;> grind [Pi.smul_apply, smul_eq_mul]

/-- Variant of `AlgHom.eq_compRight_of_forall_or_of_isIdempotentElem_of_nonempty` that assumes
`Nontrivial R` instead. -/
lemma AlgHom.eq_compRight_of_forall_or_of_isIdempotentElem [Nontrivial R]
    (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) (f : (E → R) →ₐ[R] F → R) :
    ∃ (σ : F → E), f = .compRight R _ σ := by
  cases isEmpty_or_nonempty E
  · have : Subsingleton (F → R) := f.codomain_trivial
    cases isEmpty_or_nonempty F
    · use default, Subsingleton.elim _ _
    · simpa using false_of_nontrivial_of_subsingleton (F → R)
  · exact f.eq_compRight_of_forall_or_of_isIdempotentElem_of_nonempty H

lemma AlgHom.eq_compRight_of_isLocalRing [IsLocalRing R] (f : (E → R) →ₐ[R] F → R) :
    ∃ (σ : F → E), f = .compRight R _ σ := by
  refine f.eq_compRight_of_forall_or_of_isIdempotentElem fun e he ↦ ?_
  rwa [IsLocalRing.isIdempotentElem_iff_eq_zero_or_eq_one] at he

open Localization in
lemma AlgHom.exists_notMem_eq_compRight [_root_.Finite F] (f : (E → R) →ₐ[R] F → R)
    (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (σ : F → E),
      Algebra.TensorProduct.map (.id (Away r) (Away r)) f =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (.compRight _ _ σ) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (E → R) p.primeCompl)
      (E → Localization.AtPrime p) := by
    rw [← isLocalizedModule_iff_isLocalization]
    convert IsLocalizedModule.pi p.primeCompl (fun _ ↦ Algebra.linearMap R (Localization.AtPrime p))
    infer_instance
  have : IsLocalization (Algebra.algebraMapSubmonoid (F → R) p.primeCompl)
      (F → Localization.AtPrime p) := by
    rw [← isLocalizedModule_iff_isLocalization]
    convert IsLocalizedModule.pi p.primeCompl (fun _ ↦ Algebra.linearMap R (Localization.AtPrime p))
    infer_instance
  let fₚ : (E → Localization.AtPrime p) →ₐ[Localization.AtPrime p] F → Localization.AtPrime p :=
    IsLocalization.mapₐ p.primeCompl (Localization.AtPrime p) (E → Localization.AtPrime p)
      (F → Localization.AtPrime p) f
  obtain ⟨σ, hσ⟩ := fₚ.eq_compRight_of_isLocalRing
  let gₚ : (E → Localization.AtPrime p) →ₐ[Localization.AtPrime p] F → Localization.AtPrime p :=
    IsLocalization.mapₐ p.primeCompl (Localization.AtPrime p) (E → Localization.AtPrime p)
      (F → Localization.AtPrime p) (.compRight R (fun _ ↦ R) σ)
  have : fₚ = gₚ := by
    rw [hσ]
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (E → R) p.primeCompl)
    ext x i
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      AlgHom.compRight_apply, IsLocalization.mapₐ_coe, IsLocalization.map_eq, gₚ]
    rfl
  obtain ⟨r, hr, heq⟩ := Module.Finite.exists_algebraTensorProductMap_id_eq _ _ _ _
    f (.compRight R _ σ) this
  exact ⟨r, hr, σ, heq _ (by rfl)⟩

end

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R S] [Algebra R B]

/-- Any algebra map between finite étale algebras, is étale locally finite split. -/
lemma AlgHom.exists_isSplit [Module.Finite R A] [Algebra.Etale R A] [Module.Finite R B]
    [Algebra.Etale R B] (f : A →ₐ[R] B) (p : PrimeSpectrum R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.Etale R S ∧
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) ∧
      (Algebra.TensorProduct.map (AlgHom.id S S) f).IsFiniteSplit := by
  classical
  wlog hA : Algebra.IsFiniteSplit R A
  · obtain ⟨S, _, _, _, ⟨p, rfl⟩, hS⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale p
      (S := A)
    obtain ⟨S', _, _, _, ⟨q, rfl⟩, hS'⟩ := this (Algebra.TensorProduct.map (.id S S) f) p hS
    let _ : Algebra R S' := Algebra.compHom S' (algebraMap R S)
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    refine ⟨S', inferInstance, inferInstance, .comp _ S _, ⟨q, rfl⟩, ?_⟩
    rwa [AlgHom.IsFiniteSplit.iff_of_isScalarTower S]
  wlog hB : Algebra.IsFiniteSplit R B
  · obtain ⟨S, _, _, _, ⟨p, rfl⟩, hS⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale p
      (S := B)
    obtain ⟨S', _, _, _, ⟨q, rfl⟩, hS'⟩ := this
      (A := S ⊗[R] A) (B := S ⊗[R] B) (R := S)
      (Algebra.TensorProduct.map (.id S S) f) p inferInstance hS
    let _ : Algebra R S' := Algebra.compHom S' (algebraMap R S)
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    refine ⟨S', inferInstance, inferInstance, .comp _ S _, ⟨q, rfl⟩, ?_⟩
    rwa [AlgHom.IsFiniteSplit.iff_of_isScalarTower S]
  obtain ⟨n, ⟨eA⟩⟩ := hA
  obtain ⟨m, ⟨eB⟩⟩ := hB
  let f' : (Fin n → R) →ₐ[R] Fin m → R := eB.toAlgHom.comp (f.comp eA.symm.toAlgHom)
  obtain ⟨r, hr, σ, hσ⟩ := AlgHom.exists_notMem_eq_compRight f' p.asIdeal
  refine ⟨Localization.Away r, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rwa [PrimeSpectrum.localization_away_comap_range _ r]
  · let e := TensorProduct.piScalarRight R (Localization.Away r) (Localization.Away r) (Fin m)
    apply AlgHom.IsFiniteSplit.mk _
      (Algebra.TensorProduct.congr .refl eA |>.trans (Algebra.TensorProduct.piScalarRight ..))
      (Algebra.TensorProduct.congr .refl eB |>.trans (Algebra.TensorProduct.piScalarRight ..)) σ
    ext a : 2
    simpa [Algebra.TensorProduct.piScalarRight_tmul, f', e] using congr(e ($(hσ) (1 ⊗ₜ eA a)))

end
