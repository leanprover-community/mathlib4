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

-- TODO: move me
lemma _root_.Algebra.exists_cover_rankAtStalk_eq {R : Type*} (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FinitePresentation R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p,
      Module.rankAtStalk (R := Localization.Away r) (Localization.Away r ⊗[R] S) =
        Module.rankAtStalk S ⟨p, inferInstance⟩ := by
  obtain ⟨U, hU, hp, heq⟩ := (Module.isLocallyConstant_rankAtStalk (M := S)).exists_open ⟨p, ‹_›⟩
  obtain ⟨V, ⟨r, rfl⟩, (hr : r ∉ p), hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hU
  refine ⟨r, hr, ?_⟩
  ext q
  rw [Module.rankAtStalk_baseChange]
  apply heq
  apply hrU
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.mem_compl_iff,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff,
    SetLike.mem_coe]
  obtain ⟨-, b⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint (.powers r) _ q.asIdeal).mp q.2
  rw [Set.disjoint_left] at b
  simp only [SetLike.mem_coe, Ideal.coe_comap, Set.mem_preimage] at b
  apply b
  use 1
  simp

attribute [local instance] Module.FinitePresentation.of_finite_of_finitePresentation in
lemma exists_tensorProduct_of_etale [Module.Finite R S] [Etale R S] (p : PrimeSpectrum R) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      Etale R T ∧
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R T)) ∧
      IsFiniteSplit T (T ⊗[R] S) := by
  wlog h : ∃ (n : ℕ), Module.rankAtStalk (R := R) S = n
  · obtain ⟨r, hr, hn⟩ := Algebra.exists_cover_rankAtStalk_eq S p.asIdeal
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

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
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
  refine ⟨Fintype.card E, Fintype.card F, eA.trans ?_, eB.trans ?_, eE ∘ σ ∘ eF.symm, ?_⟩
  · exact AlgEquiv.piCongrLeft R (fun _ ↦ R) eE
  · exact AlgEquiv.piCongrLeft R (fun _ ↦ R) eF
  · ext x
    apply eB.injective
    have := DFunLike.congr_fun h x
    simp only [AlgEquiv.toAlgHom_eq_coe, coe_comp, AlgHom.coe_coe, Function.comp_apply] at this
    ext i
    simp [this, AlgHom.compRight]

variable (S) in
lemma AlgHom.IsFiniteSplit.tensorProductMap {f : A →ₐ[R] B} (hf : f.IsFiniteSplit) :
    (Algebra.TensorProduct.map (.id S S) f).IsFiniteSplit := by
  obtain ⟨n, m, eA, eB, σ, hf⟩ := hf
  refine AlgHom.IsFiniteSplit.mk (E := Fin n) (F := Fin m) _
    ((Algebra.TensorProduct.congr .refl eA).trans (Algebra.TensorProduct.piScalarRight ..))
    ((Algebra.TensorProduct.congr .refl eB).trans (Algebra.TensorProduct.piScalarRight ..)) σ ?_
  ext a
  simp [hf]

variable (S) in
lemma AlgHom.IsFiniteSplit.iff_of_isScalarTower
    (T : Type u) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (f : A →ₐ[R] B) :
    (Algebra.TensorProduct.map (.id T T) f).IsFiniteSplit ↔
      (Algebra.TensorProduct.map (.id T T)
        (Algebra.TensorProduct.map (.id S S) f)).IsFiniteSplit := by
  refine ⟨?_, ?_⟩
  · rintro ⟨n, m, eA, eB, σ, hf⟩
    refine AlgHom.IsFiniteSplit.mk (E := Fin n) (F := Fin m) _ ?_ ?_ σ ?_
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eA
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eB
    ext a i
    have := DFunLike.congr_fun hf (1 ⊗ₜ a)
    simp only [Algebra.TensorProduct.map_tmul, coe_id, id_eq, AlgEquiv.toAlgHom_eq_coe, coe_comp,
      AlgHom.coe_coe, Function.comp_apply] at this
    simp [this]
  · rintro ⟨n, m, eA, eB, σ, hf⟩
    refine AlgHom.IsFiniteSplit.mk (E := Fin n) (F := Fin m) _ ?_ ?_ σ ?_
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eA
    · exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eB
    ext a i
    have := DFunLike.congr_fun hf (1 ⊗ₜ (1 ⊗ₜ a))
    simp only [Algebra.TensorProduct.map_tmul, coe_id, id_eq, AlgEquiv.toAlgHom_eq_coe, coe_comp,
      AlgHom.coe_coe, Function.comp_apply] at this
    simp [this]

lemma AlgHom.eq_compRight_of_no_nontrivial_isIdempotentElem {R E F : Type*} [_root_.Finite E]
    [Nonempty E] [CommRing R] (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (f : (E → R) →ₐ[R] F → R) : ∃ (σ : F → E), f = .compRight R _ σ := by
  nontriviality R
  cases nonempty_fintype E
  classical
  have hor (i) (j) : f (Pi.single j 1) i = 0 ∨ f (Pi.single j 1) i = 1 := by
    apply H
    unfold IsIdempotentElem
    rw [← Pi.mul_apply, ← map_mul, ← Pi.single_mul_left]
    simp
  have (x : F) : ∃ (y : E), f (Pi.single y 1) x = 1 := by
    by_contra! hc
    replace hc (y : E) : f (Pi.single y 1) x = 0 := by
      obtain (h|h) := hor x y
      · assumption
      · simp [hc] at h
    have : 1 = ∑ y : E, f (Pi.single y 1) x := by
      rw [← Fintype.sum_apply]
      rw [← map_sum, Finset.univ_sum_single, ← Pi.one_def, map_one, Pi.one_apply]
    simp_rw [hc] at this
    simp at this
  have (x : F) : ∃! (y : E), f (Pi.single y 1) x = 1 := by
    apply existsUnique_of_exists_of_unique
    · exact this x
    · intro a b ha hb
      by_contra! h
      have : (Pi.single a 1) * (Pi.single b 1 : E → R) = 0 := by
        simp [← Pi.single_mul_left, h]
      apply_fun ((f ·) · x) at this
      simp [ha, hb] at this
  choose σ hσ hun using this
  use σ
  simp only at hσ
  ext x i
  induction x using Pi.single_induction with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single j r =>
      have : Pi.single j r = r • (Pi.single j 1 : E → R) := by simp [← Pi.single_smul]
      rw [this]
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, AlgHom.compRight_apply]
      congr
      obtain (h|h) := hor i j
      · have : j ≠ σ i := by
          intro hj
          subst hj
          simp [hσ] at h
        simp [this, h]
      · have := hun i j h
        subst this
        simp [hσ]

lemma AlgHom.eq_compRight_of_no_nontrivial_isIdempotentElem' {R E F : Type*} [_root_.Finite E]
    [CommRing R] [Nontrivial R] (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (f : (E → R) →ₐ[R] F → R) : ∃ (σ : F → E), f = .compRight R _ σ := by
  cases isEmpty_or_nonempty E
  · have : Subsingleton (F → R) := f.codomain_trivial
    cases isEmpty_or_nonempty F
    · use default
      apply Subsingleton.elim
    · simpa using false_of_nontrivial_of_subsingleton (F → R)
  · apply eq_compRight_of_no_nontrivial_isIdempotentElem H

lemma IsIdempotentElem.eq_one_of_isUnit {R : Type*} [CommRing R]
    {e : R} (he : IsIdempotentElem e) (heu : IsUnit e) : e = 1 := by
  rw [eq_comm, ← sub_eq_zero]
  apply heu.mul_left_cancel
  simp [he]

lemma IsLocalRing.isIdempotentElem_iff_eq_zero_or_eq_one {R : Type*} [CommRing R] [IsLocalRing R]
    {e : R} : IsIdempotentElem e ↔ e = 0 ∨ e = 1 := by
  refine ⟨fun he ↦ ?_, ?_⟩
  · obtain (h|h) := IsLocalRing.isUnit_or_isUnit_one_sub_self e
    · exact Or.inr (he.eq_one_of_isUnit h)
    · exact Or.inl (by simpa using he.one_sub.eq_one_of_isUnit h)
  · rintro (h|h) <;> subst h
    · exact IsIdempotentElem.zero
    · exact IsIdempotentElem.one

lemma RingHom.eq_compRight_of_isLocalHom {R E F : Type*} [_root_.Finite E] [CommRing R]
    (f : (E → R) →ₐ[R] F → R) [IsLocalRing R] :
    ∃ (σ : F → E), f = .compRight R _ σ := by
  apply AlgHom.eq_compRight_of_no_nontrivial_isIdempotentElem'
  intro e he
  rwa [IsLocalRing.isIdempotentElem_iff_eq_zero_or_eq_one] at he

open Localization in
lemma AlgHom.exists_cover_eq_of_eq {R A B : Type*} [CommRing R] (S : Submonoid R)
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Finite R A]
    (Rₚ : Type*) (Aₚ Bₚ : Type u) [CommRing Rₚ] [CommRing Aₚ] [CommRing Bₚ]
    [Algebra R Rₚ] [Algebra R Aₚ] [Algebra R Bₚ] [Algebra Rₚ Aₚ] [Algebra Rₚ Bₚ]
    [Algebra A Aₚ] [Algebra B Bₚ]
    [IsScalarTower R A Aₚ] [IsScalarTower R B Bₚ] [IsScalarTower R Rₚ Aₚ] [IsScalarTower R Rₚ Bₚ]
    [IsLocalization S Rₚ] [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid B S) Bₚ]
    (f g : A →ₐ[R] B) (hf : IsLocalization.mapₐ S Rₚ Aₚ Bₚ f = IsLocalization.mapₐ S Rₚ Aₚ Bₚ g) :
    ∃ (r : S),
      Algebra.TensorProduct.map (.id (Away r.val) (Away r.val)) f =
        Algebra.TensorProduct.map (.id (Away r.val) (Away r.val)) g := by
  let u : B →ₗ[R] Bₚ := (IsScalarTower.toAlgHom R B Bₚ).toLinearMap
  have : IsLocalizedModule S u := by
    simp only [u]
    rw [isLocalizedModule_iff_isLocalization]
    infer_instance
  obtain ⟨s, hs⟩ := by
    refine Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S
      (N := B) (N' := Bₚ) (M := A) u f g ?_
    ext x
    simpa using DFunLike.congr_fun hf (algebraMap A Aₚ x)
  use s
  ext a
  simp only [Algebra.TensorProduct.map_restrictScalars_comp_includeRight, coe_comp,
    Function.comp_apply, Algebra.TensorProduct.includeRight_apply]
  have hun : IsUnit ((algebraMap R (Away s.val ⊗[R] B) s)) := by
    rw [IsScalarTower.algebraMap_apply R (Away s.val) _]
    apply (IsLocalization.Away.algebraMap_isUnit s.val).map
  suffices s.val • ((1 : Away s.val) ⊗ₜ[R] f a) = s.val • (1 ⊗ₜ[R] g a) by
    apply hun.mul_left_cancel
    rwa [← Algebra.smul_def, ← Algebra.smul_def]
  have := DFunLike.congr_fun hs a
  dsimp at this
  rw [← TensorProduct.tmul_smul]
  rw [← TensorProduct.tmul_smul]
  rw [← Submonoid.smul_def, this, ← Submonoid.smul_def]

-- TODO: fix `IsLocalization.mapₐ` to have the correct universe generality
open Localization in
lemma AlgHom.exists_cover_eq_compRight'' {R : Type*} {E F : Type u}
    [_root_.Finite E] [_root_.Finite F]
    [CommRing R]
    (f : (E → R) →ₐ[R] F → R) (p : Ideal R) [p.IsPrime] :
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
    IsLocalization.mapₐ p.primeCompl (Localization.AtPrime p)
      (E → Localization.AtPrime p)
      (F → Localization.AtPrime p) f
  obtain ⟨σ, hσ⟩ := RingHom.eq_compRight_of_isLocalHom fₚ
  let gₚ : (E → Localization.AtPrime p) →ₐ[Localization.AtPrime p] F → Localization.AtPrime p :=
    IsLocalization.mapₐ p.primeCompl (Localization.AtPrime p)
      (E → Localization.AtPrime p)
      (F → Localization.AtPrime p) (.compRight R (fun _ ↦ R) σ)
  have : fₚ = gₚ := by
    rw [hσ]
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (E → R) p.primeCompl)
    ext x i
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      AlgHom.compRight_apply, IsLocalization.mapₐ_coe, IsLocalization.map_eq, gₚ]
    rfl
  obtain ⟨⟨r, hr⟩, heq⟩ := AlgHom.exists_cover_eq_of_eq _ _ _ _ f (.compRight R _ σ) this
  exact ⟨r, hr, σ, heq⟩

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
    refine ⟨S', inferInstance, inferInstance, ?_, ⟨q, rfl⟩, ?_⟩
    · exact .comp _ S _
    · rwa [AlgHom.IsFiniteSplit.iff_of_isScalarTower S]
  wlog hB : Algebra.IsFiniteSplit R B
  · obtain ⟨S, _, _, _, ⟨p, rfl⟩, hS⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale p
      (S := B)
    obtain ⟨S', _, _, _, ⟨q, rfl⟩, hS'⟩ := this
      (A := S ⊗[R] A) (B := S ⊗[R] B) (R := S)
      (Algebra.TensorProduct.map (.id S S) f) p inferInstance hS
    let _ : Algebra R S' := Algebra.compHom S' (algebraMap R S)
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    refine ⟨S', inferInstance, inferInstance, ?_, ⟨q, rfl⟩, ?_⟩
    · exact .comp _ S _
    · rwa [AlgHom.IsFiniteSplit.iff_of_isScalarTower S]
  obtain ⟨n, ⟨eA⟩⟩ := hA
  obtain ⟨m, ⟨eB⟩⟩ := hB
  let f' : (Fin n → R) →ₐ[R] Fin m → R := eB.toAlgHom.comp (f.comp eA.symm.toAlgHom)
  obtain ⟨r, hr, σ, hσ⟩ := AlgHom.exists_cover_eq_compRight'' f' p.asIdeal
  refine ⟨Localization.Away r, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · infer_instance
  · change p ∈ Set.range (PrimeSpectrum.comap <| algebraMap R (Localization.Away r))
    rwa [PrimeSpectrum.localization_away_comap_range _ r]
  · let e := TensorProduct.piScalarRight R (Localization.Away r) (Localization.Away r) (Fin m)
    apply AlgHom.IsFiniteSplit.mk (E := Fin n) (F := Fin m) _
      (Algebra.TensorProduct.congr .refl eA |>.trans (Algebra.TensorProduct.piScalarRight ..))
      (Algebra.TensorProduct.congr .refl eB |>.trans (Algebra.TensorProduct.piScalarRight ..)) σ
    ext a : 2
    simpa [Algebra.TensorProduct.piScalarRight_tmul, f', e] using congr(e ($(hσ) (1 ⊗ₜ eA a)))

end
