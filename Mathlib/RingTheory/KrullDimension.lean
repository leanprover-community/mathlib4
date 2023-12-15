/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/

import Mathlib.Order.KrullDimension
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Noetherian
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Topology.NoetherianSpace
import Mathlib.Tactic.IntervalCases

/-!
# Krull dimension of a (commutative) ring

The ring theoretic krull dimension is the order theoretic krull dimension applied to its prime
spectrum. Unfolding this definition, it is the length of longest series of prime ideals ordered by
inclusion.

## Results
- `ringKrullDim.eq_of_ringEquiv` : isomorphic rings have equal krull dimension
- `primeIdealHeight_eq_ringKrullDim_of_Localization` : the height of a prime ideal `𝔭` is equal to
  krull dimension of `R_𝔭`
-/

/--
The ring theoretic Krull dimension is the Krull dimension of prime spectrum ordered by inclusion.
-/
noncomputable abbrev ringKrullDim (R : Type _) [CommRing R] : WithBot (WithTop ℕ) :=
  krullDim (PrimeSpectrum R)

namespace ringKrullDim

open PrimeSpectrum OrderDual in
lemma eq_topologicalKrullDim (R : Type _) [CommRing R] :
    ringKrullDim R = topologicalKrullDim (PrimeSpectrum R) :=
  Eq.symm $ krullDim.eq_orderDual.trans $ krullDim.eq_of_orderIso $ OrderIso.symm {
    toFun := fun p ↦ ⟨zeroLocus p.asIdeal, isClosed_zeroLocus p.asIdeal,
      isIrreducible_zeroLocus_iff _ |>.mpr <| by simpa only [p.IsPrime.radical] using p.IsPrime⟩
    invFun := (fun s ↦ ⟨vanishingIdeal s.1, isIrreducible_iff_vanishingIdeal_isPrime.mp s.2.2⟩)
    left_inv := fun p ↦ PrimeSpectrum.ext _ _ <|
      by simp [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, p.IsPrime.radical]
    right_inv := fun s ↦ Subtype.ext <|
      by simpa [zeroLocus_vanishingIdeal_eq_closure] using s.2.1.closure_eq
    map_rel_iff' := by
      intro p q
      change zeroLocus _ ≤ zeroLocus _ ↔ _
      simp [zeroLocus_subset_zeroLocus_iff, q.IsPrime.radical] }

/--
If `R ⟶ S` is a surjective ring homomorphism, then `ringKrullDim S ≤ ringKrullDim R`.
-/
theorem le_of_surj (R S : Type _) [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) : ringKrullDim S ≤ ringKrullDim R :=
  krullDim.le_of_strictMono (PrimeSpectrum.comap f) (Monotone.strictMono_of_injective
    (fun _ _ hab ↦ Ideal.comap_mono hab) (PrimeSpectrum.comap_injective_of_surjective f hf))

/--
If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringKrullDim R`.
-/
theorem le_of_quot (R : Type _) [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim R :=
  le_of_surj _ _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/--
If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`.
-/
theorem eq_of_ringEquiv (R S : Type _) [CommRing R] [CommRing S] (e : R ≃+* S) :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm (le_of_surj S R (RingEquiv.symm e) (EquivLike.surjective (RingEquiv.symm e)))
    (le_of_surj R S e (EquivLike.surjective e))

section field

instance primeSpectrum_unique_of_field (F : Type _) [Field F] : Unique (PrimeSpectrum F) where
  default := ⟨⊥, Ideal.bot_prime⟩
  uniq := fun p ↦ PrimeSpectrum.ext _ _ $ Ideal.ext $ fun x ↦ by
    refine ⟨fun h ↦ ?_, fun h ↦ h.symm ▸ Submodule.zero_mem _⟩
    rwa [p.asIdeal.eq_bot_of_prime] at h

instance finiteDimensionalType_of_field (F : Type _) [Field F] :
  FiniteDimensionalOrder (PrimeSpectrum F) := inferInstance

lemma eq_zero_of_Field (F : Type _) [Field F] : ringKrullDim F = 0 :=
  krullDim.eq_zero_of_unique

end field

section dimension_0

variable {R : Type _} [CommRing R]

lemma _root_.Ideal.IsPrime.isMaximal_of_dim_zero
    {I : Ideal R} (h : I.IsPrime) (dim0 : ringKrullDim R = 0) :
    I.IsMaximal := by
  obtain ⟨J, hJ1, hJ2⟩ := I.exists_le_maximal h.1
  by_cases hIJ : I = J
  · subst hIJ; exact hJ1
  let x : LTSeries (PrimeSpectrum R) :=
  { length := 1
    toFun := ![⟨I, h⟩, ⟨J, hJ1.isPrime⟩]
    step := by
      intro i
      fin_cases i
      simp only [Fin.zero_eta, Fin.castSucc_zero, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        Matrix.cons_val_one, Matrix.head_cons, ← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine ⟨hJ2, fun r ↦ ?_⟩
      exact hIJ <| Eq.symm <| hJ1.eq_of_le h.1 r }
  have : 1 ≤ ringKrullDim R :=
    le_iSup (α := WithBot (WithTop ℕ)) (f := fun x : LTSeries _ ↦ x.length) x
  rw [dim0] at this
  norm_num at this

lemma _root_.Ideal.IsPrime.isMinimal_of_dim_zero
    {I : Ideal R} (h : I.IsPrime) (dim0 : ringKrullDim R = 0) :
    I ∈ minimalPrimes R := by
  obtain ⟨p, hp, le⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := I) bot_le
  by_cases hIp : I = p
  · subst hIp; exact hp
  let x : LTSeries (PrimeSpectrum R) :=
  { length := 1
    toFun := ![⟨p, hp.1.1⟩, ⟨I, h⟩]
    step := by
      intro i
      fin_cases i
      simp only [Fin.zero_eta, Fin.castSucc_zero, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        Matrix.cons_val_one, Matrix.head_cons, ← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine ⟨le, ?_⟩
      contrapose! hIp
      exact le_antisymm hIp le }
  have : 1 ≤ ringKrullDim R :=
    le_iSup (α := WithBot (WithTop ℕ)) (f := fun x : LTSeries _ ↦ x.length) x
  rw [dim0] at this
  norm_num at this

end dimension_0

section artinian_and_noetherian

variable (R : Type _) [CommRing R] [Nontrivial R]

lemma eq_zero_of_isArtinianRing [IsArtinianRing R] : ringKrullDim R = 0 := by
  rw [ringKrullDim, krullDim.eq_iSup_height]
  suffices : ∀ (a : PrimeSpectrum R), height (PrimeSpectrum R) a = 0
  · simp_rw [this]; rw [iSup_const]
  · intro p
    refine le_antisymm (iSup_le fun x ↦ ?_) krullDim.nonneg_of_Nonempty
    erw [WithBot.coe_le_coe, WithTop.coe_le_coe]
    by_contra! r
    have : x 0 < x 1 := by
      let hx := x.step ⟨0, r⟩
      rw [show (Fin.castSucc { val := 0, isLt := r }) = 0 by exact rfl,
        show (Fin.succ { val := 0, isLt := r }) = 1 by
        rw [show (Fin.succ { val := 0, isLt := r }) = 0 + 1 by
        exact Fin.ext $ Eq.symm (Fin.val_add_one_of_lt r)];
        exact Fin.zero_add 1] at hx
      exact hx
    haveI H0 : (x 0).1.asIdeal.IsMaximal := inferInstance
    exact ne_of_lt this (show x 0 = x 1 by
      rw [Subtype.ext_iff_val, PrimeSpectrum.ext_iff];
      exact H0.eq_of_le (x 1).1.IsPrime.1 (le_of_lt this))

variable {R} in
noncomputable def _root_.PrimeSpectrum.finTypeOfNoetherian
    [IsNoetherianRing R] (h : ringKrullDim R = 0) :
    Fintype (PrimeSpectrum R) :=
  letI fin1 : Fintype (minimalPrimes R) := @Fintype.ofFinite _ <|
    Set.finite_coe_iff.mpr <| minimalPrimes.finiteOfIsNoetherianRing R
  Fintype.ofInjective
    (fun p ↦ ⟨p.asIdeal, p.IsPrime.isMinimal_of_dim_zero h⟩ : PrimeSpectrum R → minimalPrimes R)
    (fun _ _ H ↦ PrimeSpectrum.ext _ _ <| Subtype.ext_iff.mp H)

open TopologicalSpace in
lemma artinian_of_zero_dimensional_noetherian [IsNoetherianRing R] (h : ringKrullDim R = 0) :
    IsArtinianRing R := by
  letI : Fintype (PrimeSpectrum R) := PrimeSpectrum.finTypeOfNoetherian h

  sorry

end artinian_and_noetherian

section PID

variable (R : Type _) [CommRing R] [IsPrincipalIdealRing R] [IsDomain R] (hR : ¬ IsField R)

noncomputable def _root_.LTSeries.ofPID : LTSeries (PrimeSpectrum R) where
  length := 1
  toFun :=
    ![⟨⊥, Ideal.bot_prime⟩,
      ⟨(Ideal.exists_maximal R).choose, (Ideal.exists_maximal R).choose_spec.isPrime⟩]
  step := by
   intro i
   fin_cases i
   rw [show ⟨⊥, _⟩ = (⊥ : PrimeSpectrum R) by rfl]
   exact @Ideal.bot_lt_of_maximal R _ _ (Ideal.exists_maximal R).choose
     (Ideal.exists_maximal R).choose_spec hR

lemma _root_.LTSeries.ofPID_isLongest (x : LTSeries (PrimeSpectrum R)) : x.length ≤ 1 := by
  by_contra! rid
  have m := LTSeries.strictMono x
  rcases x with ⟨l, f, s⟩
  let a := Submodule.IsPrincipal.generator (f 1).asIdeal
  let b := Submodule.IsPrincipal.generator (f 2).asIdeal
  have hf1 : (f 1).asIdeal ≠ ⊥ := fun h ↦ by
    have : (f 0).asIdeal < (f 1).asIdeal
    · simpa only [show 0 = Fin.castSucc ⟨0, Nat.lt_of_succ_lt rid⟩ by rfl, show 1 = Fin.succ
        ⟨0, Nat.lt_of_succ_lt rid⟩ from Fin.ext <| Nat.mod_eq_of_lt <| by linarith] using
        s ⟨0, Nat.lt_of_succ_lt rid⟩
    rw [h] at this
    exact (not_le_of_lt this bot_le).elim
  have hf12 : (f 1).asIdeal < (f 2).asIdeal := by
    simpa only [show 1 = Fin.castSucc ⟨1, rid⟩ from Fin.ext <| Nat.mod_eq_of_lt <| by linarith,
      show 2 = Fin.succ ⟨1, rid⟩ from Fin.ext <| Nat.mod_eq_of_lt <| by linarith] using
      s ⟨1, rid⟩
  have lt1 : Ideal.span {a} < Ideal.span {b} := by
    rw [Ideal.span_singleton_generator, Ideal.span_singleton_generator]
    exact hf12
  rw [Ideal.span_singleton_lt_span_singleton] at lt1
  rcases lt1 with ⟨h, ⟨r, hr1, hr2⟩⟩
  have ha : Prime a := Submodule.IsPrincipal.prime_generator_of_isPrime (f 1).asIdeal hf1
  have hb : Prime b := Submodule.IsPrincipal.prime_generator_of_isPrime (f 2).asIdeal $
    Iff.mp bot_lt_iff_ne_bot (lt_trans (Ne.bot_lt hf1) hf12)
  obtain ⟨x, hx⟩ := (hb.dvd_prime_iff_associated ha).mp ⟨r, hr2⟩
  rw [← hx] at hr2
  rw [← mul_left_cancel₀ h hr2] at hr1
  exact (hr1 x.isUnit).elim

/--
Any PID that is not a field is finite dimensional with dimension 1.
-/
lemma PID_finiteDimensional (R : Type _) [CommRing R] [IsPrincipalIdealRing R]
    [IsDomain R] (hR : ¬ IsField R) :
    FiniteDimensionalOrder (PrimeSpectrum R) where
  exists_longest_relSeries :=
    ⟨LTSeries.ofPID R hR, LTSeries.ofPID_isLongest R⟩

lemma PID_eq_one_of_not_isField (R : Type _) [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
    (hR : ¬ IsField R) : ringKrullDim R = 1 := by
  rw [ringKrullDim, @krullDim.eq_len_of_finiteDimensionalType _ _ (PID_finiteDimensional _ hR)]
  have := PID_finiteDimensional R hR
  simp only [Nat.cast_eq_one]
  exact Eq.symm <| LTSeries.longestOf_len_unique (α := (PrimeSpectrum R))
    (LTSeries.ofPID R hR) <| LTSeries.ofPID_isLongest R

end PID

/--
https://stacks.math.columbia.edu/tag/00KG
-/
lemma eq_iSup_height_maximal_ideals (R : Type _) [CommRing R] : ringKrullDim R =
    ⨆ (p : PrimeSpectrum R) (_ : p.asIdeal.IsMaximal), height (PrimeSpectrum R) p := by
  refine' krullDim.eq_iSup_height.trans $ le_antisymm ?_ ?_
  · exact iSup_le $ fun p ↦ by
      rcases (p.asIdeal.exists_le_maximal p.IsPrime.1) with ⟨q, ⟨h1, h2⟩⟩
      refine' le_trans ?_ (le_sSup ⟨⟨q, Ideal.IsMaximal.isPrime h1⟩, iSup_pos h1⟩)
      exact krullDim.height_mono h2
  · rw [show (⨆ (a : PrimeSpectrum R), height (PrimeSpectrum R) a) = ⨆ (a : PrimeSpectrum R)
      (_ : true), height (PrimeSpectrum R) a by simp only [iSup_pos]]
    exact iSup_le_iSup_of_subset $ fun _ _ ↦ rfl

/-
Here we aim to show that for any prime ideal `𝔭` of a commutative ring `R`, the
height of `𝔭` equals the Krull dimension of `Localization.AtPrime 𝔭.asIdeal`.
-/
section aboutHeightAndLocalization

variable {R : Type _} [CommRing R] (𝔭 : PrimeSpectrum R)

/--
The height of `𝔭` is equal to the Krull dimension of `localization.at_prime 𝔭.as_ideal`.
-/
theorem primeIdealHeight_eq_ringKrullDim_of_Localization :
    height (PrimeSpectrum R) 𝔭 = ringKrullDim (Localization.AtPrime 𝔭.asIdeal) :=
  let e := (IsLocalization.orderIsoOfPrime (𝔭.asIdeal.primeCompl)
      (Localization.AtPrime 𝔭.asIdeal))
  krullDim.eq_of_orderIso
  { toFun := fun I ↦ let J := e.symm ⟨I.1.1, I.1.2, by
        rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_not_mem]
        rintro r ⟨h1, h2⟩
        exact h1 $ I.2 h2⟩
      ⟨J.1, J.2⟩
    invFun := fun J ↦ let I := e ⟨J.1, J.2⟩
      ⟨⟨I.1, I.2.1⟩, fun r (hr : r ∈ I.1) ↦ not_not.mp $ Set.disjoint_right.mp I.2.2 hr⟩
    left_inv := fun I ↦ by simp only [Subtype.coe_eta, OrderIso.apply_symm_apply]
    right_inv := fun J ↦ by simp only [Subtype.coe_eta, OrderIso.symm_apply_apply]
    map_rel_iff' := fun {I₁ I₂} ↦ by
      convert e.symm.map_rel_iff (a := ⟨I₁.1.1, I₁.1.2, ?_⟩) (b := ⟨I₂.1.1, I₂.1.2, ?_⟩) using 1 <;>
      rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_not_mem] <;>
      rintro r ⟨h1, h2⟩
      · exact h1 $ I₁.2 h2
      · exact h1 $ I₂.2 h2 }

end aboutHeightAndLocalization

end ringKrullDim
