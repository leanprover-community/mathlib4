/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Jingting Wang, Andrew Yang, Shouxin Zhang
-/
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Order.KrullDimension
import Mathlib.Order.Atoms
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Artinian.Ring
/-!
# Krull's Height Theorem

In this file, we proved Krull's principal ideal theorem and Krull's height theorem.

## Main Results

* `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes` : In a commutative Noetherian ring `R`,
  any prime ideal that is minimal over a principal ideal has height at most 1.

* `Ideal.height_le_spanRank_toENat_of_mem_minimal_primes` : In a commutative Noetherian ring `R`,
  any prime ideal that is minimal over an ideal generated by `n` elements has height at most `n`.

* `Ideal.height_le_spanRank_toENat` : In a commutative Noetherian ring `R`, the height of a
  (finitely-generated) ideal is smaller than or equal to the minimum number of generators for
  this ideal.

* `Ideal.height_le_iff_exists_minimal_primes` : In a commutative Noetherian ring `R`, a prime ideal
  `p` has height no greater than `n` if and only if it is a minimal ideal over some ideal generated
  by no more than `n` elements.
-/

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

lemma Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing
    [IsLocalRing R] (I : Ideal R) [I.IsPrincipal]
    (hp : (IsLocalRing.maximalIdeal R) ∈ I.minimalPrimes) :
    (IsLocalRing.maximalIdeal R).height ≤ 1 := by
  rw [← ENat.coe_one, Ideal.height_le_iff]
  intro q h₁ h₂
  suffices q.primeHeight = 0 by rw [Ideal.height_eq_primeHeight, this]; exact zero_lt_one
  rw [← Ideal.height_eq_primeHeight, ← WithBot.coe_inj,
    ← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
    WithBot.coe_zero, ← ringKrullDimZero_iff_ringKrullDim_eq_zero,
    ← isArtinianRing_iff_krullDimLE_zero,
    isArtinianRing_iff_isNilpotent_maximalIdeal,
    ← Localization.AtPrime.map_eq_maximalIdeal]
  have hI : I ≠ ⊤ := (hp.1.2.trans_lt
    (lt_top_iff_ne_top.mpr (IsLocalRing.maximalIdeal.isMaximal _).ne_top)).ne
  have := Ideal.Quotient.nontrivial hI
  have := IsLocalRing.of_surjective' _ (Ideal.Quotient.mk_surjective (I := I))
  have : IsArtinianRing (R ⧸ I) := by
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal,
      Ideal.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    refine (Ideal.comap_le_comap_iff_of_surjective _ Ideal.Quotient.mk_surjective _ _).mp ?_
    rw [nilradical, Ideal.comap_radical, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective
      _ (Ideal.Quotient.mk_surjective (I := I))), Ideal.radical_eq_sInf, le_sInf_iff]
    exact fun J ⟨hJ₁, hJ₂⟩ => hp.2 ⟨hJ₂, hJ₁⟩ (IsLocalRing.le_maximalIdeal hJ₂.ne_top)
  let f := algebraMap R (Localization.AtPrime q)
  let qs : ℕ →o (Ideal (R ⧸ I))ᵒᵈ :=
    { toFun n := ((q.map f ^ n).comap f).map (Ideal.Quotient.mk I)
      monotone' i j e := Ideal.map_mono (Ideal.comap_mono (Ideal.pow_le_pow_right e)) }
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes qs
  refine ⟨n, ?_⟩
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (q.map f) _ (IsNoetherian.noetherian _)
  rotate_left
  · rw [IsLocalRing.jacobson_eq_maximalIdeal, Localization.AtPrime.map_eq_maximalIdeal]
    exact bot_ne_top
  rw [smul_eq_mul, ← pow_succ',
    ← (IsLocalization.orderEmbedding q.primeCompl (Localization.AtPrime q)).map_rel_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := I) (IsNoetherian.noetherian _) ?_ ?_
  · rw [IsLocalRing.jacobson_eq_maximalIdeal]
    exacts [hp.1.2, bot_ne_top]
  · replace hn := congr(Ideal.comap (Ideal.Quotient.mk I) $(hn _ n.le_succ))
    simp only [qs, OrderHom.coe_mk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective] at hn
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hn.le (Ideal.mem_sup_left hx))
    refine Submodule.add_mem_sup hy ?_
    obtain ⟨z, rfl⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hz
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
    refine Ideal.mul_mem_mul ?_ (Submodule.IsPrincipal.generator_mem _)
    dsimp [IsLocalization.orderEmbedding] at hx
    rwa [Ideal.mem_comap, f.map_add, f.map_mul, Ideal.add_mem_iff_right _
      (Ideal.pow_le_pow_right n.le_succ hy), mul_comm, Ideal.unit_mul_mem_iff_mem] at hx
    refine IsLocalization.map_units (M := q.primeCompl) _ ⟨_, ?_⟩
    show Submodule.IsPrincipal.generator I ∉ (↑q : Set R)
    rw [← Set.singleton_subset_iff, ← Ideal.span_le, Ideal.span_singleton_generator]
    exact fun e ↦ h₂.not_le (hp.2 ⟨h₁, e⟩ h₂.le)

/-- **Krull's Hauptidealsatz**: In a commutative Noetherian ring `R`,
  any prime ideal that is minimal over a principal ideal has height at most 1. -/
lemma Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
    (I : Ideal R) [I.IsPrincipal] (p : Ideal R) (hp : p ∈ I.minimalPrimes) : p.height ≤ 1 := by
  have := hp.1.1
  let f := algebraMap R (Localization.AtPrime p)
  have := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing
    (I.map f) ⟨⟨f (Submodule.IsPrincipal.generator I), ?_⟩⟩ ?_
  · rwa [← IsLocalization.height_comap p.primeCompl,
     Localization.AtPrime.comap_maximalIdeal] at this
  · rw [← Set.image_singleton, ← Ideal.span, ← Ideal.map_span, Ideal.span_singleton_generator I]
  · rwa [IsLocalization.minimalPrimes_map p.primeCompl (Localization.AtPrime p) I,
      Set.mem_preimage, Localization.AtPrime.comap_maximalIdeal]

/-- **Krull's height theorem** : In a commutative Noetherian ring `R`,
  any prime ideal that is minimal over an ideal generated by `n` elements has height at most `n`. -/
lemma Ideal.height_le_spanRank_toENat_of_mem_minimal_primes
    (I : Ideal R) (p : Ideal R) (hp : p ∈ I.minimalPrimes) :
    p.height ≤ I.spanRank.toENat := by
  classical
  rw [I.spanRank_toENat_eq_iInf_finset_card]
  apply le_iInf
  rintro ⟨s, hs, hs'⟩
  induction hn : hs.toFinset.card using Nat.strong_induction_on generalizing R with
  | h n H =>
    have := hp.1.1
    subst hs'
    cases n with
    | zero =>
      rw [CharP.cast_eq_zero, nonpos_iff_eq_zero, Ideal.height_eq_primeHeight p,
        Ideal.primeHeight_eq_zero_iff, minimalPrimes]
      simp_all
    | succ n =>
      rw [← @Localization.AtPrime.comap_maximalIdeal _ _ p,
        IsLocalization.height_comap p.primeCompl]
      rw [← Localization.AtPrime.comap_maximalIdeal (I := p), ← Set.mem_preimage,
        ← IsLocalization.minimalPrimes_map p.primeCompl, ← Ideal.span, Ideal.map_span] at hp
      let A' := Localization p.primeCompl
      let p' := IsLocalRing.maximalIdeal A'
      let t := algebraMap R A' '' s
      have ht : t.Finite := hs.image _
      replace hn : ht.toFinset.card ≤ n + 1 := by
        rw [show ht.toFinset = hs.toFinset.image (algebraMap R A') by ext; simp [t]]
        exact Finset.card_image_le.trans_eq hn
      change p' ∈ (Ideal.span t).minimalPrimes at hp
      show p'.height ≤ _
      clear_value t
      clear hs s
      simp_rw [Ideal.height_le_iff_covBy, ENat.coe_add, ENat.coe_one, ENat.lt_coe_add_one_iff]
      intro q hq hpq hq'
      obtain ⟨x, s, hxs, rfl, hxq⟩ : ∃ x s, x ∉ s ∧ t = insert x s ∧ x ∉ q := by
        have : ¬t ⊆ q := by
          rw [← Ideal.span_le]
          exact fun e => lt_irrefl _ ((hp.2 ⟨hq, e⟩ hpq.le).trans_lt hpq)
        obtain ⟨x, hxt, hxq⟩ := Set.not_subset.mp this
        refine ⟨x, t \ {x}, fun e => e.2 rfl, ?_, hxq⟩
        rw [Set.insert_diff_singleton, Set.insert_eq_of_mem hxt]
      have : p' ≤ (q ⊔ Ideal.span {x}).radical := by
        rw [Ideal.radical_eq_sInf, le_sInf_iff]
        rintro J ⟨hJ, hJ'⟩
        by_contra h
        refine hq' J hJ' (lt_of_le_of_ne (le_sup_left.trans hJ) ?_)
          (lt_of_le_not_le (IsLocalRing.le_maximalIdeal hJ'.ne_top) h)
        rintro rfl
        exact hxq <| hJ <| Ideal.mem_sup_right <| Submodule.mem_span_singleton_self _
      have h : ∀ z ∈ s, z ∈ (q ⊔ Ideal.span {x}).radical := by
        have := hp.1.2.trans this
        rw [Ideal.span_le, Set.insert_subset_iff] at this
        exact this.2
      replace h : ∀ z : s, ∃ (m : ℕ) (y : A') (h : y ∈ q) (a : A'), y + a * x = z ^ m := by
        rintro ⟨z, hzs⟩
        dsimp [Ideal.radical] at h
        simp only [Submodule.mem_sup, Ideal.mem_span_singleton'] at h
        obtain ⟨m, y, hyq, _, ⟨a, rfl⟩, hy⟩ := h z hzs
        exact ⟨m, y, hyq, a, hy⟩
      choose m y hyq a hy using h
      let I' := Ideal.span (Set.range y)
      let f := Ideal.Quotient.mk I'
      have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
      have hf' (z) : f (y z) = 0 := by
        rw [← RingHom.mem_ker, Ideal.mk_ker]
        exact Ideal.subset_span ⟨z, rfl⟩
      have hI'q : I' ≤ q := by
        rw [Ideal.span_le]
        rintro _ ⟨z, rfl⟩
        exact hyq _
      have hI'p' : I' ≤ p' := hI'q.trans hpq.le
      have h :=
        @Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ _
          ((Ideal.span {x}).map f) ⟨⟨algebraMap _ _ x,
            by rw [Ideal.map_span, Set.image_singleton]; rfl⟩⟩ (p'.map f) ?_
      swap
      · have : (p'.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rwa [Ideal.mk_ker])
        obtain ⟨p'', h₁, h₂⟩ := Ideal.exists_minimalPrimes_le
          (show (Ideal.span {x}).map f ≤ p'.map f by
            apply Ideal.map_mono
            rw [Ideal.span_singleton_le_iff_mem]
            exact hp.1.2 (Ideal.subset_span (Set.mem_insert x s)))
        have hxp'' : f x ∈ p'' := by
          rw [← Ideal.span_singleton_le_iff_mem, ← Set.image_singleton, ← Ideal.map_span]
          exact h₁.1.2
        convert h₁
        refine (Ideal.map_le_iff_le_comap.mpr
          (hp.2 ⟨@Ideal.IsPrime.comap _ _ _ _ _ _ f _ _ h₁.1.1, ?_⟩ ?_)).antisymm h₂
        · rw [Ideal.span_le, Set.insert_subset_iff]
          refine ⟨hxp'', ?_⟩
          intro z hz
          show f z ∈ p''
          apply h₁.1.1.mem_of_pow_mem (m ⟨z, hz⟩)
          specialize hy ⟨z, hz⟩
          rw [Subtype.coe_mk] at hy
          rw [← map_pow, ← hy, map_add, hf', zero_add, f.map_mul]
          exact Ideal.mul_mem_left _ _ hxp''
        · conv_rhs => rw [← sup_eq_left.mpr hI'p', ← @Ideal.mk_ker _ _ I', RingHom.ker_eq_comap_bot,
            ← Ideal.comap_map_of_surjective f hf p']
          exact Ideal.comap_mono h₂
      have h_lt : q.map f < p'.map f := by
        refine lt_of_le_not_le (Ideal.map_mono hpq.le) (fun e => ?_)
        have := @Ideal.comap_mono _ _ _ _ _ _ f _ _ _ e
        simp_rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot, f, Ideal.mk_ker,
          sup_eq_left.mpr hI'q, sup_eq_left.mpr (hI'q.trans hpq.le)] at this
        exact lt_irrefl _ (this.trans_lt hpq)
      have : (p'.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rwa [Ideal.mk_ker])
      have : (q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rwa [Ideal.mk_ker])
      have : (p'.map f).FiniteHeight := by
        rw [Ideal.finiteHeight_iff, ← lt_top_iff_ne_top]
        exact Or.inr (h.trans_lt (WithTop.coe_lt_top 1))
      rw [Ideal.height_eq_primeHeight] at h
      have := (Ideal.primeHeight_strict_mono h_lt).trans_le h
      rw [ENat.lt_one_iff_eq_zero, Ideal.primeHeight_eq_zero_iff, minimalPrimes,
        ← @Ideal.map_bot A' (A' ⧸ I') _ _ _ _ f, Ideal.minimalPrimes_map_of_surjective hf,
        bot_sup_eq, Ideal.mk_ker] at this
      obtain ⟨q', hq₁, hq₂⟩ := this
      obtain rfl : q = q' := by
        apply_fun Ideal.comap f at hq₂
        simp_rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
          f, Ideal.mk_ker] at hq₂
        rwa [sup_eq_left.mpr hI'q, sup_eq_left.mpr hq₁.1.2, eq_comm] at hq₂
      have hs : s.Finite := ht.subset (Set.subset_insert _ _)
      have := hs.fintype
      suffices h' : (Set.finite_range y).toFinset.card ≤ n from
        le_trans (H (Set.finite_range y).toFinset.card (by rwa [Nat.lt_add_one_iff]) _ _ hq₁
          (Set.range y) (Set.finite_range y) rfl rfl) (by norm_cast)
      trans hs.toFinset.card
      · convert Finset.card_image_le (s := Finset.univ) (f := y) <;> simp
      · refine Nat.le_of_lt_succ <| show hs.toFinset.card + 1 ≤ n + 1 from ?_
        rw [← Finset.card_insert_of_not_mem (a := x) (by simpa)]
        simpa using hn

/-- In a commutative Noetherian ring `R`, the height of a (finitely-generated) ideal is smaller
than or equal to the minimum number of generators for this ideal. -/
lemma Ideal.height_le_spanRank_toENat (I : Ideal R) (hI : I ≠ ⊤) :
    I.height ≤ I.spanRank.toENat := by
  obtain ⟨J, hJ⟩ := Ideal.nonempty_minimalPrimes hI
  refine (iInf₂_le J hJ).trans ?_
  convert (I.height_le_spanRank_toENat_of_mem_minimal_primes J hJ)
  exact Eq.symm (@height_eq_primeHeight _ _ J hJ.1.1)

lemma Ideal.height_le_spanFinrank (I : Ideal R) (hI : I ≠ ⊤) :
    I.height ≤ I.spanFinrank := by
  have : I.spanFinrank = I.spanRank.toENat := by
    rw [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr (IsNoetherian.noetherian I), map_natCast]
  exact this ▸ height_le_spanRank_toENat I hI

lemma Ideal.height_le_spanRank (I : Ideal R) (hI : I ≠ ⊤) :
    I.height ≤ I.spanRank := by
  apply le_trans (b := ((Cardinal.toENat I.spanRank) : Cardinal))
  · norm_cast
    exact I.height_le_spanRank_toENat hI
  · exact Cardinal.ofENat_toENat_le (Submodule.spanRank I)

instance Ideal.finiteHeight_of_isNoetherianRing (I : Ideal R) :
    I.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr <| Or.elim (em (I = ⊤)) Or.inl <|
  fun h ↦ Or.inr <| (lt_of_le_of_lt (I.height_le_spanFinrank h) (ENat.coe_lt_top _))

lemma exists_spanRank_eq_and_height_eq  (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ J ≤ I, J.spanRank = I.height ∧ J.height = I.height := by
  obtain ⟨J, hJ₁, hJ₂, hJ₃⟩ := exists_spanRank_le_and_le_height_of_le_height I _
    (ENat.coe_toNat_le_self I.height)
  rw [ENat.coe_toNat_eq_self.mpr (Ideal.height_ne_top hI)] at hJ₃
  refine ⟨J, hJ₁, le_antisymm ?_ (le_trans ?_ (J.height_le_spanRank ?_)),
    le_antisymm (Ideal.height_mono hJ₁) hJ₃⟩
  · convert hJ₂
    exact Cardinal.ofENat_eq_nat.mpr (ENat.coe_toNat (I.height_ne_top hI)).symm
  · exact Cardinal.ofENat_le_ofENat_of_le hJ₃
  · rintro rfl
    exact hI (top_le_iff.mp hJ₁)

/-- In a commutative Noetherian ring `R`, a prime ideal `p` has height no greater than `n` if and
only if it is a minimal ideal over some ideal generated by no more than `n` elements. -/
lemma Ideal.height_le_iff_exists_minimalPrimes  (p : Ideal R) [p.IsPrime]
    (n : ℕ∞) : p.height ≤ n ↔ ∃ I : Ideal R, p ∈ I.minimalPrimes ∧ I.spanRank ≤ n := by
  constructor
  · intro h
    obtain ⟨I, hI, e₁, e₂⟩ := exists_spanRank_eq_and_height_eq p (IsPrime.ne_top ‹_›)
    refine ⟨I, Ideal.mem_minimalPrimes_of_height_eq hI e₂.ge, e₁.symm ▸ ?_⟩
    norm_cast
  · rintro ⟨I, hp, hI⟩
    exact le_trans
      (Ideal.height_le_spanRank_toENat_of_mem_minimal_primes I p hp)
      (by simpa using (Cardinal.toENat.monotone' hI))
