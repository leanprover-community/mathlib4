/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Compactness.CompactSystem

/-!
# Analytic sets for a paving

A paving of a type `𝓧` is a set of sets `p : Set (Set 𝓧)`. A set `s` is analytic for `p` if it is
the projection on `𝓧` of a set of `𝓧 × 𝓚` (for some auxiliary space `𝓚`) that is
a countable intersection of countable unions of products `A ×ˢ K`, with `A ∈ p` and
`K` in a compact system of `𝓚`.

This is not the same notion as `MeasureTheory.AnalyticSet`, the continuous images of Polish spaces,
but it is related: in a Polish space, the analytic sets are the sets that are analytic for
the paving of closed sets (see the TODO below).

## Main definitions

* `MeasureTheory.prodSigmaDelta p q`: the countable intersections of countable unions of products
  `A ×ˢ K` with `A ∈ p` and `K ∈ q`.
* `MeasureTheory.IsPavingAnalyticFor p 𝓚 s`: `s` is analytic for the paving `p`, with auxiliary
  space `𝓚`.
* `MeasureTheory.IsPavingAnalytic p s`: `s` is analytic for the paving `p`: there exists
  an auxiliary space `𝓚` such that `s` is analytic for `p` with auxiliary space `𝓚`.
  In the definition, `𝓚` lives in `Type`, since we cannot quantify over universes.
  This is not an actual restriction: see `IsPavingAnalyticFor.isPavingAnalytic`.

## Main statements

* `MeasureTheory.IsPavingAnalyticFor.isPavingAnalyticFor_nat_nat`: the auxiliary space in the
  definition of analytic sets can always be taken to be `ℕ → ℕ`.
* `IsPavingAnalyticFor.isPavingAnalytic`: a set that is analytic for a paving `p` and an auxiliary
  space `𝓚` (in any universe) is analytic for `p`.
* `MeasureTheory.IsPavingAnalytic.fst`: the projection of a set that is analytic for a product
  paving `p × q`, with `q` a compact system, is analytic for `p`.

## Implementation notes

Some references require the compact system `q` to contain `∅` and the auxiliary space `𝓚` to be
nonempty. This gives the same notion: `insert ∅ q` is a compact system if `q` is one, and a set
that is analytic with an empty auxiliary space is empty, hence analytic with any auxiliary space.

We use `IsCompactSystem`, which corresponds to the semi-compact pavings of Dellacherie and Meyer,
rather than compact pavings (the same notion with arbitrary intersections instead of countable
ones): this is sufficient for our applications and easier to work with.

## TODO

Relate `IsPavingAnalytic` to `MeasureTheory.AnalyticSet`: in a Polish space, the analytic sets are
the sets that are analytic for the paving of closed sets.
A future PR will add the following:
```
theorem analyticSet_iff_isPavingAnalytic_isClosed [PolishSpace X] {s : Set X} :
    AnalyticSet s ↔ IsPavingAnalytic {t | IsClosed t} s
```

## References

* [S. He, J. Wang and J. Yan, *Semimartingale theory and stochastic calculus*][hewangyan1992]
-/

@[expose] public section

namespace MeasureTheory

variable {𝓧 𝓨 𝓚 𝓚' ι : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)} {s t : Set 𝓧}

/-- The paving of countable intersections of countable unions of products `A ×ˢ K` with `A ∈ p`
and `K ∈ q`. See `mem_prodSigmaDelta_iff`.

The name `prodSigmaDelta` comes from the usual notations with subscripts `δ` and `σ` for the class
of sets that are countable intersections of countable unions. -/
def prodSigmaDelta (p : Set (Set 𝓧)) (q : Set (Set 𝓚)) : Set (Set (𝓧 × 𝓚)) :=
  countableInfClosure (countableSupClosure (Set.image2 (· ×ˢ ·) p q))

lemma mem_countableSupClosure_image2_prod_iff {s : Set (𝓧 × 𝓚)} :
    s ∈ countableSupClosure (Set.image2 (· ×ˢ ·) p q) ↔
      ∃ A : ℕ → Set 𝓧, (∀ n, A n ∈ p) ∧ ∃ K : ℕ → Set 𝓚, (∀ n, K n ∈ q) ∧
        ⋃ n, A n ×ˢ K n = s := by
  simp only [mem_countableSupClosure_iff_iSup, Set.mem_image2, Set.iSup_eq_iUnion]
  refine ⟨fun ⟨B, hB, hs⟩ ↦ ?_, fun ⟨A, hA, K, hK, hs⟩ ↦
    ⟨fun n ↦ A n ×ˢ K n, fun n ↦ ⟨A n, hA n, K n, hK n, rfl⟩, hs⟩⟩
  choose A hA K hK hB_eq using hB
  exact ⟨A, hA, K, hK, by simp_rw [hB_eq]; exact hs⟩

lemma mem_prodSigmaDelta_iff {s : Set (𝓧 × 𝓚)} :
    s ∈ prodSigmaDelta p q ↔
      ∃ A : ℕ → ℕ → Set 𝓧, (∀ n m, A n m ∈ p) ∧ ∃ K : ℕ → ℕ → Set 𝓚, (∀ n m, K n m ∈ q) ∧
        ⋂ n, ⋃ m, A n m ×ˢ K n m = s := by
  simp only [prodSigmaDelta, mem_countableInfClosure_iff_iInf,
    mem_countableSupClosure_image2_prod_iff, Set.iInf_eq_iInter]
  refine ⟨fun ⟨B, hB, hs⟩ ↦ ?_, fun ⟨A, hA, K, hK, hs⟩ ↦
    ⟨fun n ↦ ⋃ m, A n m ×ˢ K n m, fun n ↦ ⟨A n, hA n, K n, hK n, rfl⟩, hs⟩⟩
  choose A hA K hK hB_eq using hB
  exact ⟨A, hA, K, hK, by simp_rw [hB_eq]; exact hs⟩

lemma prod_mem_prodSigmaDelta {s : Set 𝓧} {t : Set 𝓚} (hs : s ∈ p) (ht : t ∈ q) :
    s ×ˢ t ∈ prodSigmaDelta p q :=
  subset_countableInfClosure (subset_countableSupClosure (Set.mem_image2_of_mem hs ht))

@[gcongr]
lemma prodSigmaDelta_mono {p' : Set (Set 𝓧)} {q' : Set (Set 𝓚)} (hp : p ⊆ p') (hq : q ⊆ q') :
    prodSigmaDelta p q ⊆ prodSigmaDelta p' q' :=
  countableInfClosure_mono (countableSupClosure_mono (Set.image2_subset hp hq))

lemma countableInfClosed_prodSigmaDelta : CountableInfClosed (prodSigmaDelta p q) :=
  countableInfClosed_countableInfClosure

/-- The preimage of a set of `prodSigmaDelta p q` by `Prod.map g f` belongs to the
`prodSigmaDelta` of the preimage pavings. -/
lemma preimage_prodMap_mem_prodSigmaDelta {g : 𝓨 → 𝓧} {f : 𝓚' → 𝓚} {t : Set (𝓧 × 𝓚)}
    (ht : t ∈ prodSigmaDelta p q) :
    Prod.map g f ⁻¹' t ∈ prodSigmaDelta ((g ⁻¹' ·) '' p) ((f ⁻¹' ·) '' q) := by
  obtain ⟨A, hA, K, hK, rfl⟩ := mem_prodSigmaDelta_iff.mp ht
  refine mem_prodSigmaDelta_iff.mpr ⟨fun n m ↦ g ⁻¹' A n m, fun n m ↦ ⟨A n m, hA n m, rfl⟩,
    fun n m ↦ f ⁻¹' K n m, fun n m ↦ ⟨K n m, hK n m, rfl⟩, ?_⟩
  simp [Set.preimage_iInter, Set.preimage_iUnion, Set.preimage_prod_map_prod]

/-- A set `s` is analytic for a paving `p` and a type `𝓚` if there exists a compact system `q` of
`𝓚` such that `s` is the projection of a set `t ∈ prodSigmaDelta p q`. -/
def IsPavingAnalyticFor (p : Set (Set 𝓧)) (𝓚 : Type*) (s : Set 𝓧) : Prop :=
  ∃ q : Set (Set 𝓚), IsCompactSystem q ∧
    ∃ t : Set (𝓧 × 𝓚), t ∈ prodSigmaDelta p q ∧ s = Prod.fst '' t

/-- A set `s` is analytic for a paving `p` if there exists a type `𝓚` and a compact system `q` of
`𝓚` such that `s` is the projection of a set `t ∈ prodSigmaDelta p q`. -/
def IsPavingAnalytic (p : Set (Set 𝓧)) (s : Set 𝓧) : Prop :=
  ∃ 𝓚 : Type, IsPavingAnalyticFor p 𝓚 s

/-- The auxiliary space in the definition of analytic sets can always be taken to be `ℕ → ℕ`. -/
lemma IsPavingAnalyticFor.isPavingAnalyticFor_nat_nat (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor p (ℕ → ℕ) s := by
  classical
  obtain ⟨q, hq, t, ht, rfl⟩ := hs
  obtain ⟨A, hA, K, hK, rfl⟩ := mem_prodSigmaDelta_iff.mp ht
  -- encode a point `k` by the set of indices `(n, m)` such that `k ∈ K n m`
  let φ : 𝓚 → ℕ → ℕ := fun k j ↦ if k ∈ K j.unpair.1 j.unpair.2 then 1 else 0
  have hφ n m : φ ⁻¹' (φ '' K n m) = K n m := by
    refine subset_antisymm ?_ (Set.subset_preimage_image _ _)
    rintro k' ⟨k, hk, h⟩
    have h_nm := congrFun h (Nat.pair n m)
    simp only [φ, Nat.unpair_pair, hk, ↓reduceIte] at h_nm
    by_contra hk'
    simp [hk'] at h_nm
  refine ⟨(φ '' ·) '' {t | ∃ n m, K n m = t}, ?_, ⋂ n, ⋃ m, A n m ×ˢ (φ '' K n m),
    mem_prodSigmaDelta_iff.mpr ⟨A, hA, _, fun n m ↦ ⟨K n m, ⟨n, m, rfl⟩, rfl⟩, rfl⟩, ?_⟩
  · refine (hq.mono ?_).image ?_
    · rintro _ ⟨n, m, rfl⟩
      exact hK n m
    · rintro _ ⟨n, m, rfl⟩
      exact hφ n m
  -- the points of `𝓚` with the same image by `φ` belong to the same sets `K n m`
  ext x
  simp only [Set.mem_image, Set.mem_iInter, Set.mem_iUnion, Set.mem_prod, Prod.exists,
    exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨φ k, fun n ↦ (hk n).imp fun m h ↦ ⟨h.1, k, h.2, rfl⟩⟩
  · rintro ⟨τ, hτ⟩
    obtain ⟨-, -, k, -, rfl⟩ := hτ 0
    refine ⟨k, fun n ↦ (hτ n).imp fun m ⟨hxA, hk⟩ ↦ ⟨hxA, ?_⟩⟩
    rwa [← hφ n m]

lemma IsPavingAnalyticFor.isPavingAnalytic (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalytic p s :=
  ⟨ℕ → ℕ, hs.isPavingAnalyticFor_nat_nat⟩

lemma isPavingAnalyticFor_of_mem (𝓚 : Type*) [Nonempty 𝓚] (hs : s ∈ p) :
    IsPavingAnalyticFor p 𝓚 s :=
  ⟨{Set.univ, ∅}, isCompactSystem_singleton_empty.insert_univ, s ×ˢ .univ,
    prod_mem_prodSigmaDelta hs (by simp), (Set.fst_image_prod s Set.univ_nonempty).symm⟩

lemma isPavingAnalytic_of_mem (hs : s ∈ p) : IsPavingAnalytic p s :=
  (isPavingAnalyticFor_of_mem Unit hs).isPavingAnalytic

lemma IsPavingAnalyticFor.mono {p' : Set (Set 𝓧)} (hp : p ⊆ p') (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor p' 𝓚 s :=
  let ⟨q, hq, t, ht, hs⟩ := hs
  ⟨q, hq, t, prodSigmaDelta_mono hp subset_rfl ht, hs⟩

lemma IsPavingAnalytic.mono {p' : Set (Set 𝓧)} (hp : p ⊆ p') (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic p' s :=
  let ⟨_, hs⟩ := hs
  (hs.mono hp).isPavingAnalytic

/-- An analytic set for `p` is contained in a countable union of sets of `p`.
See the paragraph after Definition 1.25 of [hewangyan1992]. -/
lemma IsPavingAnalyticFor.exists_mem_countableSupClosure_superset (hs : IsPavingAnalyticFor p 𝓚 s) :
    ∃ t ∈ countableSupClosure p, s ⊆ t := by
  obtain ⟨q, -, B, hB, rfl⟩ := hs
  obtain ⟨A, hA, K, -, rfl⟩ := mem_prodSigmaDelta_iff.mp hB
  refine ⟨⋃ m, A 0 m, iSup_mem_countableSupClosure (hA 0), ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨m, hm, -⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hy 0)
  exact Set.mem_iUnion.mpr ⟨m, hm⟩

lemma isPavingAnalyticFor_empty (𝓚 : Type*) (hp : p.Nonempty) : IsPavingAnalyticFor p 𝓚 ∅ :=
  let ⟨A, hA⟩ := hp
  ⟨{Set.univ, ∅}, isCompactSystem_singleton_empty.insert_univ, A ×ˢ ∅,
    prod_mem_prodSigmaDelta hA (by simp), by simp⟩

@[simp]
lemma isPavingAnalytic_empty (hp : p.Nonempty) : IsPavingAnalytic p ∅ :=
  (isPavingAnalyticFor_empty Unit hp).isPavingAnalytic

@[simp]
lemma isPavingAnalyticFor_iff_eq_empty [IsEmpty 𝓚] (hp : p.Nonempty) :
    IsPavingAnalyticFor p 𝓚 s ↔ s = ∅ :=
  ⟨fun ⟨_, _, t, _, hs⟩ ↦ by simp [hs, Set.eq_empty_of_isEmpty t],
    fun hs ↦ hs ▸ isPavingAnalyticFor_empty 𝓚 hp⟩

/-- A countable intersection of analytic sets is analytic.
Theorem 1.26 of [hewangyan1992]. -/
lemma IsPavingAnalyticFor.iInter [Countable ι] [Nonempty ι] {𝓚 : ι → Type*} {s : ι → Set 𝓧}
    (hs : ∀ i, IsPavingAnalyticFor p (𝓚 i) (s i)) :
    IsPavingAnalyticFor p (Π i, 𝓚 i) (⋂ i, s i) := by
  classical
  choose q hq B hB hs_eq using hs
  -- the set `⋂ i, s i` is the projection of the set of `(x, y)` with `(x, y i) ∈ B i` for all `i`
  refine ⟨Set.univ.pi '' Set.univ.pi (fun i ↦ insert Set.univ (q i)),
    IsCompactSystem.pi fun i ↦ (hq i).insert_univ, ⋂ i, Prod.map id (Function.eval i) ⁻¹' B i,
    countableInfClosed_prodSigmaDelta.iInf_mem fun i ↦
      prodSigmaDelta_mono ?_ ?_ (preimage_prodMap_mem_prodSigmaDelta (hB i)), ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact hA
  · rintro _ ⟨K, hK, rfl⟩
    refine ⟨Function.update (fun _ ↦ Set.univ) i K, fun j _ ↦ ?_, Set.eval_preimage.symm⟩
    rcases eq_or_ne j i with rfl | hj
    · simpa using .inr hK
    · simp [hj]
  · ext x
    simp only [hs_eq, Set.mem_iInter, Set.mem_image, Set.mem_preimage, Prod.map_apply, id_eq,
      Function.eval, Prod.exists, exists_and_right, exists_eq_right]
    refine ⟨fun h ↦ ?_, fun ⟨y, hy⟩ i ↦ ⟨y i, hy i⟩⟩
    choose y hy using h
    exact ⟨y, hy⟩

/-- A countable intersection of analytic sets is analytic.
Theorem 1.26 of [hewangyan1992]. -/
lemma IsPavingAnalytic.iInter [Countable ι] [Nonempty ι] {s : ι → Set 𝓧}
    (hs : ∀ i, IsPavingAnalytic p (s i)) :
    IsPavingAnalytic p (⋂ i, s i) := by
  obtain ⟨f, hf⟩ := exists_surjective_nat ι
  rw [← hf.iInter_comp]
  choose 𝓚 hs𝓚 using hs
  exact (IsPavingAnalyticFor.iInter fun n ↦ hs𝓚 (f n)).isPavingAnalytic

/-- The intersection of two analytic sets is analytic.
Theorem 1.26 of [hewangyan1992]. -/
lemma IsPavingAnalyticFor.inter (hs : IsPavingAnalyticFor p 𝓚 s) (ht : IsPavingAnalyticFor p 𝓚' t) :
    IsPavingAnalyticFor p (𝓚 × 𝓚') (s ∩ t) := by
  obtain ⟨q, hq, B, hB, rfl⟩ := hs
  obtain ⟨q', hq', B', hB', rfl⟩ := ht
  -- the set `s ∩ t` is the projection of the set of `(x, y, y')` with `(x, y) ∈ B` and
  -- `(x, y') ∈ B'`
  refine ⟨Set.image2 (· ×ˢ ·) (insert Set.univ q) (insert Set.univ q'),
    hq.insert_univ.prod hq'.insert_univ,
    Prod.map id Prod.fst ⁻¹' B ∩ Prod.map id Prod.snd ⁻¹' B',
    countableInfClosed_prodSigmaDelta.infClosed
      (prodSigmaDelta_mono ?_ ?_ (preimage_prodMap_mem_prodSigmaDelta hB))
      (prodSigmaDelta_mono ?_ ?_ (preimage_prodMap_mem_prodSigmaDelta hB')), ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact hA
  · rintro _ ⟨K, hK, rfl⟩
    exact ⟨K, .inr hK, Set.univ, .inl rfl, Set.prod_univ⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact hA
  · rintro _ ⟨K, hK, rfl⟩
    exact ⟨Set.univ, .inl rfl, K, .inr hK, Set.univ_prod⟩
  · ext
    simp

/-- The intersection of two analytic sets is analytic.
Theorem 1.26 of [hewangyan1992]. -/
lemma IsPavingAnalytic.inter (hs : IsPavingAnalytic p s) (ht : IsPavingAnalytic p t) :
    IsPavingAnalytic p (s ∩ t) :=
  let ⟨_, hs⟩ := hs
  let ⟨_, ht⟩ := ht
  (hs.inter ht).isPavingAnalytic

/-- The projection of an analytic set for the paving `p × q`, with `q` a compact system, is
analytic for `p`.
This is Theorem 1.28 of [hewangyan1992]. -/
lemma IsPavingAnalyticFor.fst (hq : IsCompactSystem q) {s : Set (𝓧 × 𝓚)}
    (hs : IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p q) 𝓚' s) :
    IsPavingAnalyticFor p (𝓚 × 𝓚') (Prod.fst '' s) := by
  obtain ⟨q', hq', B, hB, rfl⟩ := hs
  obtain ⟨C, hC, K', hK', rfl⟩ := mem_prodSigmaDelta_iff.mp hB
  choose A hA K hK hC_eq using hC
  refine ⟨Set.image2 (· ×ˢ ·) q q', hq.prod hq', ⋂ n, ⋃ m, A n m ×ˢ (K n m ×ˢ K' n m),
    mem_prodSigmaDelta_iff.mpr ⟨A, hA, _, fun n m ↦ Set.mem_image2_of_mem (hK n m) (hK' n m), rfl⟩,
    ?_⟩
  ext
  simp [← hC_eq, and_assoc]

/-- The projection of an analytic set for the paving `p × q`, with `q` a compact system, is
analytic for `p`.
This is Theorem 1.28 of [hewangyan1992]. -/
lemma IsPavingAnalytic.fst (hq : IsCompactSystem q)
    {s : Set (𝓧 × 𝓚)} (hs : IsPavingAnalytic (Set.image2 (· ×ˢ ·) p q) s) :
    IsPavingAnalytic p (Prod.fst '' s) := by
  obtain ⟨𝓚', hs𝓚'⟩ := hs
  exact (hs𝓚'.fst hq).isPavingAnalytic

/-- The product of an analytic set for `p` with a set of `r` is analytic for the product paving
`r × p`. -/
lemma IsPavingAnalyticFor.prod_left {r : Set (Set 𝓨)} {t : Set 𝓨} (ht : t ∈ r)
    (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) 𝓚 (t ×ˢ s) := by
  obtain ⟨q, hq, B, hB, rfl⟩ := hs
  obtain ⟨A, hA, K, hK, rfl⟩ := mem_prodSigmaDelta_iff.mp hB
  refine ⟨q, hq, ⋂ n, ⋃ m, (t ×ˢ A n m) ×ˢ K n m,
    mem_prodSigmaDelta_iff.mpr ⟨_, fun n m ↦ Set.mem_image2_of_mem ht (hA n m), K, hK, rfl⟩, ?_⟩
  ext ⟨y, x⟩
  simp only [Set.mem_prod, Set.mem_image, Set.mem_iInter, Set.mem_iUnion, Prod.exists,
    exists_and_right, exists_eq_right]
  exact ⟨fun ⟨hy, k, hk⟩ ↦ ⟨k, fun n ↦ (hk n).imp fun _ h ↦ ⟨⟨hy, h.1⟩, h.2⟩⟩,
    fun ⟨k, hk⟩ ↦ ⟨(hk 0).choose_spec.1.1, k, fun n ↦ (hk n).imp fun _ h ↦ ⟨h.1.2, h.2⟩⟩⟩

/-- The product of an analytic set for `p` with a set of `r` is analytic for the product paving
`r × p`. -/
lemma IsPavingAnalytic.prod_left {r : Set (Set 𝓨)} {t : Set 𝓨} (ht : t ∈ r)
    (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) r p) (t ×ˢ s) :=
  let ⟨_, hs⟩ := hs
  (hs.prod_left ht).isPavingAnalytic

/-- The product of an analytic set for `p` with a set of `r` is analytic for the product paving
`p × r`. -/
lemma IsPavingAnalyticFor.prod_right {r : Set (Set 𝓨)} {t : Set 𝓨}
    (hs : IsPavingAnalyticFor p 𝓚 s) (ht : t ∈ r) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) 𝓚 (s ×ˢ t) := by
  obtain ⟨q, hq, B, hB, rfl⟩ := hs
  obtain ⟨A, hA, K, hK, rfl⟩ := mem_prodSigmaDelta_iff.mp hB
  refine ⟨q, hq, ⋂ n, ⋃ m, (A n m ×ˢ t) ×ˢ K n m,
    mem_prodSigmaDelta_iff.mpr ⟨_, fun n m ↦ Set.mem_image2_of_mem (hA n m) ht, K, hK, rfl⟩, ?_⟩
  ext ⟨x, y⟩
  simp only [Set.mem_prod, Set.mem_image, Set.mem_iInter, Set.mem_iUnion, Prod.exists,
    exists_and_right, exists_eq_right]
  exact ⟨fun ⟨⟨k, hk⟩, hy⟩ ↦ ⟨k, fun n ↦ (hk n).imp fun _ h ↦ ⟨⟨h.1, hy⟩, h.2⟩⟩,
    fun ⟨k, hk⟩ ↦ ⟨⟨k, fun n ↦ (hk n).imp fun _ h ↦ ⟨h.1.1, h.2⟩⟩, (hk 0).choose_spec.1.2⟩⟩

/-- The product of an analytic set for `p` with a set of `r` is analytic for the product paving
`p × r`. -/
lemma IsPavingAnalytic.prod_right {r : Set (Set 𝓨)} {t : Set 𝓨}
    (hs : IsPavingAnalytic p s) (ht : t ∈ r) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) p r) (s ×ˢ t) :=
  let ⟨_, hs⟩ := hs
  (hs.prod_right ht).isPavingAnalytic

end MeasureTheory
