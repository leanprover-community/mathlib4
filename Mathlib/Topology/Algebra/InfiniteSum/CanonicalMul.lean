import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Separation.Regular
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Algebra.Order.Quantale
import Mathlib.Topology.Algebra.Order.LiminfLimsup

variable {M R ι κ : Type*} {i j : ι} {f g : ι → M} {s t : Set ι}

variable [CommMonoid M] [CompleteLattice M] [IsOrderedMonoid M]
    [TopologicalSpace M] [SupConvergenceClass M] [CanonicallyOrderedMul M]

-- Underscores are to prevent conflicts with currently deprecated declarations

set_option linter.style.longLine false

@[to_additive]
lemma bot_eq_one''' {α : Type*} [CommMonoid α] [CompleteLattice α] [CanonicallyOrderedMul α] :
  (⊥ : α) = 1 :=
  bot_le.antisymm <| one_le _

open Set Topology Function Filter

/-- If a topological monoid is a canonically ordered complete lattice with well-behaved
suprema, then every function is multipliable. -/
@[to_additive]
theorem hasProd : HasProd f (⨆ s : Finset ι, ∏ i ∈ s, f i) :=
  tendsto_atTop_iSup <| fun _ _ ↦ Finset.prod_le_prod_of_subset'

@[to_additive (attr := simp)]
theorem multipliable : Multipliable f :=
  hasProd.multipliable

omit [IsOrderedMonoid M] [SupConvergenceClass M] in
@[to_additive (attr := simp)]
theorem tprod_iSup_eq (i : ι) : (∏' b : ι, ⨆ _ : i = b, f b) = f i :=
  (tprod_eq_mulSingle i fun _ h => by simp [h.symm, bot_eq_one''']).trans <| by simp

section T2Space

variable [T2Space M]

@[to_additive]
theorem tprod_eq_iSup_prod : ∏' i, f i = ⨆ s : Finset ι, ∏ i ∈ s, f i :=
  hasProd.tprod_eq

@[to_additive]
theorem tprod_eq_iSup_prod' (s : κ → Finset ι) (hs : ∀ t, ∃ k, t ⊆ s k) :
    ∏' i, f i = ⨆ k, ∏ i ∈ s k, f i := by
  rw [tprod_eq_iSup_prod, eq_comm]
  exact (Finset.prod_mono_set' f).iSup_comp_eq hs

@[to_additive]
theorem tprod_eq_iSup_nat' {f : ℕ → M} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    ∏' i : ℕ, f i = ⨆ i : ℕ, ∏ a ∈ Finset.range (N i), f a :=
  tprod_eq_iSup_prod' _ fun t =>
    let ⟨n, hn⟩ := t.exists_nat_subset_range
    let ⟨k, _, hk⟩ := exists_le_of_tendsto_atTop hN 0 n
    ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩

@[to_additive]
theorem tprod_eq_iSup_nat {f : ℕ → M} :
    ∏' i : ℕ, f i = ⨆ i : ℕ, ∏ a ∈ Finset.range i, f a :=
  tprod_eq_iSup_prod' _ Finset.exists_nat_subset_range

@[to_additive (attr := gcongr)]
theorem _tprod_le_tprod (h : ∀ i, f i ≤ g i) : ∏' i, f i ≤ ∏' i, g i := by
  rw [tprod_eq_iSup_prod, tprod_eq_iSup_prod]
  exact iSup_mono fun s ↦ Finset.prod_le_prod' fun i _ ↦ h i

@[to_additive]
theorem _tprod_mono : Monotone (tprod : (ι → M) → M) :=
  fun _ _ ↦ _tprod_le_tprod

@[to_additive]
theorem _prod_le_tprod (s : Finset ι) : ∏ x ∈ s, f x ≤ ∏' x, f x := by
  rw [tprod_eq_iSup_prod]
  apply le_iSup (f := fun s ↦ ∏ x ∈ s, f x)

@[to_additive]
theorem _le_tprod (i : ι) : f i ≤ ∏' i, f i := by
  simpa using _prod_le_tprod {i}

@[to_additive]
theorem _le_tprod_of_mem (hi : i ∈ s) : f i ≤ ∏' x : s, f x :=
  _le_tprod (⟨i,hi⟩ : s) (f := fun x ↦ f x.1)

@[to_additive (attr := simp)]
theorem _tprod_eq_one_iff : ∏' i, f i = 1 ↔ ∀ i, f i = 1 := by
  rw [tprod_eq_iSup_prod, ← le_one_iff_eq_one, iSup_le_iff]
  simp only [le_one_iff_eq_one, Finset.prod_eq_one_iff]
  exact ⟨fun h i ↦ by simpa using h {i}, fun h _ i _ ↦ h _⟩

@[to_additive]
theorem _tprod_ne_one_iff : ∏' i, f i ≠ 1 ↔ ∃ i, f i ≠ 1 := by
  simp

@[to_additive]
theorem tprod_eq_top_of_eq_top (hi : f i = ⊤) : ∏' i, f i = ⊤ :=
  (hi.symm.trans_le (_le_tprod _)).antisymm' le_top

@[to_additive]
theorem tprod_subtype_eq_top_of_eq_top (his : i ∈ s) (h : f i = ⊤) : ∏' i : s, f i = ⊤ :=
  tprod_eq_top_of_eq_top <| show f (⟨i, his⟩ : s) = ⊤ from h

@[to_additive _tsum_pos]
theorem _one_lt_tprod (hi : 1 < f i) : 1 < ∏' (i : ι), f i :=
  hi.trans_le <| _le_tprod _

@[to_additive (attr := simp)]
theorem tprod_top [Nonempty M] : ∏' _ : M, ⊤ = (⊤ : M) :=
  tprod_eq_top_of_eq_top (i := Classical.arbitrary M) rfl

section ContinuousMul

variable [ContinuousMul M]

@[to_additive]
theorem _tprod_sum {f : ι ⊕ κ → M} : ∏' (i : ι ⊕ κ), f i = (∏' i, f (.inl i)) * ∏' j, f (.inr j) :=
  multipliable.tprod_sum multipliable

@[to_additive]
theorem tprod_subtype_union_disjoint (hd : Disjoint s t) :
    ∏' (i : ↑(s ∪ t)), f i = (∏' i : s, f i) * ∏' i : t, f i :=
  multipliable.tprod_union_disjoint hd multipliable

@[to_additive]
theorem _tprod_finset_bUnion_disjoint {s : Finset ι} {t : ι → Set κ} {f : κ → M}
    (hd : (s : Set ι).Pairwise (Disjoint on t)) :
    ∏' (x : ↑(⋃ i ∈ s, t i)), f ↑x = ∏ i ∈ s, ∏' (x : ↑(t i)), f x :=
  Multipliable.tprod_finset_bUnion_disjoint hd <| by simp

@[to_additive]
theorem tprod_subtype_le_of_subset (h : s ⊆ t) : ∏' i : s, f i ≤ ∏' i : t, f i := by
  rw [← diff_union_of_subset h, tprod_subtype_union_disjoint disjoint_sdiff_left]
  exact le_mul_self

@[to_additive]
theorem tprod_subtype_le_tprod (s : Set ι) : ∏' i : s, f i ≤ ∏' i, f i := by
  simpa using tprod_subtype_le_of_subset (subset_univ s) (f := f)

@[to_additive]
theorem tprod_subtype_union_le (s t : Set ι) :
    ∏' (i : ↑(s ∪ t)), f (i : ι) ≤ (∏' i : s, f i) * ∏' (x : t), f x := by
  rw [← diff_union_self, tprod_subtype_union_disjoint disjoint_sdiff_left]
  exact mul_le_mul_right' (tprod_subtype_le_of_subset diff_subset) _

@[to_additive]
theorem tprod_subtype_insert (h : i ∉ s) : ∏' (x : ↑(insert i s)), f x = f i * ∏' i : s, f i := by
  rw [← singleton_union, tprod_subtype_union_disjoint, tprod_singleton]
  rwa [disjoint_singleton_left]

/-- the corresponding `Mulitipliable` lemma here is primed -/
@[to_additive]
theorem _tprod_eq_mul_tprod_ite [DecidableEq ι] (i : ι) :
    ∏' i, f i = f i * ∏' x, if x = i then 1 else f x := by
  apply multipliable.tprod_eq_mul_tprod_ite'

/-- TODO : The corresponding `Multipliable` lemma is primed, but also misnamed
  `prod_mul_tprod_nat_mul'` (should be `prod_mul_tprod_nat_add'`) -/
@[to_additive]
theorem _prod_mul_tprod_nat_add {f : ℕ → M} {k : ℕ} :
    (∏ i ∈ Finset.range k, f i) * ∏' (i : ℕ), f (i + k) = ∏' (i : ℕ), f i :=
  multipliable.prod_mul_tprod_nat_mul'

/-- TODO : The lemma `tprod_eq_zero_mul'` should have been deprecated but wasn't. -/
@[to_additive]
theorem _tprod_eq_zero_mul {f : ℕ → M} : ∏' (b : ℕ), f b = f 0 * ∏' (b : ℕ), f (b + 1) :=
  tprod_eq_zero_mul' multipliable

/-- TODO : The lemma `tprod_even_mul_odd` should have been deprecated but wasn't. -/
@[to_additive]
theorem _tprod_even_mul_odd {f : ℕ → M} : (∏' k, f (2 * k)) * ∏' k, f (2 * k + 1) = ∏' k, f k :=
  tprod_even_mul_odd multipliable multipliable

/-- TODO : The lemma `tprod_of_nat_of_neg_add_one` should have been deprecated but wasn't. -/
@[to_additive]
theorem _tprod_of_nat_of_neg_add_one {f : ℤ → M} :
    ∏' (n : ℤ), f n = (∏' (n : ℕ), f ↑n) * ∏' (n : ℕ), f (-(↑n + 1)) :=
  tprod_of_nat_of_neg_add_one multipliable multipliable

end ContinuousMul

end T2Space

@[to_additive]
theorem _tprod_le_of_prod_range_le [ClosedIicTopology M] {c : M} {f : ℕ → M}
    (h : ∀ (n : ℕ), ∏ i ∈ Finset.range n, f i ≤ c) : ∏' n, f n ≤ c :=
  multipliable.tprod_le_of_prod_range_le h

@[to_additive]
theorem _tprod_le_tprod_of_inj [OrderClosedTopology M] {g : κ → M} (e : ι → κ)
    (he : Injective e) (hs : ∀ c ∉ range e, 1 ≤ g c) (h : ∀ (i : ι), f i ≤ g (e i)) :
    tprod f ≤ tprod g :=
  multipliable.tprod_le_tprod_of_inj e he hs h multipliable

@[to_additive]
theorem _tprod_le_of_prod_le [OrderClosedTopology M] {c : M}
    (h : ∀ (s : Finset ι), ∏ i ∈ s, f i ≤ c) : ∏' (i : ι), f i ≤ c :=
  multipliable.tprod_le_of_prod_le h

section LinearOrder

variable {M : Type*} [CommMonoid M] [CompleteLinearOrder M] [IsOrderedMonoid M] [TopologicalSpace M]
  [OrderTopology M] [CanonicallyOrderedMul M]

@[to_additive]
theorem tprod_eq_liminf_prod_nat {f : ℕ → M} :
    ∏' i, f i = liminf (fun n ↦ ∏ i ∈ Finset.range n, f i) atTop :=
  multipliable.hasProd.tendsto_prod_nat.liminf_eq.symm

@[to_additive]
theorem tprod_eq_limsup_prod_nat {f : ℕ → M} :
    ∏' i, f i = limsup (fun n ↦ ∏ i ∈ Finset.range n, f i) atTop :=
  multipliable.hasProd.tendsto_prod_nat.limsup_eq.symm

@[to_additive]
theorem hasProd_iff_tendsto_nat {f : ℕ → M} (r : M) :
    HasProd f r ↔ Tendsto (fun n : ℕ ↦ ∏ i ∈ Finset.range n, f i) atTop (𝓝 r) := by
  refine ⟨HasProd.tendsto_prod_nat, fun h => ?_⟩
  rw [← iSup_eq_of_tendsto _ h, ← tprod_eq_iSup_nat]
  · exact multipliable.hasProd
  exact fun s t hst => Finset.prod_le_prod_of_subset' (Finset.range_subset.2 hst)


end LinearOrder

section T3Space

variable [T3Space M] [ContinuousMul M] {κ : Type*}

@[to_additive]
theorem _tprod_sigma' {β : ι → Type*} (f : (Σ i, β i) → M) :
    ∏' p : Σ i, β i, f p = ∏' (i) (j), f ⟨i, j⟩ :=
  multipliable.tprod_sigma' (fun _ => multipliable)

@[to_additive _tsum_prod]
theorem _tprod_prod {f : ι → κ → M} : ∏' p : ι × κ, f p.1 p.2 = ∏' (i) (j), f i j :=
  multipliable.tprod_prod' fun _ => multipliable

@[to_additive]
theorem _tprod_prod' {f : ι × κ → M} : ∏' p : ι × κ, f p = ∏' (i) (j), f (i, j) :=
  multipliable.tprod_prod' fun _ => multipliable

@[to_additive]
theorem _tprod_comm {f : ι → κ → M} : ∏' i, ∏' j, f i j = ∏' j, ∏' i, f i j :=
   multipliable.tprod_comm' (fun _ => multipliable) fun _ => multipliable

@[to_additive]
theorem _tprod_mul : ∏' i, (f i * g i) = (∏' i, f i) * ∏' i, g i :=
   multipliable.tprod_mul multipliable

@[to_additive]
theorem _tprod_mul_tprod_compl : (∏' (i : ↑s), f i) * ∏' (i : ↑sᶜ), f i = ∏' (i : ι), f i :=
  multipliable.tprod_mul_tprod_compl multipliable

@[to_additive]
theorem _tprod_sigma {β : ι → Type*} (f : ∀ i, β i → M) :
    ∏' p : Σ i, β i, f p.1 p.2 = ∏' (i) (j), f i j :=
  multipliable.tprod_sigma' (fun _ => multipliable)

@[to_additive]
theorem tprod_comp_le_tprod_of_injective {f : ι → κ} (hf : Injective f) (g : κ → M) :
    ∏' i, g (f i) ≤ ∏' j, g j := by
  rw [← tprod_range _ hf]
  exact tprod_subtype_le_tprod (range f)

@[to_additive]
theorem tprod_le_tprod_comp_of_surjective {f : ι → κ}
    (hf : Surjective f) (g : κ → M) : ∏' y, g y ≤ ∏' x, g (f x) := by
  calc ∏' y, g y = ∏' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
    _ ≤ ∏' x, g (f x) := tprod_comp_le_tprod_of_injective (injective_surjInv hf) (g ∘ f)

@[to_additive]
theorem tprod_comp_eq_tprod_of_bijective {f : ι → κ} (hf : f.Bijective) (g : κ → M) :
    ∏' i, g (f i) = ∏' j, g j :=
  (tprod_comp_le_tprod_of_injective hf.injective g).antisymm
    (tprod_le_tprod_comp_of_surjective hf.surjective g)

@[to_additive]
theorem tprod_comp_eq_tprod_of_equiv (e : ι ≃ κ) (g : κ → M) : ∏' i, g (e i) = ∏' j, g j :=
  tprod_comp_eq_tprod_of_bijective e.bijective ..

@[to_additive]
theorem tprod_subtype_sigma {β : ι → Type*} (f : ∀ i, β i → M) :
    ∏' p : Σ i, β i, f p.1 p.2 = ∏' (i) (j), f i j :=
  multipliable.tprod_sigma' (fun _ ↦ multipliable)

@[to_additive]
theorem tprod_subtype_sigma' {β : ι → Type*} (f : (Σ i, β i) → M) :
    ∏' p : Σ i, β i, f p = ∏' (i) (j), f ⟨i, j⟩ :=
  multipliable.tprod_sigma' (fun _ ↦ multipliable)

@[to_additive]
theorem tprod_subtype_iUnion_le_tprod (f : ι → M) (t : κ → Set ι) :
    ∏' x : ⋃ i, t i, f x ≤ ∏' i, ∏' x : t i, f x :=
  calc ∏' x : ⋃ i, t i, f x ≤ ∏' x : Σ i, t i, f x.2 :=
    tprod_le_tprod_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∏' i, ∏' x : t i, f x := tprod_subtype_sigma' _

@[to_additive]
theorem tprod_subtype_biUnion_le_tprod (f : ι → M) (s : Set κ) (t : κ → Set ι) :
    ∏' x : ⋃ i ∈ s, t i, f x ≤ ∏' i : s, ∏' x : t i, f x :=
  calc ∏' x : ⋃ i ∈ s, t i, f x = ∏' x : ⋃ i : s, t i, f x := by rw [tprod_congr_subtype]; simp
  _ ≤ ∏' i : s, (∏' x : t i, f x) := tprod_subtype_iUnion_le_tprod ..

@[to_additive]
theorem tprod_subtype_biUnion_le (f : ι → M) (s : Finset ι) (t : ι → Set ι) :
    ∏' x : ⋃ i ∈ s, t i, f x ≤ ∏ i ∈ s, ∏' x : t i, f x :=
  (tprod_subtype_biUnion_le_tprod f s.toSet t).trans_eq <|
    Finset.tprod_subtype s fun i ↦ ∏' x : t i, f x

@[to_additive]
theorem tprod_subtype_iUnion_le [Fintype ι] (f : ι → M) (t : ι → Set ι) :
    ∏' x : ⋃ i, t i, f x ≤ ∏ i, ∏' x : t i, f x := by
  rw [← tprod_fintype]
  exact tprod_subtype_iUnion_le_tprod f t

@[to_additive]
theorem tprod_subtype_iUnion_eq_tprod (f : ι → M) (t : ι → Set ι) (ht : Pairwise (Disjoint on t)) :
    ∏' x : ⋃ i, t i, f x = ∏' i, ∏' x : t i, f x :=
  calc ∏' x : ⋃ i, t i, f x = ∏' x : Σ i, t i, f x.2 := (tprod_comp_eq_tprod_of_bijective
      (sigmaToiUnion_bijective t (fun _ _ hij ↦ ht hij)) _).symm
    _ = _ := tprod_subtype_sigma' _

@[to_additive]
theorem _tprod_prod_uncurry {f : ι → κ → M} : ∏' p, uncurry f p = ∏' (i) (j), f i j :=
  multipliable.tprod_prod_uncurry <| by simp

end T3Space

section Ring

variable {R : Type*} {f : ι → R} {c : R}

variable [CommSemiring R] [CompleteLinearOrder R] [CanonicallyOrderedAdd R] [TopologicalSpace R]
  [OrderTopology R] [ContinuousMul R]

instance : IsQuantale R where
  mul_sSup_distrib c s := by
    rw [Monotone.map_sSup_of_continuousAt (continuous_mul_left c).continuousAt
      mul_left_mono ?_, sSup_image]
    simp [bot_eq_zero''']
  sSup_mul_distrib s c := by
    rw [Monotone.map_sSup_of_continuousAt (continuous_mul_right c).continuousAt
      mul_right_mono ?_, sSup_image]
    simp [show (⊥ : R) = 0 from bot_le.antisymm (zero_le _)]

variable [IsOrderedRing R]

theorem mul_tsum_distrib (c : R) : c * ∑' i, f i = ∑' i, c * f i := by
  simp_rw [tsum_eq_iSup_sum, Quantale.mul_iSup_distrib, Finset.mul_sum]

theorem tsum_mul_distrib (c : R) : (∑' i, f i) * c = ∑' i, f i * c := by
  simp_rw [tsum_eq_iSup_sum, Quantale.iSup_mul_distrib, Finset.sum_mul]

theorem tsum_const_smul {S : Type*} [SMul S R] [IsScalarTower S R R] (a : S) :
    a • ∑' i, f i = ∑' i, a • f i := by
  simpa using (mul_tsum_distrib (f := f) (a • (1 : R)))

end Ring






-- protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ∞) → ∑' a, f a = ∞
--   | ⟨a, ha⟩ => top_unique <| ha ▸ ENNReal.le_tsum a

-- protected theorem lt_top_of_tsum_ne_top {a : α → ℝ≥0∞} (tsum_ne_top : ∑' i, a i ≠ ∞) (j : α) :
--     a j < ∞ := by
--   contrapose! tsum_ne_top with h
--   exact ENNReal.tsum_eq_top_of_eq_top ⟨j, top_unique h⟩


-- theorem tsum_const_eq_top_of_ne_zero {α : Type*} [Infinite α] {c : ℝ≥0∞} (hc : c ≠ 0) :
--     ∑' _ : α, c = ∞ := by
--   have A : Tendsto (fun n : ℕ => (n : ℝ≥0∞) * c) atTop (𝓝 (∞ * c)) := by
--     apply ENNReal.Tendsto.mul_const tendsto_nat_nhds_top
--     simp only [true_or, top_ne_zero, Ne, not_false_iff]
--   have B : ∀ n : ℕ, (n : ℝ≥0∞) * c ≤ ∑' _ : α, c := fun n => by
--     rcases Infinite.exists_subset_card_eq α n with ⟨s, hs⟩
--     simpa [hs] using @ENNReal.sum_le_tsum α (fun _ => c) s
--   simpa [hc] using le_of_tendsto' A B

-- protected theorem ne_top_of_tsum_ne_top (h : ∑' a, f a ≠ ∞) (a : α) : f a ≠ ∞ := fun ha =>
--   h <| ENNReal.tsum_eq_top_of_eq_top ⟨a, ha⟩

-- protected theorem tsum_mul_left : ∑' i, a * f i = a * ∑' i, f i := by
--   by_cases hf : ∀ i, f i = 0
--   · simp [hf]
--   · rw [← ENNReal.tsum_eq_zero] at hf
--     have : Tendsto (fun s : Finset α => ∑ j ∈ s, a * f j) atTop (𝓝 (a * ∑' i, f i)) := by
--       simp only [← Finset.mul_sum]
--       exact ENNReal.Tendsto.const_mul ENNReal.summable.hasSum (Or.inl hf)
--     exact HasSum.tsum_eq this

-- protected theorem tsum_mul_right : ∑' i, f i * a = (∑' i, f i) * a := by
--   simp [mul_comm, ENNReal.tsum_mul_left]






-- theorem tendsto_nat_tsum (f : ℕ → ℝ≥0∞) :
--     Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 (∑' n, f n)) := by
--   rw [← hasSum_iff_tendsto_nat]
--   exact ENNReal.summable.hasSum

-- theorem toNNReal_apply_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) (x : α) :
--     (((ENNReal.toNNReal ∘ f) x : ℝ≥0) : ℝ≥0∞) = f x :=
--   coe_toNNReal <| ENNReal.ne_top_of_tsum_ne_top hf _

-- theorem summable_toNNReal_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) :
--     Summable (ENNReal.toNNReal ∘ f) := by
--   simpa only [← tsum_coe_ne_top_iff_summable, toNNReal_apply_of_tsum_ne_top hf] using hf

-- theorem tendsto_cofinite_zero_of_tsum_ne_top {α} {f : α → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
--     Tendsto f cofinite (𝓝 0) := by
--   have f_ne_top : ∀ n, f n ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hf
--   have h_f_coe : f = fun n => ((f n).toNNReal : ENNReal) :=
--     funext fun n => (coe_toNNReal (f_ne_top n)).symm
--   rw [h_f_coe, ← @coe_zero, tendsto_coe]
--   exact NNReal.tendsto_cofinite_zero_of_summable (summable_toNNReal_of_tsum_ne_top hf)

-- theorem tendsto_atTop_zero_of_tsum_ne_top {f : ℕ → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
--     Tendsto f atTop (𝓝 0) := by
--   rw [← Nat.cofinite_eq_atTop]
--   exact tendsto_cofinite_zero_of_tsum_ne_top hf

-- /-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
-- space. This does not need a summability assumption, as otherwise all sums are zero. -/
-- theorem tendsto_tsum_compl_atTop_zero {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
--     Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
--   lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
--   convert ENNReal.tendsto_coe.2 (NNReal.tendsto_tsum_compl_atTop_zero f)
--   rw [ENNReal.coe_tsum]
--   exact NNReal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective

-- protected theorem tsum_apply {ι α : Type*} {f : ι → α → ℝ≥0∞} {x : α} :
--     (∑' i, f i) x = ∑' i, f i x :=
--   tsum_apply <| Pi.summable.mpr fun _ => ENNReal.summable

-- theorem tsum_sub {f : ℕ → ℝ≥0∞} {g : ℕ → ℝ≥0∞} (h₁ : ∑' i, g i ≠ ∞) (h₂ : g ≤ f) :
--     ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i :=
--   have : ∀ i, f i - g i + g i = f i := fun i => tsub_add_cancel_of_le (h₂ i)
--   ENNReal.eq_sub_of_add_eq h₁ <| by simp only [← ENNReal.tsum_add, this]

-- theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → ℝ≥0∞) :
--     ∑' x, g (f x) ≤ ∑' y, g y :=
--   ENNReal.summable.tsum_le_tsum_of_inj f hf (fun _ _ => zero_le _) (fun _ => le_rfl)
--     ENNReal.summable

-- theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → ℝ≥0∞) :
--     ∑' y, g y ≤ ∑' x, g (f x) :=
--   calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
--   _ ≤ ∑' x, g (f x) := tsum_comp_le_tsum_of_injective (injective_surjInv hf) _

-- theorem tsum_mono_subtype (f : α → ℝ≥0∞) {s t : Set α} (h : s ⊆ t) :
--     ∑' x : s, f x ≤ ∑' x : t, f x :=
--   tsum_comp_le_tsum_of_injective (inclusion_injective h) _

-- theorem tsum_iUnion_le_tsum {ι : Type*} (f : α → ℝ≥0∞) (t : ι → Set α) :
--     ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : t i, f x :=
--   calc ∑' x : ⋃ i, t i, f x ≤ ∑' x : Σ i, t i, f x.2 :=
--     tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
--   _ = ∑' i, ∑' x : t i, f x := ENNReal.tsum_sigma' _

-- theorem tsum_biUnion_le_tsum {ι : Type*} (f : α → ℝ≥0∞) (s : Set ι) (t : ι → Set α) :
--     ∑' x : ⋃ i ∈ s , t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
--   calc ∑' x : ⋃ i ∈ s, t i, f x = ∑' x : ⋃ i : s, t i, f x := tsum_congr_set_coe _ <| by simp
--   _ ≤ ∑' i : s, ∑' x : t i, f x := tsum_iUnion_le_tsum _ _

-- theorem tsum_biUnion_le {ι : Type*} (f : α → ℝ≥0∞) (s : Finset ι) (t : ι → Set α) :
--     ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i ∈ s, ∑' x : t i, f x :=
--   (tsum_biUnion_le_tsum f s.toSet t).trans_eq (Finset.tsum_subtype s fun i => ∑' x : t i, f x)

-- theorem tsum_iUnion_le {ι : Type*} [Fintype ι] (f : α → ℝ≥0∞) (t : ι → Set α) :
--     ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x := by
--   rw [← tsum_fintype]
--   exact tsum_iUnion_le_tsum f t

-- theorem tsum_union_le (f : α → ℝ≥0∞) (s t : Set α) :
--     ∑' x : ↑(s ∪ t), f x ≤ ∑' x : s, f x + ∑' x : t, f x :=
--   calc ∑' x : ↑(s ∪ t), f x = ∑' x : ⋃ b, cond b s t, f x := tsum_congr_set_coe _ union_eq_iUnion
--   _ ≤ _ := by simpa using tsum_iUnion_le f (cond · s t)

-- open Classical in
-- theorem tsum_eq_add_tsum_ite {f : β → ℝ≥0∞} (b : β) :
--     ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
--   ENNReal.summable.tsum_eq_add_tsum_ite' b

-- theorem tsum_add_one_eq_top {f : ℕ → ℝ≥0∞} (hf : ∑' n, f n = ∞) (hf0 : f 0 ≠ ∞) :
--     ∑' n, f (n + 1) = ∞ := by
--   rw [tsum_eq_zero_add' ENNReal.summable, add_eq_top] at hf
--   exact hf.resolve_left hf0

-- /-- A sum of extended nonnegative reals which is finite can have only finitely many terms
-- above any positive threshold. -/
-- theorem finite_const_le_of_tsum_ne_top {ι : Type*} {a : ι → ℝ≥0∞} (tsum_ne_top : ∑' i, a i ≠ ∞)
--     {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) : { i : ι | ε ≤ a i }.Finite := by
--   by_contra h
--   have := Infinite.to_subtype h
--   refine tsum_ne_top (top_unique ?_)
--   calc ∞ = ∑' _ : { i | ε ≤ a i }, ε := (tsum_const_eq_top_of_ne_zero ε_ne_zero).symm
--   _ ≤ ∑' i, a i := ENNReal.summable.tsum_le_tsum_of_inj (↑)
--     Subtype.val_injective (fun _ _ => zero_le _) (fun i => i.2) ENNReal.summable

-- /-- Markov's inequality for `Finset.card` and `tsum` in `ℝ≥0∞`. -/
-- theorem finset_card_const_le_le_of_tsum_le {ι : Type*} {a : ι → ℝ≥0∞} {c : ℝ≥0∞} (c_ne_top : c ≠ ∞)
--     (tsum_le_c : ∑' i, a i ≤ c) {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) :
--     ∃ hf : { i : ι | ε ≤ a i }.Finite, #hf.toFinset ≤ c / ε := by
--   have hf : { i : ι | ε ≤ a i }.Finite :=
--     finite_const_le_of_tsum_ne_top (ne_top_of_le_ne_top c_ne_top tsum_le_c) ε_ne_zero
--   refine ⟨hf, (ENNReal.le_div_iff_mul_le (.inl ε_ne_zero) (.inr c_ne_top)).2 ?_⟩
--   calc #hf.toFinset * ε = ∑ _i ∈ hf.toFinset, ε := by rw [Finset.sum_const, nsmul_eq_mul]
--     _ ≤ ∑ i ∈ hf.toFinset, a i := Finset.sum_le_sum fun i => hf.mem_toFinset.1
--     _ ≤ ∑' i, a i := ENNReal.sum_le_tsum _
--     _ ≤ c := tsum_le_c

-- theorem tsum_fiberwise (f : β → ℝ≥0∞) (g : β → γ) :
--     ∑' x, ∑' b : g ⁻¹' {x}, f b = ∑' i, f i := by
--   apply HasSum.tsum_eq
--   let equiv := Equiv.sigmaFiberEquiv g
--   apply (equiv.hasSum_iff.mpr ENNReal.summable.hasSum).sigma
--   exact fun _ ↦ ENNReal.summable.hasSum_iff.mpr rfl

-- end tsum


-- /-
-- DEPRECATED list


-- tsum_mul_tsum
-- tsum_mul_tsum_eq_tsum_sum_antidiagonal
-- tsum_mul_tsum_eq_tsum_sum_range
-- -/

-- -- #check MonotoneOn.map_csSup_of_continuousWithinAt

-- -- example {α β : Type*} [CompleteLattice α] [CompleteLattice β] [TopologicalSpace α]
-- --   [TopologicalSpace β] [OrderTopology α] [OrderClosedTopology α] {f : α → β} (hf : Continuous f)
-- --     (hmono : Monotone f) (A : Set α) : f (sSup A) = sSup (f '' A) := by
-- --   _

-- -- #check isLUB_of_tendsto



-- --   simp_rw [le_iff_exists_add] at hb
-- --   choose d hd using hb


-- -- theorem mul_tprod {R : Type*} [Semiring R] [CompleteLattice R] [IsOrderedAddMonoid R]
-- --     [TopologicalSpace R] [T2Space R] [ContinuousAdd R] [SupSummable R]
-- --     [CanonicallyOrderedAdd R] [MulLeftMono R]
-- --     {f : ι → R} (c : R) : c * ∏' i, f i = ∏' a, c * f i := by
-- --   rw [tprod_eq_iSup_prod, tprod_eq_iSup_prod]
-- --   simp_rw [← Finset.mul_prod, mul_iSup]

-- --   -- refine' (monotone_id.const_mul' _).map_iSup_of_continuousAt (ι := R) (β := R) _ (mul_zero c)
-- --   -- apply Monotone.iSup_comp_eq (f := c * (·))
-- --   -- simp_rw [ENat.tprod_eq_iSup_prod, ENat.mul_iSup, Finset.mul_prod]

-- -- -- theorem tprod_mul (c : ℕ∞) : (∏' i, f i) * c = ∏' i, f i * c := by
-- -- --   simp_rw [ENat.tprod_eq_iSup_prod, ENat.iSup_mul, Finset.prod_mul]



-- -- end T2Space
