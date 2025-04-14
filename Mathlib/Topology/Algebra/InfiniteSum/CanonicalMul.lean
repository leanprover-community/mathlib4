import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Separation.Regular

variable {M ι κ : Type*} {i j : ι} {f g : ι → M} {s t : Set ι}

variable [CommMonoid M] [CompleteLattice M] [IsOrderedMonoid M]
    [TopologicalSpace M] [SupConvergenceClass M] [CanonicallyOrderedMul M]

-- Underscores are to prevent conflicts with currently deprecated declarations

open Set Topology Function

/-- If a topological monoid is a canonically ordered complete lattice with well-behaved
suprema, then every function is multipliable. -/
@[to_additive]
theorem hasProd : HasProd f (⨆ s : Finset ι, ∏ i ∈ s, f i) :=
  tendsto_atTop_iSup <| fun _ _ ↦ Finset.prod_le_prod_of_subset'

@[to_additive (attr := simp)]
theorem multipliable : Multipliable f :=
  hasProd.multipliable

section T2Space

variable [T2Space M]

@[to_additive]
theorem tprod_eq_iSup_prod : ∏' i, f i = ⨆ s : Finset ι, ∏ i ∈ s, f i :=
  hasProd.tprod_eq

@[to_additive]
theorem tprod_eq_iSup_prod' {s : κ → Finset ι} (hs : ∀ t, ∃ k, t ⊆ s k) :
    ∏' i, f i = ⨆ k, ∏ i ∈ s k, f i := by
  rw [tprod_eq_iSup_prod, eq_comm]
  exact (Finset.prod_mono_set' f).iSup_comp_eq hs

@[to_additive]
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


/-
DEPRECATED list


tsum_mul_tsum
tsum_mul_tsum_eq_tsum_sum_antidiagonal
tsum_mul_tsum_eq_tsum_sum_range
-/



-- theorem mul_iSup {R : Type*} [Semiring R] [CompleteLattice R] [IsOrderedAddMonoid R]
--      [CanonicallyOrderedAdd R] [MulLeftMono R] {f : ι → R} (c : R)
-- : c * ⨆ i, f i = ⨆ a, c * f i := by
--   simp [le_antisymm_iff]
--   refine ⟨?_, fun a ↦ mul_le_mul_left' (le_iSup _ _) c⟩
--   simp_rw [le_iSup_iff]
--   intro b hb
--   simp_rw [le_iff_exists_add] at hb
--   choose d hd using hb


-- theorem mul_tprod {R : Type*} [Semiring R] [CompleteLattice R] [IsOrderedAddMonoid R]
--     [TopologicalSpace R] [T2Space R] [ContinuousAdd R] [SupSummable R]
--     [CanonicallyOrderedAdd R] [MulLeftMono R]
--     {f : ι → R} (c : R) : c * ∏' i, f i = ∏' a, c * f i := by
--   rw [tprod_eq_iSup_prod, tprod_eq_iSup_prod]
--   simp_rw [← Finset.mul_prod, mul_iSup]

--   -- refine' (monotone_id.const_mul' _).map_iSup_of_continuousAt (ι := R) (β := R) _ (mul_zero c)
--   -- apply Monotone.iSup_comp_eq (f := c * (·))
--   -- simp_rw [ENat.tprod_eq_iSup_prod, ENat.mul_iSup, Finset.mul_prod]

-- -- theorem tprod_mul (c : ℕ∞) : (∏' i, f i) * c = ∏' i, f i * c := by
-- --   simp_rw [ENat.tprod_eq_iSup_prod, ENat.iSup_mul, Finset.prod_mul]



-- end T2Space
