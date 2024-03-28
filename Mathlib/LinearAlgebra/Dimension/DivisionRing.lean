/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen,
Scott Morrison, Chris Hughes, Anne Baanen, Junyan Xu
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.SetTheory.Cardinal.Subfield
import Mathlib.LinearAlgebra.Dimension.Constructions

#align_import linear_algebra.dimension from "leanprover-community/mathlib"@"47a5f8186becdbc826190ced4312f8199f9db6a5"

/-!
# Dimension of vector spaces

In this file we provide results about `Module.rank` and `FiniteDimensional.finrank` of vector spaces
over division rings.

## Main statements

For vector spaces (i.e. modules over a field), we have

* `rank_quotient_add_rank`: if `V₁` is a submodule of `V`, then
  `Module.rank (V/V₁) + Module.rank V₁ = Module.rank V`.
* `rank_range_add_rank_ker`: the rank-nullity theorem.
* `rank_dual_eq_card_dual_of_aleph0_le_rank`: The **Erdős-Kaplansky Theorem** which says that
  the dimension of an infinite-dimensional dual space over a division ring has dimension
  equal to its cardinality.

-/


noncomputable section

universe u v v' v'' u₁' w w'

variable {K R : Type u} {V V₁ V₂ V₃ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}
variable {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type*}

open BigOperators Cardinal Basis Submodule Function Set

section Module

section DivisionRing

variable [DivisionRing K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup V'] [Module K V']
variable [AddCommGroup V₁] [Module K V₁]

/-- If a vector space has a finite dimension, the index set of `Basis.ofVectorSpace` is finite. -/
theorem Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0 (h : Module.rank K V < ℵ₀) :
    (Basis.ofVectorSpaceIndex K V).Finite :=
  finite_def.2 <| (Basis.ofVectorSpace K V).nonempty_fintype_index_of_rank_lt_aleph0 h
#align basis.finite_of_vector_space_index_of_rank_lt_aleph_0 Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0

theorem rank_quotient_add_rank (p : Submodule K V) :
    Module.rank K (V ⧸ p) + Module.rank K p = Module.rank K V := by
  classical
    let ⟨f⟩ := quotient_prod_linearEquiv p
    exact rank_prod'.symm.trans f.rank_eq
#align rank_quotient_add_rank rank_quotient_add_rank

/-- The **rank-nullity theorem** -/
theorem rank_range_add_rank_ker (f : V →ₗ[K] V₁) :
    Module.rank K (LinearMap.range f) + Module.rank K (LinearMap.ker f) = Module.rank K V := by
  haveI := fun p : Submodule K V => Classical.decEq (V ⧸ p)
  rw [← f.quotKerEquivRange.rank_eq, rank_quotient_add_rank]
#align rank_range_add_rank_ker rank_range_add_rank_ker

theorem rank_eq_of_surjective (f : V →ₗ[K] V₁) (h : Surjective f) :
    Module.rank K V = Module.rank K V₁ + Module.rank K (LinearMap.ker f) := by
  rw [← rank_range_add_rank_ker f, ← rank_range_of_surjective f h]
#align rank_eq_of_surjective rank_eq_of_surjective

/-- Given a family of `n` linearly independent vectors in a space of dimension `> n`, one may extend
the family by another vector while retaining linear independence. -/
theorem exists_linearIndependent_cons_of_lt_rank {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (h : n < Module.rank K V) :
    ∃ (x : V), LinearIndependent K (Fin.cons x v) := by
  have A : Submodule.span K (range v) ≠ ⊤ := by
    intro H
    rw [← rank_top, ← H] at h
    have : Module.rank K (Submodule.span K (range v)) ≤ n := by
      have := Cardinal.mk_range_le_lift (f := v)
      simp only [Cardinal.lift_id'] at this
      exact (rank_span_le _).trans (this.trans (by simp))
    exact lt_irrefl _ (h.trans_le this)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ Submodule.span K (range v) := by
    contrapose! A
    exact Iff.mpr Submodule.eq_top_iff' A
  exact ⟨x, linearIndependent_fin_cons.2 ⟨hv, hx⟩⟩

/-- Given a family of `n` linearly independent vectors in a space of dimension `> n`, one may extend
the family by another vector while retaining linear independence. -/
theorem exists_linearIndependent_snoc_of_lt_rank {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (h : n < Module.rank K V) :
    ∃ (x : V), LinearIndependent K (Fin.snoc v x) := by
  simpa [linearIndependent_fin_cons, ← linearIndependent_fin_snoc]
    using exists_linearIndependent_cons_of_lt_rank hv h

/-- Given a nonzero vector in a space of dimension `> 1`, one may find another vector linearly
independent of the first one. -/
theorem exists_linearIndependent_pair_of_one_lt_rank
    (h : 1 < Module.rank K V) {x : V} (hx : x ≠ 0) :
    ∃ y, LinearIndependent K ![x, y] := by
  obtain ⟨y, hy⟩ := exists_linearIndependent_snoc_of_lt_rank (linearIndependent_unique ![x] hx) h
  have : Fin.snoc ![x] y = ![x, y] := Iff.mp List.ofFn_inj rfl
  rw [this] at hy
  exact ⟨y, hy⟩

section

variable [AddCommGroup V₂] [Module K V₂]
variable [AddCommGroup V₃] [Module K V₃]

open LinearMap

/-- This is mostly an auxiliary lemma for `Submodule.rank_sup_add_rank_inf_eq`. -/
theorem rank_add_rank_split (db : V₂ →ₗ[K] V) (eb : V₃ →ₗ[K] V) (cd : V₁ →ₗ[K] V₂)
    (ce : V₁ →ₗ[K] V₃) (hde : ⊤ ≤ LinearMap.range db ⊔ LinearMap.range eb) (hgd : ker cd = ⊥)
    (eq : db.comp cd = eb.comp ce) (eq₂ : ∀ d e, db d = eb e → ∃ c, cd c = d ∧ ce c = e) :
    Module.rank K V + Module.rank K V₁ = Module.rank K V₂ + Module.rank K V₃ := by
  have hf : Surjective (coprod db eb) := by rwa [← range_eq_top, range_coprod, eq_top_iff]
  conv =>
    rhs
    rw [← rank_prod', rank_eq_of_surjective _ hf]
  congr 1
  apply LinearEquiv.rank_eq
  let L : V₁ →ₗ[K] ker (coprod db eb) := by -- Porting note: this is needed to avoid a timeout
    refine' LinearMap.codRestrict _ (prod cd (-ce)) _
    · intro c
      simp only [add_eq_zero_iff_eq_neg, LinearMap.prod_apply, mem_ker, Pi.prod, coprod_apply,
        neg_neg, map_neg, neg_apply]
      exact LinearMap.ext_iff.1 eq c
  refine' LinearEquiv.ofBijective L ⟨_, _⟩
  · rw [← ker_eq_bot, ker_codRestrict, ker_prod, hgd, bot_inf_eq]
  · rw [← range_eq_top, eq_top_iff, range_codRestrict, ← map_le_iff_le_comap, Submodule.map_top,
      range_subtype]
    rintro ⟨d, e⟩
    have h := eq₂ d (-e)
    simp only [add_eq_zero_iff_eq_neg, LinearMap.prod_apply, mem_ker, SetLike.mem_coe,
      Prod.mk.inj_iff, coprod_apply, map_neg, neg_apply, LinearMap.mem_range, Pi.prod] at h ⊢
    intro hde
    rcases h hde with ⟨c, h₁, h₂⟩
    refine' ⟨c, h₁, _⟩
    rw [h₂, _root_.neg_neg]
#align rank_add_rank_split rank_add_rank_split

theorem Submodule.rank_sup_add_rank_inf_eq (s t : Submodule K V) :
    Module.rank K (s ⊔ t : Submodule K V) + Module.rank K (s ⊓ t : Submodule K V) =
    Module.rank K s + Module.rank K t :=
  rank_add_rank_split
    (inclusion le_sup_left) (inclusion le_sup_right)
    (inclusion inf_le_left) (inclusion inf_le_right)
    (by
      rw [← map_le_map_iff' (ker_subtype <| s ⊔ t), Submodule.map_sup, Submodule.map_top, ←
        LinearMap.range_comp, ← LinearMap.range_comp, subtype_comp_inclusion,
        subtype_comp_inclusion, range_subtype, range_subtype, range_subtype])
    (ker_inclusion _ _ _) (by ext ⟨x, hx⟩; rfl)
    (by
      rintro ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ eq
      obtain rfl : b₁ = b₂ := congr_arg Subtype.val eq
      exact ⟨⟨b₁, hb₁, hb₂⟩, rfl, rfl⟩)
#align submodule.rank_sup_add_rank_inf_eq Submodule.rank_sup_add_rank_inf_eq

theorem Submodule.rank_add_le_rank_add_rank (s t : Submodule K V) :
    Module.rank K (s ⊔ t : Submodule K V) ≤ Module.rank K s + Module.rank K t := by
  rw [← Submodule.rank_sup_add_rank_inf_eq]
  exact self_le_add_right _ _
#align submodule.rank_add_le_rank_add_rank Submodule.rank_add_le_rank_add_rank

end

end DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
variable [AddCommGroup V'] [Module K V']

/-- The `ι` indexed basis on `V`, where `ι` is an empty type and `V` is zero-dimensional.

See also `FiniteDimensional.finBasis`.
-/
def Basis.ofRankEqZero {ι : Type*} [IsEmpty ι] (hV : Module.rank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := rank_zero_iff.1 hV
  Basis.empty _
#align basis.of_rank_eq_zero Basis.ofRankEqZero

@[simp]
theorem Basis.ofRankEqZero_apply {ι : Type*} [IsEmpty ι] (hV : Module.rank K V = 0) (i : ι) :
    Basis.ofRankEqZero hV i = 0 :=
  rfl
#align basis.of_rank_eq_zero_apply Basis.ofRankEqZero_apply

theorem le_rank_iff_exists_linearIndependent {c : Cardinal} :
    c ≤ Module.rank K V ↔ ∃ s : Set V, #s = c ∧ LinearIndependent K ((↑) : s → V) := by
  constructor
  · intro h
    let t := Basis.ofVectorSpace K V
    rw [← t.mk_eq_rank'', Cardinal.le_mk_iff_exists_subset] at h
    rcases h with ⟨s, hst, hsc⟩
    exact ⟨s, hsc, (ofVectorSpaceIndex.linearIndependent K V).mono hst⟩
  · rintro ⟨s, rfl, si⟩
    exact si.cardinal_le_rank
#align le_rank_iff_exists_linear_independent le_rank_iff_exists_linearIndependent

theorem le_rank_iff_exists_linearIndependent_finset {n : ℕ} : ↑n ≤ Module.rank K V ↔
    ∃ s : Finset V, s.card = n ∧ LinearIndependent K ((↑) : ↥(s : Set V) → V) := by
  simp only [le_rank_iff_exists_linearIndependent, Cardinal.mk_set_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩
#align le_rank_iff_exists_linear_independent_finset le_rank_iff_exists_linearIndependent_finset

/-- A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
theorem rank_le_one_iff : Module.rank K V ≤ 1 ↔ ∃ v₀ : V, ∀ v, ∃ r : K, r • v₀ = v := by
  let b := Basis.ofVectorSpace K V
  constructor
  · intro hd
    rw [← b.mk_eq_rank'', Cardinal.le_one_iff_subsingleton, subsingleton_coe] at hd
    rcases eq_empty_or_nonempty (ofVectorSpaceIndex K V) with (hb | ⟨⟨v₀, hv₀⟩⟩)
    · use 0
      have h' : ∀ v : V, v = 0 := by simpa [b, hb, Submodule.eq_bot_iff] using b.span_eq.symm
      intro v
      simp [h' v]
    · use v₀
      have h' : (K ∙ v₀) = ⊤ := by simpa [b, hd.eq_singleton_of_mem hv₀] using b.span_eq
      intro v
      have hv : v ∈ (⊤ : Submodule K V) := mem_top
      rwa [← h', mem_span_singleton] at hv
  · rintro ⟨v₀, hv₀⟩
    have h : (K ∙ v₀) = ⊤ := by
      ext
      simp [mem_span_singleton, hv₀]
    rw [← rank_top, ← h]
    refine' (rank_span_le _).trans_eq _
    simp
#align rank_le_one_iff rank_le_one_iff

/-- A submodule has dimension at most `1` if and only if there is a
single vector in the submodule such that the submodule is contained in
its span. -/
theorem rank_submodule_le_one_iff (s : Submodule K V) :
    Module.rank K s ≤ 1 ↔ ∃ v₀ ∈ s, s ≤ K ∙ v₀ := by
  simp_rw [rank_le_one_iff, le_span_singleton_iff]
  constructor
  · rintro ⟨⟨v₀, hv₀⟩, h⟩
    use v₀, hv₀
    intro v hv
    obtain ⟨r, hr⟩ := h ⟨v, hv⟩
    use r
    simp_rw [Subtype.ext_iff, coe_smul] at hr
    exact hr
  · rintro ⟨v₀, hv₀, h⟩
    use ⟨v₀, hv₀⟩
    rintro ⟨v, hv⟩
    obtain ⟨r, hr⟩ := h v hv
    use r
    simp_rw [Subtype.ext_iff, coe_smul]
    exact hr
#align rank_submodule_le_one_iff rank_submodule_le_one_iff

/-- A submodule has dimension at most `1` if and only if there is a
single vector, not necessarily in the submodule, such that the
submodule is contained in its span. -/
theorem rank_submodule_le_one_iff' (s : Submodule K V) :
    Module.rank K s ≤ 1 ↔ ∃ v₀, s ≤ K ∙ v₀ := by
  rw [rank_submodule_le_one_iff]
  constructor
  · rintro ⟨v₀, _, h⟩
    exact ⟨v₀, h⟩
  · rintro ⟨v₀, h⟩
    by_cases hw : ∃ w : V, w ∈ s ∧ w ≠ 0
    · rcases hw with ⟨w, hw, hw0⟩
      use w, hw
      rcases mem_span_singleton.1 (h hw) with ⟨r', rfl⟩
      have h0 : r' ≠ 0 := by
        rintro rfl
        simp at hw0
      rwa [span_singleton_smul_eq (IsUnit.mk0 _ h0) _]
    · push_neg at hw
      rw [← Submodule.eq_bot_iff] at hw
      simp [hw]
#align rank_submodule_le_one_iff' rank_submodule_le_one_iff'

theorem Submodule.rank_le_one_iff_isPrincipal (W : Submodule K V) :
    Module.rank K W ≤ 1 ↔ W.IsPrincipal := by
  simp only [rank_le_one_iff, Submodule.isPrincipal_iff, le_antisymm_iff, le_span_singleton_iff,
    span_singleton_le_iff_mem]
  constructor
  · rintro ⟨⟨m, hm⟩, hm'⟩
    choose f hf using hm'
    exact ⟨m, ⟨fun v hv => ⟨f ⟨v, hv⟩, congr_arg ((↑) : W → V) (hf ⟨v, hv⟩)⟩, hm⟩⟩
  · rintro ⟨a, ⟨h, ha⟩⟩
    choose f hf using h
    exact ⟨⟨a, ha⟩, fun v => ⟨f v.1 v.2, Subtype.ext (hf v.1 v.2)⟩⟩
#align submodule.rank_le_one_iff_is_principal Submodule.rank_le_one_iff_isPrincipal

theorem Module.rank_le_one_iff_top_isPrincipal :
    Module.rank K V ≤ 1 ↔ (⊤ : Submodule K V).IsPrincipal := by
  rw [← Submodule.rank_le_one_iff_isPrincipal, rank_top]
#align module.rank_le_one_iff_top_is_principal Module.rank_le_one_iff_top_isPrincipal

end Module

section Span

open Submodule FiniteDimensional

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Given a family of `n` linearly independent vectors in a finite-dimensional space of
dimension `> n`, one may extend the family by another vector while retaining linear independence. -/
theorem exists_linearIndependent_snoc_of_lt_finrank {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (h : n < finrank K V) :
    ∃ (x : V), LinearIndependent K (Fin.snoc v x) :=
  exists_linearIndependent_snoc_of_lt_rank hv (lt_rank_of_lt_finrank h)

/-- Given a family of `n` linearly independent vectors in a finite-dimensional space of
dimension `> n`, one may extend the family by another vector while retaining linear independence. -/
theorem exists_linearIndependent_cons_of_lt_finrank {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (h : n < finrank K V) :
    ∃ (x : V), LinearIndependent K (Fin.cons x v) :=
  exists_linearIndependent_cons_of_lt_rank hv (lt_rank_of_lt_finrank h)

/-- Given a nonzero vector in a finite-dimensional space of dimension `> 1`, one may find another
vector linearly independent of the first one. -/
theorem exists_linearIndependent_pair_of_one_lt_finrank
    (h : 1 < finrank K V) {x : V} (hx : x ≠ 0) :
    ∃ y, LinearIndependent K ![x, y] :=
  exists_linearIndependent_pair_of_one_lt_rank (one_lt_rank_of_one_lt_finrank h) hx

end Span

section Basis

open FiniteDimensional

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem linearIndependent_of_top_le_span_of_card_eq_finrank {ι : Type*} [Fintype ι] {b : ι → V}
    (spans : ⊤ ≤ span K (Set.range b)) (card_eq : Fintype.card ι = finrank K V) :
    LinearIndependent K b :=
  linearIndependent_iff'.mpr fun s g dependent i i_mem_s => by
    classical
    by_contra gx_ne_zero
    -- We'll derive a contradiction by showing `b '' (univ \ {i})` of cardinality `n - 1`
    -- spans a vector space of dimension `n`.
    refine' not_le_of_gt (span_lt_top_of_card_lt_finrank
      (show (b '' (Set.univ \ {i})).toFinset.card < finrank K V from _)) _
    · calc
        (b '' (Set.univ \ {i})).toFinset.card = ((Set.univ \ {i}).toFinset.image b).card := by
          rw [Set.toFinset_card, Fintype.card_ofFinset]
        _ ≤ (Set.univ \ {i}).toFinset.card := Finset.card_image_le
        _ = (Finset.univ.erase i).card := (congr_arg Finset.card (Finset.ext (by simp [and_comm])))
        _ < Finset.univ.card := (Finset.card_erase_lt_of_mem (Finset.mem_univ i))
        _ = finrank K V := card_eq
    -- We already have that `b '' univ` spans the whole space,
    -- so we only need to show that the span of `b '' (univ \ {i})` contains each `b j`.
    refine' spans.trans (span_le.mpr _)
    rintro _ ⟨j, rfl, rfl⟩
    -- The case that `j ≠ i` is easy because `b j ∈ b '' (univ \ {i})`.
    by_cases j_eq : j = i
    swap
    · refine' subset_span ⟨j, (Set.mem_diff _).mpr ⟨Set.mem_univ _, _⟩, rfl⟩
      exact mt Set.mem_singleton_iff.mp j_eq
    -- To show `b i ∈ span (b '' (univ \ {i}))`, we use that it's a weighted sum
    -- of the other `b j`s.
    rw [j_eq, SetLike.mem_coe, show b i = -((g i)⁻¹ • (s.erase i).sum fun j => g j • b j) from _]
    · refine' neg_mem (smul_mem _ _ (sum_mem fun k hk => _))
      obtain ⟨k_ne_i, _⟩ := Finset.mem_erase.mp hk
      refine' smul_mem _ _ (subset_span ⟨k, _, rfl⟩)
      simp_all only [Set.mem_univ, Set.mem_diff, Set.mem_singleton_iff, and_self, not_false_eq_true]
    -- To show `b i` is a weighted sum of the other `b j`s, we'll rewrite this sum
    -- to have the form of the assumption `dependent`.
    apply eq_neg_of_add_eq_zero_left
    calc
      (b i + (g i)⁻¹ • (s.erase i).sum fun j => g j • b j) =
          (g i)⁻¹ • (g i • b i + (s.erase i).sum fun j => g j • b j) :=
        by rw [smul_add, ← mul_smul, inv_mul_cancel gx_ne_zero, one_smul]
      _ = (g i)⁻¹ • (0 : V) := (congr_arg _ ?_)
      _ = 0 := smul_zero _
    -- And then it's just a bit of manipulation with finite sums.
    rwa [← Finset.insert_erase i_mem_s, Finset.sum_insert (Finset.not_mem_erase _ _)] at dependent
#align linear_independent_of_top_le_span_of_card_eq_finrank linearIndependent_of_top_le_span_of_card_eq_finrank

/-- A finite family of vectors is linearly independent if and only if
its cardinality equals the dimension of its span. -/
theorem linearIndependent_iff_card_eq_finrank_span {ι : Type*} [Fintype ι] {b : ι → V} :
    LinearIndependent K b ↔ Fintype.card ι = (Set.range b).finrank K := by
  constructor
  · intro h
    exact (finrank_span_eq_card h).symm
  · intro hc
    let f := Submodule.subtype (span K (Set.range b))
    let b' : ι → span K (Set.range b) := fun i =>
      ⟨b i, mem_span.2 fun p hp => hp (Set.mem_range_self _)⟩
    have hs : ⊤ ≤ span K (Set.range b') := by
      intro x
      have h : span K (f '' Set.range b') = map f (span K (Set.range b')) := span_image f
      have hf : f '' Set.range b' = Set.range b := by
        ext x
        simp [f, Set.mem_image, Set.mem_range]
      rw [hf] at h
      have hx : (x : V) ∈ span K (Set.range b) := x.property
      conv at hx =>
        arg 2
        rw [h]
      simpa [f, mem_map] using hx
    have hi : LinearMap.ker f = ⊥ := ker_subtype _
    convert (linearIndependent_of_top_le_span_of_card_eq_finrank hs hc).map' _ hi
#align linear_independent_iff_card_eq_finrank_span linearIndependent_iff_card_eq_finrank_span

theorem linearIndependent_iff_card_le_finrank_span {ι : Type*} [Fintype ι] {b : ι → V} :
    LinearIndependent K b ↔ Fintype.card ι ≤ (Set.range b).finrank K := by
  rw [linearIndependent_iff_card_eq_finrank_span, (finrank_range_le_card _).le_iff_eq]
#align linear_independent_iff_card_le_finrank_span linearIndependent_iff_card_le_finrank_span

/-- A family of `finrank K V` vectors forms a basis if they span the whole space. -/
noncomputable def basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → V)
    (le_span : ⊤ ≤ span K (Set.range b)) (card_eq : Fintype.card ι = finrank K V) : Basis ι K V :=
  Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span
#align basis_of_top_le_span_of_card_eq_finrank basisOfTopLeSpanOfCardEqFinrank

@[simp]
theorem coe_basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → V)
    (le_span : ⊤ ≤ span K (Set.range b)) (card_eq : Fintype.card ι = finrank K V) :
    ⇑(basisOfTopLeSpanOfCardEqFinrank b le_span card_eq) = b :=
  Basis.coe_mk _ _
#align coe_basis_of_top_le_span_of_card_eq_finrank coe_basisOfTopLeSpanOfCardEqFinrank

/-- A finset of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps! repr_apply]
noncomputable def finsetBasisOfTopLeSpanOfCardEqFinrank {s : Finset V}
    (le_span : ⊤ ≤ span K (s : Set V)) (card_eq : s.card = finrank K V) : Basis {x // x ∈ s} K V :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : ↥(s : Set V) → V)
    ((@Subtype.range_coe_subtype _ fun x => x ∈ s).symm ▸ le_span)
    (_root_.trans (Fintype.card_coe _) card_eq)
#align finset_basis_of_top_le_span_of_card_eq_finrank finsetBasisOfTopLeSpanOfCardEqFinrank

/-- A set of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps! repr_apply]
noncomputable def setBasisOfTopLeSpanOfCardEqFinrank {s : Set V} [Fintype s]
    (le_span : ⊤ ≤ span K s) (card_eq : s.toFinset.card = finrank K V) : Basis s K V :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : s → V) ((@Subtype.range_coe_subtype _ s).symm ▸ le_span)
    (_root_.trans s.toFinset_card.symm card_eq)
#align set_basis_of_top_le_span_of_card_eq_finrank setBasisOfTopLeSpanOfCardEqFinrank

end Basis

section Cardinal

variable (K)
variable [DivisionRing K]

/-- Key lemma towards the Erdős-Kaplansky theorem from https://mathoverflow.net/a/168624 -/
theorem max_aleph0_card_le_rank_fun_nat : max ℵ₀ #K ≤ Module.rank K (ℕ → K) := by
  have aleph0_le : ℵ₀ ≤ Module.rank K (ℕ → K) := (rank_finsupp_self K ℕ).symm.trans_le
    (Finsupp.lcoeFun.rank_le_of_injective <| by exact DFunLike.coe_injective)
  refine max_le aleph0_le ?_
  obtain card_K | card_K := le_or_lt #K ℵ₀
  · exact card_K.trans aleph0_le
  by_contra!
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := ℕ → K)
  let L := Subfield.closure (Set.range (fun i : ιK × ℕ ↦ bK i.1 i.2))
  have hLK : #L < #K := by
    refine (Subfield.cardinal_mk_closure_le_max _).trans_lt
      (max_lt_iff.mpr ⟨mk_range_le.trans_lt ?_, card_K⟩)
    rwa [mk_prod, ← aleph0, lift_uzero, bK.mk_eq_rank'', mul_aleph0_eq aleph0_le]
  letI := Module.compHom K (RingHom.op L.subtype)
  obtain ⟨⟨ιL, bL⟩⟩ := Module.Free.exists_basis (R := Lᵐᵒᵖ) (M := K)
  have card_ιL : ℵ₀ ≤ #ιL := by
    contrapose! hLK
    haveI := @Fintype.ofFinite _ (lt_aleph0_iff_finite.mp hLK)
    rw [bL.repr.toEquiv.cardinal_eq, mk_finsupp_of_fintype,
        ← MulOpposite.opEquiv.cardinal_eq] at card_K ⊢
    apply power_nat_le
    contrapose! card_K
    exact (power_lt_aleph0 card_K <| nat_lt_aleph0 _).le
  obtain ⟨e⟩ := lift_mk_le'.mp (card_ιL.trans_eq (lift_uzero #ιL).symm)
  have rep_e := bK.total_repr (bL ∘ e)
  rw [Finsupp.total_apply, Finsupp.sum] at rep_e
  set c := bK.repr (bL ∘ e)
  set s := c.support
  let f i (j : s) : L := ⟨bK j i, Subfield.subset_closure ⟨(j, i), rfl⟩⟩
  have : ¬LinearIndependent Lᵐᵒᵖ f := fun h ↦ by
    have := h.cardinal_lift_le_rank
    rw [lift_uzero, (LinearEquiv.piCongrRight fun _ ↦ MulOpposite.opLinearEquiv Lᵐᵒᵖ).rank_eq,
        rank_fun'] at this
    exact (nat_lt_aleph0 _).not_le this
  obtain ⟨t, g, eq0, i, hi, hgi⟩ := not_linearIndependent_iff.mp this
  refine hgi (linearIndependent_iff'.mp (bL.linearIndependent.comp e e.injective) t g ?_ i hi)
  clear_value c s
  simp_rw [← rep_e, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  replace eq0 := congr_arg L.subtype (congr_fun eq0 ⟨i, hi⟩)
  rw [Finset.sum_apply, map_sum] at eq0
  have : SMulCommClass Lᵐᵒᵖ K K := ⟨fun _ _ _ ↦ mul_assoc _ _ _⟩
  simp_rw [smul_comm _ (c i), ← Finset.smul_sum]
  erw [eq0, smul_zero]

variable {K}

open Function in
theorem rank_fun_infinite {ι : Type v} [hι : Infinite ι] : Module.rank K (ι → K) = #(ι → K) := by
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := ι → K)
  obtain ⟨e⟩ := lift_mk_le'.mp ((aleph0_le_mk_iff.mpr hι).trans_eq (lift_uzero #ι).symm)
  have := LinearMap.lift_rank_le_of_injective _ <|
    LinearMap.funLeft_injective_of_surjective K K _ (invFun_surjective e.injective)
  rw [lift_umax.{u,v}, lift_id'.{u,v}] at this
  have key := (lift_le.{v}.mpr <| max_aleph0_card_le_rank_fun_nat K).trans this
  rw [lift_max, lift_aleph0, max_le_iff] at key
  haveI : Infinite ιK := by
    rw [← aleph0_le_mk_iff, bK.mk_eq_rank'']; exact key.1
  rw [bK.repr.toEquiv.cardinal_eq, mk_finsupp_lift_of_infinite,
      lift_umax.{u,v}, lift_id'.{u,v}, bK.mk_eq_rank'', eq_comm, max_eq_left]
  exact key.2

/-- The **Erdős-Kaplansky Theorem**: the dual of an infinite-dimensional vector space
  over a division ring has dimension equal to its cardinality. -/
theorem rank_dual_eq_card_dual_of_aleph0_le_rank' {V : Type*} [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) : Module.rank Kᵐᵒᵖ (V →ₗ[K] K) = #(V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'', aleph0_le_mk_iff] at h
  have e := (b.constr Kᵐᵒᵖ (M' := K)).symm.trans
    (LinearEquiv.piCongrRight fun _ ↦ MulOpposite.opLinearEquiv Kᵐᵒᵖ)
  rw [e.rank_eq, e.toEquiv.cardinal_eq]
  apply rank_fun_infinite

/-- The **Erdős-Kaplansky Theorem** over a field. -/
theorem rank_dual_eq_card_dual_of_aleph0_le_rank {K V} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) : Module.rank K (V →ₗ[K] K) = #(V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'', aleph0_le_mk_iff] at h
  have e := (b.constr K (M' := K)).symm
  rw [e.rank_eq, e.toEquiv.cardinal_eq]
  apply rank_fun_infinite

theorem lift_rank_lt_rank_dual' {V : Type v} [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) :
    Cardinal.lift.{u} (Module.rank K V) < Module.rank Kᵐᵒᵖ (V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'', rank_dual_eq_card_dual_of_aleph0_le_rank' h,
      ← (b.constr ℕ (M' := K)).toEquiv.cardinal_eq, mk_arrow]
  apply cantor'
  erw [nat_lt_lift_iff, one_lt_iff_nontrivial]
  infer_instance

theorem lift_rank_lt_rank_dual {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) :
    Cardinal.lift.{u} (Module.rank K V) < Module.rank K (V →ₗ[K] K) := by
  rw [rank_dual_eq_card_dual_of_aleph0_le_rank h, ← rank_dual_eq_card_dual_of_aleph0_le_rank' h]
  exact lift_rank_lt_rank_dual' h

theorem rank_lt_rank_dual' {V : Type u} [AddCommGroup V] [Module K V] (h : ℵ₀ ≤ Module.rank K V) :
    Module.rank K V < Module.rank Kᵐᵒᵖ (V →ₗ[K] K) := by
  convert lift_rank_lt_rank_dual' h; rw [lift_id]

theorem rank_lt_rank_dual {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) : Module.rank K V < Module.rank K (V →ₗ[K] K) := by
  convert lift_rank_lt_rank_dual h; rw [lift_id]

end Cardinal
