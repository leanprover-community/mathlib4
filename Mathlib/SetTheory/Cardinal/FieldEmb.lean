/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.FieldTheory.MvPolynomial
import Mathlib.FieldTheory.SeparableDegree

/-!

# Number of field embeddings of an infinite extension into the algebraic closure

We show that if `E/F` is an infinite-dimensional separable algebraic extension, then
`#(Field.Emb F E) = 2 ^ Module.rank F E`

This is in contrast to the finite-dimensional case, where `#Field.Emb F E = Module.rank F E`
without the power of two (see `Field.finSepDegree_eq_finrank_of_isSeparable`.)

-/

open Cardinal Module.Free Set Order

universe u v

noncomputable section

section InverseLimit

/-! In this section we compute the cardinality of the cardinality of each node in an inverse
  system indexed by a well-ordered type where the maps between consecutive nodes are surjective
  with equipotent fibers, and the node at a limit ordinal is the inverse limit of the inverse
  subsystem formed by smaller ordinals. -/

theorem Cardinal.noMaxOrder {c} (hc : ℵ₀ ≤ c) : NoMaxOrder c.ord.out.α :=
  Ordinal.out_no_max_of_succ_lt (ord_isLimit hc).2

variable {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]

open scoped Classical in
/-- A well-order is a SuccOrder. -/
def SuccOrder.ofWellOrder : SuccOrder ι :=
  SuccOrder.ofCore (fun i ↦ if h : {k | i < k}.Nonempty then wellFounded_lt.min _ h else i)
    (fun hi _ ↦ by
      rw [not_isMax_iff] at hi
      simp_rw [Set.Nonempty, mem_setOf, dif_pos hi]
      exact ⟨(wellFounded_lt.min_le · hi), lt_of_lt_of_le (wellFounded_lt.min_mem _ hi)⟩)
    fun i hi ↦ dif_neg (not_not_intro hi <| not_isMax_iff.mpr ·)
-- OrderBot .. from Nonempty

attribute [local instance] SuccOrder.ofWellOrder

open scoped Classical in
/-- Recursion principle on a well-order. -/
@[elab_as_elim]
def SuccOrder.limitRecOn {C : ι → Sort*} (i : ι)
    (H_succ : ∀ i, ¬IsMax i → C i → C (succ i))
    (H_lim : ∀ i, IsSuccLimit i → (∀ j < i, C j) → C i) : C i :=
  wellFounded_lt.fix
    (fun i IH ↦ if h : IsSuccLimit i then H_lim i h IH else
      let x := Classical.indefiniteDescription _ (not_isSuccLimit_iff.mp h)
      x.2.2 ▸ H_succ x x.2.1 (IH x <| x.2.2.subst <| lt_succ_of_not_isMax x.2.1))
    i

variable {G X : ι → Type*} {i : ι} (equiv : ∀ j : {j // j ≤ i}, (G j ≃ ∀ l : {l // l < j.1}, X l))

/-- Projection from a Pi type to the Pi type over an initial segment of its indexing type. -/
private abbrev proj ⦃i j : ι⦄ (h : i ≤ j) (f : ∀ l : {l // l < j}, X l) : ∀ l : {l // l < i}, X l :=
  fun l ↦ f ⟨l, l.2.trans_le h⟩

class InverseSystem {ι} [Preorder ι] (G : ι → Type*) (f : ∀ ⦃i j⦄, i ≤ j → G j → G i) : Prop where
  map_self ⦃i⦄ (x : G i) : f (le_refl i) x = x
  map_map ⦃k j i⦄ (hkj : k ≤ j) (hji : j ≤ i) (x : G i) : f hkj (f hji x) = f (hkj.trans hji) x

variable (f : ∀ ⦃i j : ι⦄, i ≤ j → G j → G i)

/-- The predicate that says a family of equivalences between `G j` and `∀ l < j, X l`
  is a natural transformation. -/
private def IsNatEquiv : Prop := ∀ ⦃j k⦄ (hj : j ≤ i) (hk : k ≤ j) (x : G j),
  equiv ⟨k, hk.trans hj⟩ (f hk x) = proj hk (equiv ⟨j, hj⟩ x)

private def piSplitLE : (∀ j : {j // j < i}, X j) × X i ≃ ∀ j : {j // j ≤ i}, X j where
  toFun f j := if h : j = i then h.symm ▸ f.2 else f.1 ⟨j, j.2.lt_of_ne h⟩
  invFun f := (fun j ↦ f ⟨j, j.2.le⟩, f ⟨i, le_rfl⟩)
  left_inv f := by ext j; exacts [dif_neg j.2.ne, dif_pos rfl]
  right_inv f := by
    ext j; dsimp only; split_ifs with h
    · cases (Subtype.ext h : j = ⟨i, le_rfl⟩); rfl
    · rfl

@[simp] theorem piSplitLE_eq {f : (∀ j : {j // j < i}, X j) × X i} :
    piSplitLE f ⟨i, le_rfl⟩ = f.2 := by simp [piSplitLE]

theorem piSplitLE_lt {f : (∀ j : {j // j < i}, X j) × X i} {j} (hj : j < i) :
    piSplitLE f ⟨j, hj.le⟩ = f.1 ⟨j, hj⟩ := dif_neg hj.ne

@[simps!] def Equiv.piCongrSet {β : ι → Type*} {p q : ι → Prop} (h : p = q) :
    (∀ i : {i // p i}, β i) ≃ (∀ i : {i // q i}, β i) where
  toFun f i := f ⟨i, h ▸ i.2⟩
  invFun f i := f ⟨i, h.symm ▸ i.2⟩
  left_inv f := rfl
  right_inv f := rfl

section Succ

variable (nat : IsNatEquiv equiv f) (e : G (succ i) ≃ G i × X i) (hi : ¬ IsMax i)

def piEquivSucc : ∀ j : {j // j ≤ succ i}, (G j ≃ ∀ l : {l // l < j.1}, X l) :=
  piSplitLE (X := fun i ↦ G i ≃ ∀ l : {l // l < i}, X l)
  (fun j ↦ equiv ⟨j, (lt_succ_iff_of_not_isMax hi).mp j.2⟩,
    e.trans <| ((equiv ⟨i, le_rfl⟩).prodCongr <| Equiv.refl _).trans <| piSplitLE.trans <|
      Equiv.piCongrSet <| funext fun _ ↦ propext <| (lt_succ_iff_of_not_isMax hi).symm)

theorem isNatEquiv_piEquivSucc [InverseSystem G f] (h : ∀ x, (e x).1 = f (le_succ i) x) :
    IsNatEquiv (piEquivSucc equiv e hi) f := fun j k hj hk x ↦ by
  have lt_succ {j} := (lt_succ_iff_of_not_isMax (b := j) hi).mpr
  obtain rfl | hj := le_succ_iff_eq_or_le.mp hj
  · ext l; obtain rfl | hk := le_succ_iff_eq_or_le.mp hk
    · simp [InverseSystem.map_self]
    · rw [piEquivSucc, piSplitLE_lt (lt_succ hk),
        ← InverseSystem.map_map (f := f) hk (le_succ i), ← h, proj, nat le_rfl]
      simp [piSplitLE_lt (l.2.trans_le hk)]
  · rw [piEquivSucc, piSplitLE_lt (hk.trans_lt <| lt_succ hj), nat hj, piSplitLE_lt (lt_succ hj)]

end Succ

section Lim

-- WithTop still SuccOrder ..

-- def piEquivSucc_spec :

-- Equiv.sigmaEquivProdOfEquiv



--def piEquivLim :


end Lim

end InverseLimit

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

set_option quotPrecheck false

/-- Index a basis of E/F using the initial ordinal of `Module.rank F E`. -/
local notation "ι" => (Module.rank F E).ord.out.α

variable {F E} in
private lemma wf : WellFounded ((· : ι) < ·) := (Module.rank F E).ord.out.wo.wf
private lemma card_ι : #ι = Module.rank F E := (mk_ordinal_out _).trans (card_ord _)

/-- A basis of E/F indexed by the initial ordinal. -/
private def wellOrderedBasis : Basis ι F E :=
  (chooseBasis F E).reindex
    (Cardinal.eq.mp <| (card_ι F E).trans <| rank_eq_card_chooseBasisIndex F E).some.symm

local notation "b" => wellOrderedBasis F E

variable {F E}

-- StrongRankCondition on F should be enough, and E can be any CommSemiring
theorem Algebra.rank_adjoin_le (s : Set E) : Module.rank F (adjoin F s) ≤ max #s ℵ₀ := by
  rw [adjoin_eq_range]
  change Module.rank F (LinearMap.range (MvPolynomial.aeval Subtype.val).toLinearMap) ≤ _
  rw [← lift_le.{max u v}]
  refine (lift_rank_range_le _).trans ?_
  rw [MvPolynomial.rank_eq, lift_id'.{v,u}, lift_umax.{v,u}, lift_le]
  cases isEmpty_or_nonempty s
  · exact (le_one_iff_subsingleton.mpr inferInstance).trans (le_max_of_le_right one_le_aleph0)
  · exact (mk_finsupp_nat _).le

-- or call it `mk_lt_ord_out_α`? The `le` version also hold for `c` infinite.
theorem Cardinal.mk_initialSeg {c : Cardinal} (i : c.ord.out.α) : #{j // j < i} < c :=
  card_typein_out_lt c i

private theorem adjoin_range_b_eq_top : Algebra.adjoin F (range b) = ⊤ :=
  Subalgebra.toSubmodule_injective <| top_unique <|
    (Basis.span_eq b).ge.trans <| Algebra.span_le_adjoin F _

variable (rank_inf : ℵ₀ ≤ Module.rank F E) (alg : Algebra.IsAlgebraic F E)

/-- `leastExt i` is defined to be the smallest `k : ι` that generates a nontrival extension over
(i.e. does not lie in) the subalgebra (= intermediate field) generated by all previous
`leastExt j`, `j < i`. For cardinality reasons, such `k` always exist if `ι` is infinite. -/
private def leastExt_aux (i : ι) (ih : ∀ j < i, ι) : ι :=
  wf.min {k | b k ∉ Algebra.adjoin F (range fun j : {j // j < i} ↦ b (ih j j.2))} <| by
    rw [← compl_setOf, nonempty_compl]; by_contra!
    simp_rw [eq_univ_iff_forall, mem_setOf] at this
    have := Algebra.adjoin_le (range_subset_iff.mpr this)
    rw [adjoin_range_b_eq_top, ← eq_top_iff] at this
    apply_fun Module.rank F at this
    refine ne_of_lt ?_ this
    conv_rhs => rw [Subalgebra.rank_top]
    have := mk_initialSeg i
    obtain eq | lt := rank_inf.eq_or_lt
    · replace this := mk_lt_aleph0_iff.mp (this.trans_eq eq.symm)
      have : FiniteDimensional F (Algebra.adjoin F <| range fun j : {j // j < i} ↦ b (ih j j.2)) :=
        Module.Finite.iff_fg.2 (fg_adjoin_of_finite (finite_range _) fun _ _ ↦ (alg _).isIntegral)
      exact (FiniteDimensional.rank_lt_aleph0 _ _).trans_eq eq
    · exact (Algebra.rank_adjoin_le _).trans_lt (max_lt (mk_range_le.trans_lt this) lt)

private noncomputable def leastExt : ι → ι := wf.fix (leastExt_aux rank_inf alg)
local notation "φ" => leastExt rank_inf alg

local notation F"⟮"i"⟯" => Algebra.adjoin F (b ∘ φ '' {j | j < i})

private theorem isLeast_φ' (i : ι) :
    IsLeast {k | b k ∉ Algebra.adjoin F (range fun j : {j // j < i} ↦ b (φ j))} (φ i) := by
  rw [leastExt, wf.fix_eq]; exact ⟨wf.min_mem _ _, fun _ ↦ (wf.min_le ·)⟩

private theorem isLeast_φ (i : ι) : IsLeast {k | b k ∉ F⟮i⟯} (φ i) := by
  rw [image_eq_range]; exact isLeast_φ' rank_inf alg i

private theorem strictMono_φ : StrictMono φ := fun i j h ↦ by
  have least := isLeast_φ rank_inf alg
  by_contra!
  obtain eq | lt := this.eq_or_lt
  · exact (least j).1 (Algebra.subset_adjoin ⟨i, h, congr_arg b eq.symm⟩)
  · refine ((least i).2 <| mt (Algebra.adjoin_mono (image_mono ?_) ·) (least j).1).not_lt lt
    exact fun k (hk : k < i) ↦ hk.trans h

open Algebra in
private theorem adjoin_image_φ (i : ι) : F⟮i⟯ = adjoin F (b '' {j | j < φ i}) := by
  refine le_antisymm (adjoin_mono ?_) (adjoin_le ?_)
  · rw [image_comp]; apply image_mono; rintro _ ⟨j, hj, rfl⟩; exact strictMono_φ rank_inf alg hj
  · rintro _ ⟨j, hj, rfl⟩; contrapose! hj; exact ((isLeast_φ rank_inf alg i).2 hj).not_lt

attribute [local instance] SuccOrder.ofWellOrder in
private theorem iSup_adjoin_eq_top : ⨆ i : ι, F⟮i⟯ = ⊤ := by
  simp_rw [adjoin_image_φ, eq_top_iff, ← adjoin_range_b_eq_top, Algebra.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  refine le_iSup (α := Subalgebra F E) _ (succ i) (Algebra.subset_adjoin ⟨i, ?_, rfl⟩)
  have := noMaxOrder rank_inf
  exact (lt_succ i).trans_le (wf.self_le_of_strictMono (strictMono_φ rank_inf alg) _)

local notation "Ē" => AlgebraicClosure E
local notation "deg" i => (minpoly (F⟮i⟯) (b (φ i))).natDegree

namespace IsIntegral

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Nontrivial A] {x : A}

open Polynomial in
theorem degree_minpoly_eq_one_iff : (minpoly R x).degree = 1 ↔ x ∈ (algebraMap R A).range := by
  refine ⟨minpoly.mem_range_of_degree_eq_one _ _, ?_⟩
  rintro ⟨x, rfl⟩
  haveI := Module.nontrivial R A
  exact (degree_X_sub_C x ▸ minpoly.min R (algebraMap R A x) (monic_X_sub_C x) (by simp)).antisymm
    (Nat.WithBot.add_one_le_of_lt <| minpoly.degree_pos isIntegral_algebraMap)

theorem natDegree_minpoly_eq_one_iff :
    (minpoly R x).natDegree = 1 ↔ x ∈ (algebraMap R A).range := by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos zero_lt_one]
  exact degree_minpoly_eq_one_iff

theorem two_le_natDegree_minpoly (int : IsIntegral R x) :
    2 ≤ (minpoly R x).natDegree ↔ x ∉ (algebraMap R A).range := by
  rw [iff_not_comm, ← natDegree_minpoly_eq_one_iff, not_le]
  exact ⟨fun h ↦ h.trans_lt one_lt_two, fun h ↦ by linarith only [minpoly.natDegree_pos int, h]⟩

theorem two_le_natDegree_minpoly_subalgebra {A} [CommRing A] [Algebra R A] [Nontrivial A]
    {S : Subalgebra R A} {x : A} (int : IsIntegral S x) : 2 ≤ (minpoly S x).natDegree ↔ x ∉ S := by
  rw [two_le_natDegree_minpoly int, Iff.not]
  apply Set.ext_iff.mp Subtype.range_val_subtype

end IsIntegral

theorem two_le_deg (i : ι) : 2 ≤ deg i :=
  (alg _).isIntegral.tower_top.two_le_natDegree_minpoly_subalgebra.mpr (isLeast_φ _ _ i).1

open Ordinal in
def succEquiv (i : ι) : (F⟮succ i⟯ →ₐ[F] Ē) ≃ (F⟮i⟯ →ₐ[F] Ē) × Fin (deg i) := by



-- Ordinal.typein.principalSeg
-- enum ..
-- Ordinal.limitRecOn

theorem Field.cardinal_emb_of_aleph0_le_rank_of_isSeparable [IsSeparable F E]
    (rank_inf : ℵ₀ ≤ Module.rank F E) : #(Field.Emb F E) = 2 ^ Module.rank F E := by
