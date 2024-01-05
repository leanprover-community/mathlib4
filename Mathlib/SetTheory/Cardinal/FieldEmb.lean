/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.FieldTheory.MvPolynomial
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.Data.Set.Intervals.WithBotTop

/-!

# Number of field embeddings of an infinite extension into the algebraic closure

We show that if `E/F` is an infinite-dimensional separable algebraic extension, then
`#(Field.Emb F E) = 2 ^ Module.rank F E`

This is in contrast to the finite-dimensional case, where `#Field.Emb F E = Module.rank F E`
without the power of two (see `Field.finSepDegree_eq_finrank_of_isSeparable`.)

-/

open Cardinal Module.Free Set Order IntermediateField

universe u v

noncomputable section

local notation i"⁺" => succ i

section InverseLimit

/-! In this section we compute the cardinality of the cardinality of each node in an inverse
  system indexed by a well-ordered type where the maps between consecutive nodes are surjective
  with equipotent fibers, and the node at a limit ordinal is the inverse limit of the inverse
  subsystem formed by smaller ordinals. -/

theorem Cardinal.noMaxOrder {c} [Fact (ℵ₀ ≤ c)] : NoMaxOrder c.ord.out.α :=
  Ordinal.out_no_max_of_succ_lt (ord_isLimit Fact.out).2

variable {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]

open scoped Classical in
/-- A well-order is a SuccOrder. -/
def SuccOrder.ofWellOrder : SuccOrder ι :=
  SuccOrder.ofCore (fun i ↦ if h : (Ioi i).Nonempty then wellFounded_lt.min _ h else i)
    (fun hi _ ↦ by
      rw [not_isMax_iff] at hi
      simp_rw [Set.Nonempty, mem_Ioi, dif_pos hi]
      exact ⟨(wellFounded_lt.min_le · hi), lt_of_lt_of_le (wellFounded_lt.min_mem _ hi)⟩)
    fun i hi ↦ dif_neg (not_not_intro hi <| not_isMax_iff.mpr ·)
-- OrderBot .. from Nonempty

open scoped Classical in
/-- Recursion principle on a well-founded partial SuccOrder. -/
@[elab_as_elim]
def SuccOrder.limitRecOn {ι} [PartialOrder ι] [WellFoundedLT ι] [SuccOrder ι]
    {C : ι → Sort*} (i : ι)
    (H_succ : ∀ i, ¬IsMax i → C i → C (i⁺))
    (H_lim : ∀ i, IsSuccLimit i → (∀ j < i, C j) → C i) : C i :=
  wellFounded_lt.fix
    (fun i IH ↦ if h : IsSuccLimit i then H_lim i h IH else
      let x := Classical.indefiniteDescription _ (not_isSuccLimit_iff.mp h)
      x.2.2 ▸ H_succ x x.2.1 (IH x <| x.2.2.subst <| lt_succ_of_not_isMax x.2.1))
    i

section proj

variable {ι : Type*} [Preorder ι] {F X : ι → Type*} {i j : ι} (h : i ≤ j)
  (f : ∀ ⦃i j : ι⦄, i ≤ j → F j → F i)

class InverseSystem : Prop where
  map_self ⦃i⦄ (x : F i) : f (le_refl i) x = x
  map_map ⦃k j i⦄ (hkj : k ≤ j) (hji : j ≤ i) (x : F i) : f hkj (f hji x) = f (hkj.trans hji) x

private def inverseLimit (i : ι) : Set (∀ l : Iio i, F l) :=
  {F | ∀ ⦃j k⦄ (h : j.1 ≤ k.1), f h (F k) = F j}

abbrev piLT [LT ι] (X : ι → Type*) (i : ι) := ∀ l : Iio i, X l

/-- Projection from a Pi type to the Pi type over an initial segment of its indexing type. -/
abbrev piLTProj (f : piLT X j) : piLT X i := fun l ↦ f ⟨l, l.2.trans_le h⟩

theorem piLTProj_intro {l : Iio j} {f : piLT X j} (hl : l < i) :
    f l = piLTProj h f ⟨l, hl⟩ := rfl

/-- The predicate that says a family of equivalences between `F j` and `piLT X j`
  is a natural transformation. -/
private def IsNatEquiv {s : Set ι} (equiv : ∀ j : s, F j ≃ piLT X j) : Prop :=
  ∀ ⦃j k⦄ (hj : j ∈ s) (hk : k ∈ s) (h : k ≤ j) (x : F j),
    equiv ⟨k, hk⟩ (f h x) = piLTProj h (equiv ⟨j, hj⟩ x)

abbrev Order.IsSuccLimit.mid {ι} [LT ι] {i j : ι} (hi : IsSuccLimit i) (hj : j < i) :
    {k // j < k ∧ k < i} := Classical.indefiniteDescription _ ((not_covby_iff hj).mp <| hi j)

variable {ι : Type*} [LinearOrder ι] {X : ι → Type*} {i : ι} (hi : IsSuccLimit i)

@[simps apply] def piLTLim : piLT X i ≃ inverseLimit (@piLTProj _ _ X) i where
  toFun f := ⟨fun j ↦ piLTProj j.2.le f, fun _ _ _ ↦ rfl⟩
  invFun f l := let k := hi.mid l.2; f.1 ⟨k, k.2.2⟩ ⟨l, k.2.1⟩
  left_inv f := rfl
  right_inv f := by
    ext j; funext l
    set k := hi.mid (l.2.trans j.2)
    obtain le | le := le_total j ⟨k, k.2.2⟩
    exacts [congr_fun (f.2 le) l, (congr_fun (f.2 le) ⟨l, _⟩).symm]

theorem piLTLim_symm_apply {f} (k : Iio i) {l : Iio i} (hl : l.1 < k.1) :
    (piLTLim (X := X) hi).symm f l = f.1 k ⟨l, hl⟩ := by conv_rhs => rw [← (piLTLim hi).right_inv f]

end proj

variable {F X : ι → Type*} {i : ι}

-- PartialOrder + DecidableEq is enough
private def piSplitLE : piLT X i × X i ≃ ∀ j : Iic i, X j where
  toFun f j := if h : j = i then h.symm ▸ f.2 else f.1 ⟨j, j.2.lt_of_ne h⟩
  invFun f := (fun j ↦ f ⟨j, j.2.le⟩, f ⟨i, le_rfl⟩)
  left_inv f := by ext; exacts [funext fun j ↦ dif_neg j.2.ne, dif_pos rfl]
  right_inv f := by
    ext j; dsimp only; split_ifs with h
    · cases (Subtype.ext h : j = ⟨i, le_rfl⟩); rfl
    · rfl

@[simp] theorem piSplitLE_eq {f : piLT X i × X i} :
    piSplitLE f ⟨i, le_rfl⟩ = f.2 := by simp [piSplitLE]

theorem piSplitLE_lt {f : piLT X i × X i} {j} (hj : j < i) :
    piSplitLE f ⟨j, hj.le⟩ = f.1 ⟨j, hj⟩ := dif_neg hj.ne

@[simps!] def Equiv.piCongrSet {β : ι → Type*} {s t : Set ι} (h : s = t) :
    (∀ i : s, β i) ≃ (∀ i : t, β i) where
  toFun f i := f ⟨i, h ▸ i.2⟩
  invFun f i := f ⟨i, h.symm ▸ i.2⟩
  left_inv f := rfl
  right_inv f := rfl

variable {f : ∀ ⦃i j : ι⦄, i ≤ j → F j → F i}

section Succ

variable [SuccOrder ι]
  (equiv : ∀ j : Iic i, F j ≃ piLT X j) (e : F (i⁺) ≃ F i × X i) (hi : ¬ IsMax i)

def piEquivSucc : ∀ j : Iic (i⁺), F j ≃ piLT X j :=
  piSplitLE (X := fun i ↦ F i ≃ piLT X i)
  (fun j ↦ equiv ⟨j, (lt_succ_iff_of_not_isMax hi).mp j.2⟩,
    e.trans <| ((equiv ⟨i, le_rfl⟩).prodCongr <| Equiv.refl _).trans <| piSplitLE.trans <|
      Equiv.piCongrSet <| Set.ext fun _ ↦ (lt_succ_iff_of_not_isMax hi).symm)

theorem piEquivSucc_self {x} :
    piEquivSucc equiv e hi ⟨_, le_rfl⟩ x ⟨i, lt_succ_of_not_isMax hi⟩ = (e x).2 := by
  simp [piEquivSucc]

variable {equiv e}
theorem isNatEquiv_piEquivSucc [InverseSystem f] (H : ∀ x, (e x).1 = f (le_succ i) x)
    (nat : IsNatEquiv f equiv) : IsNatEquiv f (piEquivSucc equiv e hi) := fun j k hj hk h x ↦ by
  have lt_succ {j} := (lt_succ_iff_of_not_isMax (b := j) hi).mpr
  obtain rfl | hj := le_succ_iff_eq_or_le.mp hj
  · obtain rfl | hk := le_succ_iff_eq_or_le.mp hk
    · simp [InverseSystem.map_self]
    · funext l
      rw [piEquivSucc, piSplitLE_lt (lt_succ hk),
        ← InverseSystem.map_map (f := f) hk (le_succ i), ← H, piLTProj, nat le_rfl]
      simp [piSplitLE_lt (l.2.trans_le hk)]
  · rw [piEquivSucc, piSplitLE_lt (h.trans_lt <| lt_succ hj), nat hj, piSplitLE_lt (lt_succ hj)]

end Succ

section Lim

variable {equiv : ∀ j : Iio i, F j ≃ piLT X j} (nat : IsNatEquiv f equiv)

@[simps] def invLimEquiv : inverseLimit f i ≃ inverseLimit (@piLTProj _ _ X) i where
  toFun t := ⟨fun l ↦ equiv l (t.1 l), fun _ _ h ↦ Eq.symm <| by simp_rw [← t.2 h]; apply nat⟩
  invFun t := ⟨fun l ↦ (equiv l).symm (t.1 l),
    fun _ _ h ↦ (Equiv.eq_symm_apply _).mpr <| by rw [nat, ← t.2 h]; simp⟩
  left_inv t := by ext; apply Equiv.left_inv
  right_inv t := by ext; apply Equiv.right_inv

variable (equivLim : F i ≃ inverseLimit f i) (hi : IsSuccLimit i)

def piEquivLim : ∀ j : Iic i, F j ≃ piLT X j :=
  piSplitLE (X := fun j ↦ F j ≃ piLT X j)
    (equiv, equivLim.trans <| (invLimEquiv nat).trans (piLTLim hi).symm)

variable {equivLim}
theorem isNatEquiv_piEquivLim [InverseSystem f] (H : ∀ x l, (equivLim x).1 l = f l.2.le x) :
    IsNatEquiv f (piEquivLim nat equivLim hi) := fun j k hj hk h t ↦ by
  obtain rfl | hj := hj.eq_or_lt
  · obtain rfl | hk := hk.eq_or_lt
    · simp [InverseSystem.map_self]
    · funext l
      simp_rw [piEquivLim, piSplitLE_lt hk, piSplitLE_eq, Equiv.trans_apply]
      rw [piLTProj, piLTLim_symm_apply hi ⟨k, hk⟩ (by exact l.2), invLimEquiv_apply_coe, H]
  · rw [piEquivLim, piSplitLE_lt (h.trans_lt hj), piSplitLE_lt hj]; apply nat

end Lim

section Unique

variable [SuccOrder ι] (f) (equivSucc : ∀ ⦃i⦄, ¬IsMax i → F (i⁺) ≃ F i × X i)

@[ext] structure PEquivOn (s : Set ι) where
  /-- A partial family of equivalences between `F` and `piLT X` defined on some set in `ι`. -/
  equiv : ∀ i : s, F i ≃ piLT X i
  /-- It is a natural family of equivalences. -/
  nat : IsNatEquiv f equiv
  /-- It is compatible with a family of equivalences relating `F i⁺` to `F i`. -/
  compat : ∀ {i} (hsi : i⁺ ∈ s) (hi : ¬IsMax i) (x),
    equiv ⟨i⁺, hsi⟩ x ⟨i, lt_succ_of_not_isMax hi⟩ = (equivSucc hi x).2

variable {s t : Set ι}

@[simps] def PEquivOn.restrict (e : PEquivOn f equivSucc t) (h : s ⊆ t) :
    PEquivOn f equivSucc s where
  equiv i := e.equiv ⟨i, h i.2⟩
  nat _ _ _ _ := e.nat _ _
  compat _ := e.compat _

variable {f equivSucc}
theorem unique_pEquivOn (hs : IsLowerSet s) {e₁ e₂ : PEquivOn f equivSucc s} : e₁ = e₂ := by
  obtain ⟨e₁, nat₁, compat₁⟩ := e₁
  obtain ⟨e₂, nat₂, compat₂⟩ := e₂
  ext1; ext1 i; dsimp only
  refine SuccOrder.limitRecOn (C := fun i ↦ ∀ h : i ∈ s, e₁ ⟨i, h⟩ = e₂ ⟨i, h⟩) i
    (fun i nmax ih hi ↦ ?_) (fun i lim ih hi ↦ ?_) i.2
  · ext x; funext ⟨j, hj⟩
    obtain rfl | hj := ((lt_succ_iff_of_not_isMax nmax).mp hj).eq_or_lt
    · exact (compat₁ _ nmax x).trans (compat₂ _ nmax x).symm
    have hi : i ∈ s := hs (le_succ i) hi
    rw [piLTProj_intro (f := e₁ _ x) (le_succ i) (by exact hj),
        ← nat₁ _ hi (by exact le_succ i), ih, nat₂ _ hi (by exact le_succ i)]
  · ext x; funext j
    have ⟨k, hjk, hki⟩ := lim.mid j.2
    have hk : k ∈ s := hs hki.le hi
    rw [piLTProj_intro (f := e₁ _ x) hki.le hjk, piLTProj_intro (f := e₂ _ x) hki.le hjk,
      ← nat₁ _ hk, ← nat₂ _ hk, ih _ hki]

theorem pEquivOn_apply_eq (h : IsLowerSet (s ∩ t))
    {e₁ : PEquivOn f equivSucc s} {e₂ : PEquivOn f equivSucc t} {i} {his : i ∈ s} {hit : i ∈ t} :
    e₁.equiv ⟨i, his⟩ = e₂.equiv ⟨i, hit⟩ :=
  show (e₁.restrict <| inter_subset_left s t).equiv ⟨i, his, hit⟩ =
       (e₂.restrict <| inter_subset_right s t).equiv ⟨i, his, hit⟩ from
  congr_fun (congr_arg _ <| unique_pEquivOn h) _

def pEquivOnSucc [InverseSystem f] (hi : ¬IsMax i) (e : PEquivOn f equivSucc (Iic i))
    (H : ∀ ⦃i⦄ (hi : ¬ IsMax i) x, (equivSucc hi x).1 = f (le_succ i) x) :
    PEquivOn f equivSucc (Iic (i⁺)) where
  equiv := piEquivSucc e.equiv (equivSucc hi) hi
  nat := isNatEquiv_piEquivSucc hi (H hi) e.nat
  compat hsj hj x := by
    obtain eq | lt := hsj.eq_or_lt
    · cases (succ_eq_succ_iff_of_not_isMax hj hi).mp eq; simp [piEquivSucc]
    · rw [piEquivSucc, piSplitLE_lt, e.compat] <;> assumption

variable (hi : IsSuccLimit i) (e : ∀ j : Iio i, PEquivOn f equivSucc (Iic j))

def pEquivOnGlue : PEquivOn f equivSucc (Iio i) where
  equiv := (piLTLim (X := fun j ↦ F j ≃ piLT X j) hi).symm
    ⟨fun j ↦ ((e j).restrict fun _ h ↦ h.le).equiv, fun _ _ h ↦ funext fun _ ↦
      pEquivOn_apply_eq ((isLowerSet_Iio _).inter <| isLowerSet_Iio _)⟩
  nat j k hj hk h := by rw [piLTLim_symm_apply]; apply (e _).nat; exact h.trans_lt (hi.mid _).2.1
  compat hj := have k := hi.mid hj
    by rw [piLTLim_symm_apply hi ⟨_, k.2.2⟩ (by exact k.2.1)]; apply (e _).compat

def pEquivOnLim [InverseSystem f]
    (equivLim : F i ≃ inverseLimit f i) (H : ∀ x l, (equivLim x).1 l = f l.2.le x) :
    PEquivOn f equivSucc (Iic i) where
  equiv := piEquivLim (pEquivOnGlue hi e).nat equivLim hi
  nat := isNatEquiv_piEquivLim (pEquivOnGlue hi e).nat hi H
  compat hsj hj x := by
    rw [piEquivLim, piSplitLE_lt (hi.succ_lt <| (succ_le_iff_of_not_isMax hj).mp hsj)]
    apply (pEquivOnGlue hi e).compat

end Unique

def globalEquiv [SuccOrder ι] [InverseSystem f]
    (equivSucc : ∀ i, ¬IsMax i → {e : F (i⁺) ≃ F i × X i // ∀ x, (e x).1 = f (le_succ i) x})
    (equivLim : ∀ i, IsSuccLimit i → {e : F i ≃ inverseLimit f i // ∀ x l, (e x).1 l = f l.2.le x})
    (i : ι) : F i ≃ piLT X i :=
  let e := SuccOrder.limitRecOn
    (C := (PEquivOn f (fun i hi ↦ (equivSucc i hi).1) <| Iic ·)) i
    (fun _ hi e ↦ pEquivOnSucc hi e fun i hi ↦ (equivSucc i hi).2)
    fun i hi e ↦ pEquivOnLim hi (fun j ↦ e j j.2) (equivLim i hi).1 (equivLim i hi).2
  e.equiv ⟨i, le_rfl⟩

end InverseLimit

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

set_option quotPrecheck false

/-- Index a basis of E/F using the initial ordinal of `Module.rank F E`. -/
local notation "ι" => (Module.rank F E).ord.out.α
instance : SuccOrder ι := SuccOrder.ofWellOrder

variable {F E} in
private lemma wf : WellFounded ((· : ι) < ·) := (Module.rank F E).ord.out.wo.wf
private lemma card_ι : #ι = Module.rank F E := (mk_ordinal_out _).trans (card_ord _)
instance : Nonempty ι := mk_ne_zero_iff.mp (rank_pos.trans_eq (card_ι F E).symm).ne'

/-- A basis of E/F indexed by the initial ordinal. -/
private def wellOrderedBasis : Basis ι F E :=
  (chooseBasis F E).reindex
    (Cardinal.eq.mp <| (card_ι F E).trans <| rank_eq_card_chooseBasisIndex F E).some.symm

local notation "b" => wellOrderedBasis F E
local notation "Ē" => AlgebraicClosure E

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
theorem Cardinal.mk_initialSeg {c : Cardinal} (i : c.ord.out.α) : #(Iio i) < c :=
  card_typein_out_lt c i

private theorem adjoin_basis_eq_top : adjoin F (range b) = ⊤ :=
  toSubalgebra_injective <| Subalgebra.toSubmodule_injective <| top_unique <|
    (Basis.span_eq b).ge.trans <| (Algebra.span_le_adjoin F _).trans <| algebra_adjoin_le_adjoin _ _

variable [rank_inf : Fact (ℵ₀ ≤ Module.rank F E)] (alg : Algebra.IsAlgebraic F E)

attribute [local instance] Cardinal.noMaxOrder

/-- `leastExt i` is defined to be the smallest `k : ι` that generates a nontrival extension over
(i.e. does not lie in) the subalgebra (= intermediate field) generated by all previous
`leastExt j`, `j < i`. For cardinality reasons, such `k` always exist if `ι` is infinite. -/
private def leastExt : ι → ι :=
  wf.fix fun i ih ↦
  let s := range fun j : Iio i ↦ b (ih j j.2)
  wf.min {k | b k ∉ adjoin F s} <| by
    rw [← compl_setOf, nonempty_compl]; by_contra!
    simp_rw [eq_univ_iff_forall, mem_setOf] at this
    have := adjoin_le_iff.mpr (range_subset_iff.mpr this)
    rw [adjoin_basis_eq_top, ← eq_top_iff] at this
    apply_fun Module.rank F at this
    refine ne_of_lt ?_ this
    conv_rhs => rw [topEquiv (F := F) (E := E) |>.toLinearEquiv.rank_eq]
    have := mk_initialSeg i
    obtain eq | lt := rank_inf.out.eq_or_lt
    · replace this := mk_lt_aleph0_iff.mp (this.trans_eq eq.symm)
      have : FiniteDimensional F (adjoin F s) :=
        finiteDimensional_adjoin fun x _ ↦ (alg x).isIntegral
      exact (rank_lt_aleph0 _ _).trans_eq eq
    · exact (Subalgebra.equivOfEq _ _ <| adjoin_algebraic_toSubalgebra (S := s) fun x _ ↦ alg x)
        |>.toLinearEquiv.rank_eq.trans_lt <|
        (Algebra.rank_adjoin_le _).trans_lt (max_lt (mk_range_le.trans_lt this) lt)
local notation "φ" => leastExt alg

section
local notation F"⟮<"i"⟯" => adjoin F (b ∘ φ '' Iio i)

variable {alg}

private theorem isLeast_φ' (i : ι) :
    IsLeast {k | b k ∉ adjoin F (range fun j : Iio i ↦ b (φ j))} (φ i) := by
  rw [leastExt, wf.fix_eq]; exact ⟨wf.min_mem _ _, fun _ ↦ (wf.min_le ·)⟩

private theorem isLeast_φ (i : ι) : IsLeast {k | b k ∉ F⟮<i⟯} (φ i) := by
  rw [image_eq_range]; exact isLeast_φ' i

private theorem strictMono_φ : StrictMono φ := fun i j h ↦ by
  have least := isLeast_φ (alg := alg)
  by_contra!
  obtain eq | lt := this.eq_or_lt
  · exact (least j).1 (subset_adjoin _ _ ⟨i, h, congr_arg b eq.symm⟩)
  · refine ((least i).2 <| mt (adjoin.mono _ _ _ (image_mono ?_) ·) (least j).1).not_lt lt
    exact fun k (hk : k < i) ↦ hk.trans h

private theorem adjoin_image_φ (i : ι) : F⟮<i⟯ = adjoin F (b '' Iio (φ i)) := by
  refine le_antisymm (adjoin.mono _ _ _ ?_) (adjoin_le_iff.mpr ?_)
  · rw [image_comp]; apply image_mono; rintro _ ⟨j, hj, rfl⟩; exact strictMono_φ hj
  · rintro _ ⟨j, hj, rfl⟩; contrapose! hj; exact ((isLeast_φ i).2 hj).not_lt

private theorem iSup_adjoin_eq_top : ⨆ i : ι, F⟮<i⟯ = ⊤ := by
  simp_rw [adjoin_image_φ, eq_top_iff, ← adjoin_basis_eq_top, adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  refine le_iSup (α := IntermediateField F E) _ (i⁺) (subset_adjoin _ _ ⟨i, ?_, rfl⟩)
  exact (lt_succ i).trans_le (wf.self_le_of_strictMono strictMono_φ _)

def strictMono_filtration : StrictMono (F⟮<·⟯) := fun i _ h ↦
  ⟨adjoin.mono _ _ _ (image_mono <| Iio_subset_Iio h.le),
    fun incl ↦ (isLeast_φ i).1 (incl <| subset_adjoin _ _ ⟨i, h, rfl⟩)⟩

theorem filtration_succ (i : ι) : F⟮<i⁺⟯ = F⟮<i⟯⟮b (φ i)⟯.restrictScalars F := by
  rw [Iio_succ, ← Iio_insert, image_insert_eq, ← union_singleton, adjoin_adjoin_left]; rfl

local notation "X" i => Field.Emb (F⟮<i⟯) <| F⟮<i⟯⟮b (φ i)⟯

variable (alg)

-- slow
def succEquiv (i : ι) : (F⟮<i⁺⟯ →ₐ[F] Ē) ≃ (F⟮<i⟯ →ₐ[F] Ē) × X i :=
  (((show _ ≃ₐ[F] F⟮<i⟯⟮b (φ i)⟯ from equivOfEq (filtration_succ i))).arrowCongr .refl).trans <|
    algHomEquivSigma (B := F⟮<i⟯).trans <| .sigmaEquivProdOfEquiv fun _ ↦
      (@Field.embEquivOfIsAlgClosed _ _ _ _ _ _ _ (_) <|
        (alg.tower_top _).of_injective (val _) Subtype.val_injective).symm

open FiniteDimensional

-- slow (~4s)
theorem succEquiv_coherence (i f) : (succEquiv alg i f).1 =
    f.comp (Subalgebra.inclusion <| strictMono_filtration.monotone <| le_succ i) := by
  ext; simp [succEquiv]; rfl

instance (i : ι) : FiniteDimensional (F⟮<i⟯) (F⟮<i⟯⟮b (φ i)⟯) :=
  adjoin.finiteDimensional (alg.tower_top _ _).isIntegral

theorem deg_lt_aleph0 (i : ι) : #(X i) < ℵ₀ :=
  (toNat_ne_zero.mp (Field.instNeZeroFinSepDegree (F⟮<i⟯) <| F⟮<i⟯⟮b (φ i)⟯).out).2

open WithTop in
@[simps!] def filtration : WithTop ι ↪o IntermediateField F E :=
  .ofStrictMono (fun i ↦ i.recTopCoe ⊤ (F⟮<·⟯)) fun i j h ↦ by
    cases j
    · obtain ⟨i, rfl⟩ := ne_top_iff_exists.mp h.ne
      exact ⟨le_top, fun incl ↦ (isLeast_φ i).1 (incl trivial)⟩
    · obtain ⟨i, rfl⟩ := ne_top_iff_exists.mp (h.trans <| coe_lt_top _).ne
      exact strictMono_filtration (coe_lt_coe.mp h)

def factor (i : WithTop ι) : Type _ := i.recTopCoe PUnit (X ·)

variable [IsSeparable F E] -- implies `alg`, but we keep using `alg` for convenience

-- slow (typeclass inference reasonable, type checking takes 8s)
instance (i : ι) : IsSeparable (F⟮<i⟯) (F⟮<i⟯⟮b (φ i)⟯) :=
  haveI := isSeparable_tower_top_of_isSeparable F (F⟮<i⟯) E
  haveI : IsScalarTower (F⟮<i⟯) (F⟮<i⟯⟮b (φ i)⟯) E := .of_algebraMap_eq' rfl
  isSeparable_tower_bot_of_isSeparable _ _ E

open Field in
theorem two_le_deg (i : ι) : 2 ≤ #(X i) := by
  rw [← Nat.cast_eq_ofNat, ← toNat_le_iff_le_of_lt_aleph0 (nat_lt_aleph0 _) (deg_lt_aleph0 _ i),
    toNat_cast, ← Nat.card, ← finSepDegree, finSepDegree_eq_finrank_of_isSeparable, Nat.succ_le]
  by_contra!
  obtain ⟨x, hx⟩ := finrank_adjoin_simple_eq_one_iff.mp (this.antisymm finrank_pos)
  refine (isLeast_φ (alg := alg) i).1 (hx ▸ ?_)
  exact x.2

end

local notation F"⟮<"i"⟯" => filtration (F := F) alg i
--local notation "X" i => factor alg i

def embFunctor ⦃i j : WithTop ι⦄ (h : i ≤ j) (f : F⟮<j⟯ →ₐ[F] Ē) : F⟮<i⟯ →ₐ[F] Ē :=
  f.comp (Subalgebra.inclusion <| (filtration _).monotone h)

instance : InverseSystem (embFunctor alg) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

def equivSucc (i : WithTop ι) : (F⟮<i⁺⟯ →ₐ[F] Ē) ≃ (F⟮<i⟯ →ₐ[F] Ē) × factor alg i :=
  i.recTopCoe (((equivOfEq <| by rw [succ_top]).arrowCongr .refl).trans <| .symm <| .prodPUnit _) <|
    (succEquiv alg ·)

theorem equivSucc_coherence (i f) : (equivSucc alg i f).1 = embFunctor alg (le_succ i) f := by
  cases i; exacts [rfl, succEquiv_coherence alg _ f]

section Lim

variable {i : WithTop (Module.rank F E).ord.out.α} -- WithTop ι doesn't work

theorem directed_filtration : Directed (· ≤ ·) fun j : Iio i ↦ filtration alg j :=
    ((filtration _).monotone.comp <| Subtype.mono_coe _).directed_le

variable (hi : IsSuccLimit i)

open WithTop in
theorem iSup_filtration : ⨆ j : Iio i, filtration alg j = filtration alg i := by
  cases i
  · rw [none_eq_top, ← range_coe, iSup_range']; exact iSup_adjoin_eq_top
  refine (iSup_le fun j ↦ (filtration _).monotone (mem_Iio.1 j.2).le).antisymm (adjoin_le_iff.2 ?_)
  rintro _ ⟨j, hj, rfl⟩
  refine le_iSup (α := IntermediateField F E) _ ⟨j⁺, ?_⟩ (subset_adjoin _ _ ?_)
  exacts [⟨j, lt_succ j, rfl⟩, hi.succ_lt (coe_lt_coe.mpr hj)]

open WithTop in
lemma eq_bot_of_not_nonempty (hi : ¬ Nonempty (Iio i)) : filtration alg i = ⊥ := by
  cases i
  · rw [none_eq_top, ← range_coe] at hi; exact (hi inferInstance).elim
  · exact bot_unique <| adjoin_le_iff.mpr fun _ ⟨j, hj, _⟩ ↦ (hi ⟨j, coe_lt_coe.mpr hj⟩).elim

open Classical WithTop in
def equivLim : (F⟮<i⟯ →ₐ[F] Ē) ≃ inverseLimit (embFunctor alg) i where
  toFun f := ⟨fun j ↦ embFunctor _ (id j.2 : j < i).le f, fun _ _ _ ↦ rfl⟩
  invFun f := if h : Nonempty (Iio i) then
    Subalgebra.iSupLift _ (directed_filtration _) f.1
      (fun _ _ h ↦ (f.2 <| (filtration _).map_rel_iff.mp h).symm) _ <| by
        rw [← iSup_filtration _ hi, toSubalgebra_iSup_of_directed (directed_filtration _)]
    else (Algebra.ofId F Ē).comp ((equivOfEq (eq_bot_of_not_nonempty _ hi h)).trans <| botEquiv F E)
  left_inv f := by
    split_ifs with h
    · ext ⟨x, hx⟩
      rw [← iSup_filtration _ hi, mem_toSubalgebra, ← SetLike.mem_coe,
          coe_iSup_of_directed (directed_filtration _), mem_iUnion] at hx
      rw [Subalgebra.iSupLift_of_mem _ (by exact hx.choose_spec)]; rfl
    · apply AlgHom.ext
      rw [((equivOfEq (eq_bot_of_not_nonempty alg hi h)).trans <| botEquiv F E).forall_congr_left']
      simp
  right_inv f := Subtype.ext <| funext fun j ↦ by
    have : Nonempty _ := ⟨j⟩
    simp_rw [dif_pos this]
    apply Subalgebra.iSupLift_comp_inclusion

theorem equivLim_coherence (x l) : (equivLim alg hi x).1 l = embFunctor alg (mem_Iio.mp l.2).le x :=
  rfl

end Lim

set_option pp.analyze true
def embEquivPi : Field.Emb F E ≃ ∀ i : ι, factor alg i :=
  let e := globalEquiv
    (fun i _ ↦ ⟨_, equivSucc_coherence alg i⟩) (fun _ hi ↦ ⟨_, equivLim_coherence alg hi⟩) ⊤
  (topEquiv.arrowCongr .refl).symm.trans <| e.trans <| .trans (.piCongrSet WithTop.range_coe.symm)
    <| .symm <| .piCongr (.ofInjective _ WithTop.coe_injective) fun _ ↦ .refl _

theorem Field.cardinal_emb_of_aleph0_le_rank_of_isSeparable [IsSeparable F E]
    (rank_inf : ℵ₀ ≤ Module.rank F E) : #(Field.Emb F E) = 2 ^ Module.rank F E := by
  rw [← card_ι, (embEquivPi alg).cardinal_eq, mk_pi, ← prod_const']
  apply le_antisymm <;> apply prod_le_prod
  --power_eq_two_power
