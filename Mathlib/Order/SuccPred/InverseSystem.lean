/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Order.SuccPred.Limit
import Mathlib.Order.UpperLower.Basic

/-!
# Definition of direct systems, inverse systems, and cardinalities in specific inverse systems

In this file we compute the cardinality of each node in an inverse system `F i` indexed by a
well-order in which every map between successive nodes has constant fiber `X i`, and every limit
node is the `limit` of the inverse subsystem formed by all previous nodes.
(To avoid importing `Cardinal`, we in fact construct a bijection rather than
stating the result in terms of `Cardinal.mk`.)

The most tricky part of the whole argument happens at limit nodes: if `i : ι` is a limit,
what we have in hand is a family of bijections `F j ≃ ∀ l : Iio j, X l` for every `j < i`,
which we would like to "glue" up to a bijection `F i ≃ ∀ l : Iio i, X l`. We denote
`∀ l : Iio i, X l` by `PiLT X i`, and they form an inverse system just like the `F i`.
Observe that at a limit node `i`, `PiLT X i` is actually the inverse limit of `PiLT X j` over
all `j < i` (`piLTLim`). If the family of bijections `F j ≃ PiLT X j` is natural (`IsNatEquiv`),
we immediately obtain a bijection between the limits `limit F i ≃ PiLT X i` (`invLimEquiv`),
and we just need an additional bijection `F i ≃ limit F i` to obtain the desired
extension `F i ≃ PiLT X i` to the limit node `i`. (We do have such a bijection, for example, when
we consider a directed system of algebraic structures (say fields) `K i`, and `F` is
the inverse system of homomorphisms `K i ⟶ K` into a specific field `K`.)

Now our task reduces to the recursive construction of a *natural* family of bijections for each `i`.
We can prove that a natural family over all `l ≤ i` (`Iic i`) extends to a natural family over
`Iic i⁺` (where `i⁺ = succ i`), but at a limit node, recursion stops working: we have natural
families over all `Iic j` for each `j < i`, but we need to know that they glue together to form a
natural family over all `l < i` (`Iio i`). This intricacy did not occur to the author when he
thought he had a proof and set out to formalize it. Fortunately he was able to figure out an
additional `compat` condition (compatibility with the bijections `F i⁺ ≃ F i × X i` in the `X`
component) that guarantees uniqueness (`unique_pEquivOn`) and hence gluability (well-definedness):
see `pEquivOnGlue`. Instead of just a family of natural families, we actually construct a family of
the stronger `PEquivOn`s that bundles the `compat` condition, in order for the inductive argument
to work.

It is possible to circumvent the introduction of the `compat` condition using Zorn's lemma;
if there is a chain of natural families (i.e. for any two families in the chain, one is an
extension of the other) over lowersets (which are all of the form `Iic`, `Iio`, or `univ`),
we can clearly take the union to get a natural family that extends them all. If a maximal
natural family has domain `Iic i` or `Iio i` (`i` a limit), we already know how to extend it
one step further to `Iic i⁺` or `Iic i` respectively, so it must be the case that the domain
is everything. However, the author chose the `compat` approach in the end because it constructs
the distinguished bijection that is compatible with the projections to all `X i`.

-/

open Order Set

variable {ι : Type*} [Preorder ι] {F X : ι → Type*}

variable (F) in
/-- A directed system is a functor from a category (directed poset) to another category. -/
class DirectedSystem (f : ∀ ⦃i j⦄, i ≤ j → F i → F j) : Prop where
  map_self ⦃i⦄ (x : F i) : f le_rfl x = x
  map_map ⦃k j i⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : F i) : f hjk (f hij x) = f (hij.trans hjk) x

variable (f : ∀ ⦃i j : ι⦄, i ≤ j → F j → F i) ⦃i j : ι⦄ (h : i ≤ j)

/-- A inverse system indexed by a preorder is a contravariant functor from the preorder
to another category. It is dual to `DirectedSystem`. -/
class InverseSystem : Prop where
  map_self ⦃i⦄ (x : F i) : f le_rfl x = x
  map_map ⦃k j i⦄ (hkj : k ≤ j) (hji : j ≤ i) (x : F i) : f hkj (f hji x) = f (hkj.trans hji) x

namespace InverseSystem

section proj

/-- The inverse limit of an inverse system of types. -/
def limit (i : ι) : Set (∀ l : Iio i, F l) :=
  {F | ∀ ⦃j k⦄ (h : j.1 ≤ k.1), f h (F k) = F j}

/-- For a family of types `X` indexed by an preorder `ι` and an element `i : ι`,
`piLT X i` is the product of all the types indexed by elements below `i`. -/
abbrev piLT (X : ι → Type*) (i : ι) := ∀ l : Iio i, X l

/-- The projection from a Pi type to the Pi type over an initial segment of its indexing type. -/
abbrev piLTProj (f : piLT X j) : piLT X i := fun l ↦ f ⟨l, l.2.trans_le h⟩

theorem piLTProj_intro {l : Iio j} {f : piLT X j} (hl : l < i) :
    f l = piLTProj h f ⟨l, hl⟩ := rfl

/-- The predicate that says a family of equivalences between `F j` and `piLT X j`
  is a natural transformation. -/
def IsNatEquiv {s : Set ι} (equiv : ∀ j : s, F j ≃ piLT X j) : Prop :=
  ∀ ⦃j k⦄ (hj : j ∈ s) (hk : k ∈ s) (h : k ≤ j) (x : F j),
    equiv ⟨k, hk⟩ (f h x) = piLTProj h (equiv ⟨j, hj⟩ x)

variable {ι : Type*} [LinearOrder ι] {X : ι → Type*} {i : ι} (hi : IsSuccPrelimit i)

/-- If `i` is a limit in a well-ordered type indexing a family of types,
then `piLT X i` is the limit of all `piLT X j` for `j < i`. -/
@[simps apply] noncomputable def piLTLim : piLT X i ≃ limit (piLTProj (X := X)) i where
  toFun f := ⟨fun j ↦ piLTProj j.2.le f, fun _ _ _ ↦ rfl⟩
  invFun f l := let k := hi.mid l.2; f.1 ⟨k, k.2.2⟩ ⟨l, k.2.1⟩
  left_inv f := rfl
  right_inv f := by
    ext j l
    set k := hi.mid (l.2.trans j.2)
    obtain le | le := le_total j ⟨k, k.2.2⟩
    exacts [congr_fun (f.2 le) l, (congr_fun (f.2 le) ⟨l, _⟩).symm]

theorem piLTLim_symm_apply {f} (k : Iio i) {l : Iio i} (hl : l.1 < k.1) :
    (piLTLim (X := X) hi).symm f l = f.1 k ⟨l, hl⟩ := by
  conv_rhs => rw [← (piLTLim hi).right_inv f]
  rfl

end proj

variable {ι : Type*} {F X : ι → Type*} {i : ι}

section

variable [PartialOrder ι] [DecidableEq ι]

/-- Splitting off the `X i` factor from the Pi type over `{j | j ≤ i}`. -/
def piSplitLE : piLT X i × X i ≃ ∀ j : Iic i, X j where
  toFun f j := if h : j = i then h.symm ▸ f.2 else f.1 ⟨j, j.2.lt_of_ne h⟩
  invFun f := (fun j ↦ f ⟨j, j.2.le⟩, f ⟨i, le_rfl⟩)
  left_inv f := by ext j; exacts [dif_neg j.2.ne, dif_pos rfl]
  right_inv f := by
    ext j; dsimp only; split_ifs with h
    · cases (Subtype.ext h : j = ⟨i, le_rfl⟩); rfl
    · rfl

@[simp] theorem piSplitLE_eq {f : piLT X i × X i} :
    piSplitLE f ⟨i, le_rfl⟩ = f.2 := by simp [piSplitLE]

theorem piSplitLE_lt {f : piLT X i × X i} {j} (hj : j < i) :
    piSplitLE f ⟨j, hj.le⟩ = f.1 ⟨j, hj⟩ := dif_neg hj.ne

end

variable [LinearOrder ι] {f : ∀ ⦃i j : ι⦄, i ≤ j → F j → F i}

local postfix:max "⁺" => succ -- Note: conflicts with `PosPart` notation

section Succ

variable [SuccOrder ι]
variable (equiv : ∀ j : Iic i, F j ≃ piLT X j) (e : F i⁺ ≃ F i × X i) (hi : ¬ IsMax i)

/-- Extend a family of bijections to `piLT` by one step. -/
def piEquivSucc : ∀ j : Iic i⁺, F j ≃ piLT X j :=
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

/-- A natural family of bijections below a limit ordinal
induces a bijection at the limit ordinal. -/
@[simps] def invLimEquiv : limit f i ≃ limit (piLTProj (X := X)) i where
  toFun t := ⟨fun l ↦ equiv l (t.1 l), fun _ _ h ↦ Eq.symm <| by simp_rw [← t.2 h]; apply nat⟩
  invFun t := ⟨fun l ↦ (equiv l).symm (t.1 l),
    fun _ _ h ↦ (Equiv.eq_symm_apply _).mpr <| by rw [nat, ← t.2 h]; simp⟩
  left_inv t := by ext; apply Equiv.left_inv
  right_inv t := by ext1; ext1; apply Equiv.right_inv

variable (equivLim : F i ≃ limit f i) (hi : IsSuccPrelimit i)

/-- Extend a natural family of bijections to a limit ordinal. -/
noncomputable def piEquivLim : ∀ j : Iic i, F j ≃ piLT X j :=
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

variable [SuccOrder ι] (f) (equivSucc : ∀ ⦃i⦄, ¬IsMax i → F i⁺ ≃ F i × X i)

/-- A natural partial family of bijections to `piLT` satisfying a compatibility condition. -/
@[ext] structure PEquivOn (s : Set ι) where
  /-- A partial family of bijections between `F` and `piLT X` defined on some set in `ι`. -/
  equiv (i : s) : F i ≃ piLT X i
  /-- It is a natural family of bijections. -/
  nat : IsNatEquiv f equiv
  /-- It is compatible with a family of bijections relating `F i⁺` to `F i`. -/
  compat {i} (hsi : (i⁺ : ι) ∈ s) (hi : ¬IsMax i) (x) :
    equiv ⟨i⁺, hsi⟩ x ⟨i, lt_succ_of_not_isMax hi⟩ = (equivSucc hi x).2

variable {s t : Set ι} {f equivSucc} [WellFoundedLT ι]

/-- Restrict a partial family of bijections to a smaller set. -/
@[simps] def PEquivOn.restrict (e : PEquivOn f equivSucc t) (h : s ⊆ t) :
    PEquivOn f equivSucc s where
  equiv i := e.equiv ⟨i, h i.2⟩
  nat _ _ _ _ := e.nat _ _
  compat _ := e.compat _

theorem unique_pEquivOn (hs : IsLowerSet s) {e₁ e₂ : PEquivOn f equivSucc s} : e₁ = e₂ := by
  obtain ⟨e₁, nat₁, compat₁⟩ := e₁
  obtain ⟨e₂, nat₂, compat₂⟩ := e₂
  ext1; ext1 i; dsimp only
  refine SuccOrder.prelimitRecOn i.1 (C := fun i ↦ ∀ h : i ∈ s, e₁ ⟨i, h⟩ = e₂ ⟨i, h⟩)
    (fun i nmax ih hi ↦ ?_) (fun i lim ih hi ↦ ?_) i.2
  · ext x ⟨j, hj⟩
    obtain rfl | hj := ((lt_succ_iff_of_not_isMax nmax).mp hj).eq_or_lt
    · exact (compat₁ _ nmax x).trans (compat₂ _ nmax x).symm
    have hi : i ∈ s := hs (le_succ i) hi
    rw [piLTProj_intro (f := e₁ _ x) (le_succ i) (by exact hj),
        ← nat₁ _ hi (by exact le_succ i), ih, nat₂ _ hi (by exact le_succ i)]
  · ext x j
    have ⟨k, hjk, hki⟩ := lim.mid j.2
    have hk : k ∈ s := hs hki.le hi
    rw [piLTProj_intro (f := e₁ _ x) hki.le hjk, piLTProj_intro (f := e₂ _ x) hki.le hjk,
      ← nat₁ _ hk, ← nat₂ _ hk, ih _ hki]

theorem pEquivOn_apply_eq (h : IsLowerSet (s ∩ t))
    {e₁ : PEquivOn f equivSucc s} {e₂ : PEquivOn f equivSucc t} {i} {his : i ∈ s} {hit : i ∈ t} :
    e₁.equiv ⟨i, his⟩ = e₂.equiv ⟨i, hit⟩ :=
  show (e₁.restrict inter_subset_left).equiv ⟨i, his, hit⟩ =
       (e₂.restrict inter_subset_right).equiv ⟨i, his, hit⟩ from
  congr_fun (congr_arg _ <| unique_pEquivOn h) _

/-- Extend a partial family of bijections by one step. -/
def pEquivOnSucc [InverseSystem f] (hi : ¬IsMax i) (e : PEquivOn f equivSucc (Iic i))
    (H : ∀ ⦃i⦄ (hi : ¬ IsMax i) x, (equivSucc hi x).1 = f (le_succ i) x) :
    PEquivOn f equivSucc (Iic i⁺) where
  equiv := piEquivSucc e.equiv (equivSucc hi) hi
  nat := isNatEquiv_piEquivSucc hi (H hi) e.nat
  compat hsj hj x := by
    obtain eq | lt := hsj.eq_or_lt
    · cases (succ_eq_succ_iff_of_not_isMax hj hi).mp eq; simp [piEquivSucc]
    · rwa [piEquivSucc, piSplitLE_lt, e.compat]

variable (hi : IsSuccPrelimit i) (e : ∀ j : Iio i, PEquivOn f equivSucc (Iic j))

/-- Glue partial families of bijections at a limit ordinal,
obtaining a partial family over a right-open interval. -/
noncomputable def pEquivOnGlue : PEquivOn f equivSucc (Iio i) where
  equiv := (piLTLim (X := fun j ↦ F j ≃ piLT X j) hi).symm
    ⟨fun j ↦ ((e j).restrict fun _ h ↦ h.le).equiv, fun _ _ h ↦ funext fun _ ↦
      pEquivOn_apply_eq ((isLowerSet_Iio _).inter <| isLowerSet_Iio _)⟩
  nat j k hj hk h := by rw [piLTLim_symm_apply]; exacts [(e _).nat _ _ _, h.trans_lt (hi.mid _).2.1]
  compat hj := have k := hi.mid hj
    by rw [piLTLim_symm_apply hi ⟨_, k.2.2⟩ (by exact k.2.1)]; apply (e _).compat

/-- Extend `pEquivOnGlue` by one step, obtaining a partial family over a right-closed interval. -/
noncomputable def pEquivOnLim [InverseSystem f]
    (equivLim : F i ≃ limit f i) (H : ∀ x l, (equivLim x).1 l = f l.2.le x) :
    PEquivOn f equivSucc (Iic i) where
  equiv := piEquivLim (pEquivOnGlue hi e).nat equivLim hi
  nat := isNatEquiv_piEquivLim (pEquivOnGlue hi e).nat hi H
  compat hsj hj x := by
    rw [piEquivLim, piSplitLE_lt (hi.succ_lt <| (succ_le_iff_of_not_isMax hj).mp hsj)]
    apply (pEquivOnGlue hi e).compat

end Unique

variable [WellFoundedLT ι] [SuccOrder ι] [InverseSystem f]
  (equivSucc : ∀ i, ¬IsMax i → {e : F i⁺ ≃ F i × X i // ∀ x, (e x).1 = f (le_succ i) x})
  (equivLim : ∀ i, IsSuccPrelimit i → {e : F i ≃ limit f i // ∀ x l, (e x).1 l = f l.2.le x})

private noncomputable def globalEquivAux (i : ι) :
    PEquivOn f (fun i hi ↦ (equivSucc i hi).1) (Iic i) :=
  SuccOrder.prelimitRecOn i
    (fun _ hi e ↦ pEquivOnSucc hi e fun i hi ↦ (equivSucc i hi).2)
    fun i hi e ↦ pEquivOnLim hi (fun j ↦ e j j.2) (equivLim i hi).1 (equivLim i hi).2

/-- Over a well-ordered type, construct a family of bijections by transfinite recursion. -/
noncomputable def globalEquiv (i : ι) : F i ≃ piLT X i :=
  (globalEquivAux equivSucc equivLim i).equiv ⟨i, le_rfl⟩

theorem globalEquiv_naturality ⦃i j⦄ (h : i ≤ j) (x : F j) :
    letI e := globalEquiv equivSucc equivLim
    e i (f h x) = piLTProj h (e j x) := by
  refine (DFunLike.congr_fun ?_ _).trans ((globalEquivAux equivSucc equivLim j).nat le_rfl h h x)
  exact pEquivOn_apply_eq ((isLowerSet_Iic _).inter <| isLowerSet_Iic _)

theorem globalEquiv_compatibility ⦃i⦄ (hi : ¬IsMax i) (x) :
    globalEquiv equivSucc equivLim i⁺ x ⟨i, lt_succ_of_not_isMax hi⟩ = ((equivSucc i hi).1 x).2 :=
  (globalEquivAux equivSucc equivLim i⁺).compat le_rfl hi x

end InverseSystem
