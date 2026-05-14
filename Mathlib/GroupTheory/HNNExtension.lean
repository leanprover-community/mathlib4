/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.Complement
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.List.Chain
public import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!

## HNN Extensions of Groups

This file defines the HNN extension of a group `G`, `HNNExtension G A B φ`. Given a group `G`,
subgroups `A` and `B` and an isomorphism `φ` of `A` and `B`, we adjoin a letter `t` to `G`, such
that for any `a ∈ A`, the conjugate of `of a` by `t` is `of (φ a)`, where `of` is the canonical map
from `G` into the `HNNExtension`. This construction is named after Graham Higman, Bernhard Neumann
and Hanna Neumann.

## Main definitions

- `HNNExtension G A B φ` : The HNN Extension of a group `G`, where `A` and `B` are subgroups and `φ`
  is an isomorphism between `A` and `B`.
- `HNNExtension.of` : The canonical embedding of `G` into `HNNExtension G A B φ`.
- `HNNExtension.t` : The stable letter of the HNN extension.
- `HNNExtension.lift` : Define a function `HNNExtension G A B φ →* H`, by defining it on `G` and `t`
- `HNNExtension.of_injective` : The canonical embedding `G →* HNNExtension G A B φ` is injective.
- `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range` : Britton's Lemma. If an element of
  `G` is represented by a reduced word, then this reduced word does not contain `t`.

-/

@[expose] public section

assert_not_exists Field

open Monoid Coprod Multiplicative Subgroup Function

/-- The relation we quotient the coproduct by to form an `HNNExtension`. -/
def HNNExtension.con (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) :
    Con (G ∗ Multiplicative ℤ) :=
  conGen (fun x y => ∃ (a : A),
    x = inr (ofAdd 1) * inl (a : G) ∧
    y = inl (φ a : G) * inr (ofAdd 1))

/-- The HNN Extension of a group `G`, `HNNExtension G A B φ`. Given a group `G`, subgroups `A` and
`B` and an isomorphism `φ` of `A` and `B`, we adjoin a letter `t` to `G`, such that for
any `a ∈ A`, the conjugate of `of a` by `t` is `of (φ a)`, where `of` is the canonical
map from `G` into the `HNNExtension`. -/
def HNNExtension (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : Type _ :=
  (HNNExtension.con G A B φ).Quotient

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B} {H : Type*}
  [Group H] {M : Type*} [Monoid M]

instance : Group (HNNExtension G A B φ) := by
  delta HNNExtension; infer_instance

namespace HNNExtension

/-- The canonical embedding `G →* HNNExtension G A B φ` -/
def of : G →* HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inl

/-- The stable letter of the `HNNExtension` -/
def t : HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inr (ofAdd 1)

theorem t_mul_of (a : A) :
    t * (of (a : G) : HNNExtension G A B φ) = of (φ a : G) * t :=
  (Con.eq _).2 <| ConGen.Rel.of _ _ <| ⟨a, by simp⟩

theorem of_mul_t (b : B) :
    (of (b : G) : HNNExtension G A B φ) * t = t * of (φ.symm b : G) := by
  rw [t_mul_of]; simp

theorem equiv_eq_conj (a : A) :
    (of (φ a : G) : HNNExtension G A B φ) = t * of (a : G) * t⁻¹ := by
  rw [t_mul_of]; simp

theorem equiv_symm_eq_conj (b : B) :
    (of (φ.symm b : G) : HNNExtension G A B φ) = t⁻¹ * of (b : G) * t := by
  rw [mul_assoc, of_mul_t]; simp

theorem inv_t_mul_of (b : B) :
    t⁻¹ * (of (b : G) : HNNExtension G A B φ) = of (φ.symm b : G) * t⁻¹ := by
  rw [equiv_symm_eq_conj]; simp

theorem of_mul_inv_t (a : A) :
    (of (a : G) : HNNExtension G A B φ) * t⁻¹ = t⁻¹ * of (φ a : G) := by
  rw [equiv_eq_conj]; simp [mul_assoc]

/-- Define a function `HNNExtension G A B φ →* H`, by defining it on `G` and `t` -/
def lift (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) :
    HNNExtension G A B φ →* H :=
  Con.lift _ (Coprod.lift f (zpowersHom H x)) (Con.conGen_le <| by
    rintro _ _ ⟨a, rfl, rfl⟩
    simp [hx])

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem lift_t (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) :
    lift f x hx t = x := by
  delta HNNExtension; simp [lift, t]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem lift_of (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) (g : G) :
    lift f x hx (of g) = f g := by
  delta HNNExtension; simp [lift, of]

@[ext high]
theorem hom_ext {f g : HNNExtension G A B φ →* M}
    (hg : f.comp of = g.comp of) (ht : f t = g t) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    Coprod.hom_ext hg (MonoidHom.ext_mint ht)

@[elab_as_elim]
theorem induction_on {motive : HNNExtension G A B φ → Prop}
    (x : HNNExtension G A B φ) (of : ∀ g, motive (of g))
    (t : motive t) (mul : ∀ x y, motive x → motive y → motive (x * y))
    (inv : ∀ x, motive x → motive x⁻¹) : motive x := by
  let S : Subgroup (HNNExtension G A B φ) :=
    { carrier := setOf motive
      one_mem' := by simpa using of 1
      mul_mem' := mul _ _
      inv_mem' := inv _ }
  let f : HNNExtension G A B φ →* S :=
    lift (HNNExtension.of.codRestrict S of)
      ⟨HNNExtension.t, t⟩ (by intro a; ext; simp [equiv_eq_conj, mul_assoc])
  have hf : S.subtype.comp f = MonoidHom.id _ :=
    hom_ext (by ext; simp [f]) (by simp [f])
  change motive (MonoidHom.id _ x)
  rw [← hf]
  exact (f x).2

variable (A B φ)

/-- To avoid duplicating code, we define `toSubgroup A B u` and `toSubgroupEquiv u`
where `u : ℤˣ` is `1` or `-1`. `toSubgroup A B u` is `A` when `u = 1` and `B` when `u = -1`,
and `toSubgroupEquiv` is `φ` when `u = 1` and `φ⁻¹` when `u = -1`. `toSubgroup u` is the subgroup
such that for any `a ∈ toSubgroup u`, `t ^ (u : ℤ) * a = toSubgroupEquiv a * t ^ (u : ℤ)`. -/
def toSubgroup (u : ℤˣ) : Subgroup G :=
  if u = 1 then A else B

@[simp]
theorem toSubgroup_one : toSubgroup A B 1 = A := rfl

@[simp]
theorem toSubgroup_neg_one : toSubgroup A B (-1) = B := rfl

variable {A B}

/-- To avoid duplicating code, we define `toSubgroup A B u` and `toSubgroupEquiv u`
where `u : ℤˣ` is `1` or `-1`. `toSubgroup A B u` is `A` when `u = 1` and `B` when `u = -1`,
and `toSubgroupEquiv` is the group isomorphism from `toSubgroup A B u` to `toSubgroup A B (-u)`.
It is defined to be `φ` when `u = 1` and `φ⁻¹` when `u = -1`. -/
def toSubgroupEquiv (u : ℤˣ) : toSubgroup A B u ≃* toSubgroup A B (-u) :=
  if hu : u = 1 then hu ▸ φ else by
    convert φ.symm <;>
    cases Int.units_eq_one_or u <;> simp_all

@[simp]
theorem toSubgroupEquiv_one : toSubgroupEquiv φ 1 = φ := rfl

@[simp]
theorem toSubgroupEquiv_neg_one : toSubgroupEquiv φ (-1) = φ.symm := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem toSubgroupEquiv_neg_apply (u : ℤˣ) (a : toSubgroup A B u) :
    (toSubgroupEquiv φ (-u) (toSubgroupEquiv φ u a) : G) = a := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [toSubgroup]
  · simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, SetLike.coe_eq_coe]
    exact φ.apply_symm_apply a

namespace NormalWord

variable (G A B)
/-- To put a word in the HNN Extension into a normal form, we must choose an element of each right
coset of both `A` and `B`, such that the chosen element of the subgroup itself is `1`. -/
structure TransversalPair : Type _ where
  /-- The transversal of each subgroup -/
  set : ℤˣ → Set G
  /-- We have exactly one element of each coset of the subgroup -/
  compl : ∀ u, IsComplement (toSubgroup A B u : Subgroup G) (set u)

instance TransversalPair.nonempty : Nonempty (TransversalPair G A B) := by
  choose t ht using fun u ↦ (toSubgroup A B u).exists_isComplement_right 1
  exact ⟨⟨t, fun i ↦ (ht i).1⟩⟩

/-- A reduced word is a `head`, which is an element of `G`, followed by the product list of pairs.
There should also be no sequences of the form `t^u * g * t^-u`, where `g` is in
`toSubgroup A B u`. This is a less strict condition than required for `NormalWord`. -/
structure ReducedWord : Type _ where
  /-- Every `ReducedWord` is the product of an element of the group and a word made up
  of letters each of which is in the transversal. `head` is that element of the base group. -/
  head : G
  /-- The list of pairs `(ℤˣ × G)`, where each pair `(u, g)` represents the element `t^u * g` of
  `HNNExtension G A B φ` -/
  toList : List (ℤˣ × G)
  /-- There are no sequences of the form `t^u * g * t^-u` where `g ∈ toSubgroup A B u`. -/
  chain : toList.IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1)

/-- The empty reduced word. -/
@[simps]
def ReducedWord.empty : ReducedWord G A B :=
  { head := 1
    toList := []
    chain := List.isChain_nil }

variable {G A B}
/-- The product of a `ReducedWord` as an element of the `HNNExtension` -/
def ReducedWord.prod : ReducedWord G A B → HNNExtension G A B φ :=
  fun w => of w.head * (w.toList.map (fun x => t ^ (x.1 : ℤ) * of x.2)).prod

/-- Given a `TransversalPair`, we can make a normal form for words in the `HNNExtension G A B φ`.
The normal form is a `head`, which is an element of `G`, followed by the product list of pairs,
`t ^ u * g`, where `u` is `1` or `-1` and `g` is the chosen element of its right coset of
`toSubgroup A B u`. There should also be no sequences of the form `t^u * g * t^-u`
where `g ∈ toSubgroup A B u` -/
structure _root_.HNNExtension.NormalWord (d : TransversalPair G A B) : Type _
    extends ReducedWord G A B where
  /-- Every element `g : G` in the list is the chosen element of its coset -/
  mem_set : ∀ (u : ℤˣ) (g : G), (u, g) ∈ toList → g ∈ d.set u

variable {d : TransversalPair G A B}

@[ext]
theorem ext {w w' : NormalWord d}
    (h1 : w.head = w'.head) (h2 : w.toList = w'.toList) : w = w' := by
  rcases w with ⟨⟨⟩, _⟩; cases w'; simp_all

/-- The empty word -/
@[simps]
def empty : NormalWord d :=
  { head := 1
    toList := []
    mem_set := by simp
    chain := List.isChain_nil }

/-- The `NormalWord` representing an element `g` of the group `G`, which is just the element `g`
itself. -/
@[simps]
def ofGroup (g : G) : NormalWord d :=
  { head := g
    toList := []
    mem_set := by simp
    chain := List.isChain_nil }

instance : Inhabited (NormalWord d) := ⟨empty⟩

instance : MulAction G (NormalWord d) :=
  { smul := fun g w => { w with head := g * w.head }
    one_smul := by simp +instances [instHSMul]
    mul_smul := by simp +instances [instHSMul, mul_assoc] }

theorem group_smul_def (g : G) (w : NormalWord d) :
    g • w = { w with head := g * w.head } := rfl

@[simp]
theorem group_smul_head (g : G) (w : NormalWord d) : (g • w).head = g * w.head := rfl

@[simp]
theorem group_smul_toList (g : G) (w : NormalWord d) : (g • w).toList = w.toList := rfl

instance : FaithfulSMul G (NormalWord d) := ⟨by simp [group_smul_def]⟩

/-- A constructor to append an element `g` of `G` and `u : ℤˣ` to a word `w` with sufficient
hypotheses that no normalization or cancellation need take place for the result to be in normal form
-/
@[simps]
def cons (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.head ∈ toSubgroup A B u → u = u') :
    NormalWord d :=
  { head := g,
    toList := (u, w.head) :: w.toList,
    mem_set := by
      intro u' g' h'
      simp only [List.mem_cons, Prod.mk.injEq] at h'
      rcases h' with ⟨rfl, rfl⟩ | h'
      · exact h1
      · exact w.mem_set _ _ h'
    chain := by
      refine List.isChain_cons.2 ⟨?_, w.chain⟩
      rintro ⟨u', g'⟩ hu' hw1
      exact h2 _ (by simp_all) hw1 }

/-- A recursor to induct on a `NormalWord`, by proving the property is preserved under `cons` -/
@[elab_as_elim]
def consRecOn {motive : NormalWord d → Sort*} (w : NormalWord d)
    (ofGroup : ∀ g, motive (ofGroup g))
    (cons : ∀ (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
      (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?,
        w.head ∈ toSubgroup A B u → u = u'),
      motive w → motive (cons g u w h1 h2)) : motive w := by
  rcases w with ⟨⟨g, l, chain⟩, mem_set⟩
  induction l generalizing g with
  | nil => exact ofGroup _
  | cons a l ih =>
    exact cons g a.1
      { head := a.2
        toList := l
        mem_set := fun _ _ h => mem_set _ _ (List.mem_cons_of_mem _ h),
        chain := (List.isChain_cons.1 chain).2 }
      (mem_set a.1 a.2 List.mem_cons_self)
      (by simpa using (List.isChain_cons.1 chain).1)
      (ih _ _ _)

@[simp]
theorem consRecOn_ofGroup {motive : NormalWord d → Sort*}
    (g : G) (ofGroup : ∀ g, motive (ofGroup g))
    (cons : ∀ (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
      (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.head
        ∈ toSubgroup A B u → u = u'),
      motive w → motive (cons g u w h1 h2)) :
    consRecOn (.ofGroup g) ofGroup cons = ofGroup g := rfl

@[simp]
theorem consRecOn_cons {motive : NormalWord d → Sort*}
    (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.head ∈ toSubgroup A B u → u = u')
    (ofGroup : ∀ g, motive (ofGroup g))
    (cons : ∀ (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
      (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?,
        w.head ∈ toSubgroup A B u → u = u'),
      motive w → motive (cons g u w h1 h2)) :
    consRecOn (.cons g u w h1 h2) ofGroup cons = cons g u w h1 h2
      (consRecOn w ofGroup cons) := rfl

@[simp]
theorem smul_cons (g₁ g₂ : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.head ∈ toSubgroup A B u → u = u') :
    g₁ • cons g₂ u w h1 h2 = cons (g₁ * g₂) u w h1 h2 :=
  rfl

@[simp]
theorem smul_ofGroup (g₁ g₂ : G) :
    g₁ • (ofGroup g₂ : NormalWord d) = ofGroup (g₁ * g₂) := rfl

variable (d)
/-- The action of `t^u` on `ofGroup g`. The normal form will be
`a * t^u * g'` where `a ∈ toSubgroup A B (-u)` -/
noncomputable def unitsSMulGroup (u : ℤˣ) (g : G) :
    (toSubgroup A B (-u)) × d.set u :=
  let g' := (d.compl u).equiv g
  (toSubgroupEquiv φ u g'.1, g'.2)

theorem unitsSMulGroup_snd (u : ℤˣ) (g : G) :
    (unitsSMulGroup φ d u g).2 = ((d.compl u).equiv g).2 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

variable {d}

/-- `Cancels u w` is a predicate expressing whether `t^u` cancels with some occurrence
of `t^-u` when we multiply `t^u` by `w`. -/
def Cancels (u : ℤˣ) (w : NormalWord d) : Prop :=
  (w.head ∈ (toSubgroup A B u : Subgroup G)) ∧ w.toList.head?.map Prod.fst = some (-u)

/-- Multiplying `t^u` by `w` in the special case where cancellation happens -/
def unitsSMulWithCancel (u : ℤˣ) (w : NormalWord d) : Cancels u w → NormalWord d :=
  consRecOn w
    (by simp [Cancels, ofGroup]; tauto)
    (fun g _ w _ _ _ can =>
      (toSubgroupEquiv φ u ⟨g, can.1⟩ : G) • w)

/-- Multiplying `t^u` by a `NormalWord`, `w` and putting the result in normal form. -/
noncomputable def unitsSMul (u : ℤˣ) (w : NormalWord d) : NormalWord d :=
  letI := Classical.dec
  if h : Cancels u w
  then unitsSMulWithCancel φ u w h
  else let g' := unitsSMulGroup φ d u w.head
    cons g'.1 u ((g'.2 * w.head⁻¹ : G) • w)
      (by simp)
      (by
        simp only [g', group_smul_toList, Option.mem_def, Option.map_eq_some_iff, Prod.exists,
          exists_and_right, exists_eq_right, group_smul_head, inv_mul_cancel_right,
          forall_exists_index, unitsSMulGroup]
        simp only [Cancels, Option.map_eq_some_iff, Prod.exists, exists_and_right, exists_eq_right,
          not_and, not_exists] at h
        intro u' x hx hmem
        have : w.head ∈ toSubgroup A B u := by
          have := (d.compl u).rightCosetEquivalence_equiv_snd w.head
          rw [RightCosetEquivalence, rightCoset_eq_iff, mul_mem_cancel_left hmem] at this
          simp_all
        have := h this x
        simp_all [Int.units_ne_iff_eq_neg])

/-- A condition for not cancelling whose hypotheses are the same as those of the `cons` function. -/
theorem not_cancels_of_cons_hyp (u : ℤˣ) (w : NormalWord d)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?,
      w.head ∈ toSubgroup A B u → u = u') :
    ¬ Cancels u w := by
  simp only [Cancels, Option.map_eq_some_iff, Prod.exists,
    exists_and_right, exists_eq_right, not_and, not_exists]
  intro hw x hx
  rw [hx] at h2
  simpa using h2 (-u) rfl hw

theorem unitsSMul_cancels_iff (u : ℤˣ) (w : NormalWord d) :
    Cancels (-u) (unitsSMul φ u w) ↔ ¬ Cancels u w := by
  by_cases h : Cancels u w
  · simp only [unitsSMul, h, dite_true, not_true_eq_false, iff_false]
    induction w using consRecOn with
    | ofGroup => simp [Cancels, unitsSMulWithCancel]
    | cons g u' w h1 h2 _ =>
      intro hc
      apply not_cancels_of_cons_hyp _ _ h2
      simp only [Cancels, cons_head, cons_toList, List.head?_cons,
        Option.map_some, Option.some.injEq] at h
      cases h.2
      simpa [Cancels, unitsSMulWithCancel,
        Subgroup.mul_mem_cancel_left] using hc
  · simp only [unitsSMul, dif_neg h]
    simpa [Cancels] using h

theorem unitsSMul_neg (u : ℤˣ) (w : NormalWord d) :
    unitsSMul φ (-u) (unitsSMul φ u w) = w := by
  rw [unitsSMul]
  split_ifs with hcan
  · have hncan : ¬ Cancels u w := (unitsSMul_cancels_iff _ _ _).1 hcan
    unfold unitsSMul
    simp only [dif_neg hncan]
    simp [unitsSMulWithCancel, unitsSMulGroup, (d.compl u).equiv_snd_eq_inv_mul,
      -SetLike.coe_sort_coe]
  · have hcan2 : Cancels u w := not_not.1 (mt (unitsSMul_cancels_iff _ _ _).2 hcan)
    unfold unitsSMul at hcan ⊢
    simp only [dif_pos hcan2] at hcan ⊢
    cases w using consRecOn with
    | ofGroup => simp [Cancels] at hcan2
    | cons g u' w h1 h2 ih =>
      clear ih
      simp only [unitsSMulGroup, SetLike.coe_sort_coe, unitsSMulWithCancel, id_eq, consRecOn_cons,
        group_smul_head,
        mul_inv_rev]
      cases hcan2.2
      have : ((d.compl (-u)).equiv w.head).1 = 1 :=
        (d.compl (-u)).equiv_fst_eq_one_of_mem_of_one_mem _ h1
      simpa [NormalWord.ext_iff, (d.compl (-u)).equiv_mul_left, Units.ext_iff,
        (d.compl (-u)).equiv_snd_eq_inv_mul]

/-- the equivalence given by multiplication on the left by `t` -/
@[simps]
noncomputable def unitsSMulEquiv : NormalWord d ≃ NormalWord d :=
  { toFun := unitsSMul φ 1
    invFun := unitsSMul φ (-1),
    left_inv := fun _ => by rw [unitsSMul_neg]
    right_inv := fun w => by convert unitsSMul_neg _ _ w; simp }

set_option backward.isDefEq.respectTransparency false in
theorem unitsSMul_one_group_smul (g : A) (w : NormalWord d) :
    unitsSMul φ 1 ((g : G) • w) = (φ g : G) • (unitsSMul φ 1 w) := by
  unfold unitsSMul
  have : Cancels 1 ((g : G) • w) ↔ Cancels 1 w := by
    simp [Cancels, Subgroup.mul_mem_cancel_left]
  by_cases hcan : Cancels 1 w
  · simp only [unitsSMulWithCancel, toSubgroup_one, id_eq, toSubgroup_neg_one, toSubgroupEquiv_one,
      group_smul_head, mul_inv_rev, dif_pos (this.2 hcan), dif_pos hcan]
    cases w using consRecOn
    · simp [Cancels] at hcan
    · simp only [smul_cons, consRecOn_cons]
      rw [← mul_smul, ← Subgroup.coe_mul, ← map_mul φ]
      rfl
  · rw [dif_neg (mt this.1 hcan), dif_neg hcan]
    -- Before https://github.com/leanprover/lean4/pull/2644, all this was just
    -- `simp [← mul_smul, mul_assoc, unitsSMulGroup]`
    simp +instances only [toSubgroup_neg_one, unitsSMulGroup, toSubgroup_one, toSubgroupEquiv_one,
      SetLike.coe_sort_coe, group_smul_head, mul_inv_rev, ← mul_smul, mul_assoc, inv_mul_cancel,
      mul_one, smul_cons]
    -- This used to be the end of the proof before https://github.com/leanprover/lean4/pull/2644
    congr 1
    · conv_lhs => erw [IsComplement.equiv_mul_left]
      simp_rw [toSubgroup_one]
      simp only [SetLike.coe_sort_coe, map_mul, Subgroup.coe_mul]
    conv_lhs => erw [IsComplement.equiv_mul_left]
    rfl

noncomputable instance : MulAction (HNNExtension G A B φ) (NormalWord d) :=
  MulAction.ofEndHom <| (MulAction.toEndHom (M := Equiv.Perm (NormalWord d))).comp
    (HNNExtension.lift (MulAction.toPermHom _ _) (unitsSMulEquiv φ) <| by
      intro a
      ext : 1
      simp [unitsSMul_one_group_smul])

@[simp]
theorem prod_group_smul (g : G) (w : NormalWord d) :
    (g • w).prod φ = of g * (w.prod φ) := by
  simp [ReducedWord.prod, mul_assoc]

theorem of_smul_eq_smul (g : G) (w : NormalWord d) :
    (of g : HNNExtension G A B φ) • w = g • w := by
  simp +instances [instHSMul, SMul.smul, MulAction.toEndHom]

theorem t_smul_eq_unitsSMul (w : NormalWord d) :
    (t : HNNExtension G A B φ) • w = unitsSMul φ 1 w := by
  simp +instances [instHSMul, SMul.smul, MulAction.toEndHom]

theorem t_pow_smul_eq_unitsSMul (u : ℤˣ) (w : NormalWord d) :
    (t ^ (u : ℤ) : HNNExtension G A B φ) • w = unitsSMul φ u w := by
  rcases Int.units_eq_one_or u with (rfl | rfl) <;>
    simp +instances [instHSMul, SMul.smul, MulAction.toEndHom, Equiv.Perm.inv_def]

@[simp]
theorem prod_cons (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?,
      w.head ∈ toSubgroup A B u → u = u') :
    (cons g u w h1 h2).prod φ = of g * (t ^ (u : ℤ) * w.prod φ) := by
  simp [ReducedWord.prod, cons, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem prod_unitsSMul (u : ℤˣ) (w : NormalWord d) :
    (unitsSMul φ u w).prod φ = (t ^ (u : ℤ) * w.prod φ : HNNExtension G A B φ) := by
  rw [unitsSMul]
  split_ifs with hcan
  · cases w using consRecOn
    · simp [Cancels] at hcan
    · cases hcan.2
      simp only [unitsSMulWithCancel, id_eq, consRecOn_cons, prod_group_smul, prod_cons, zpow_neg]
      rcases Int.units_eq_one_or u with (rfl | rfl)
      · simp [equiv_eq_conj, mul_assoc]
      · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
        -- simp [equiv_symm_eq_conj, mul_assoc].
        simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one,
          Int.reduceNeg, zpow_neg, zpow_one, inv_inv]
        erw [equiv_symm_eq_conj, mul_assoc, mul_assoc]
  · simp only [unitsSMulGroup, SetLike.coe_sort_coe, prod_cons, prod_group_smul, map_mul, map_inv]
    rcases Int.units_eq_one_or u with (rfl | rfl)
    · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
      -- simp [equiv_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul].
      simp only [toSubgroup_neg_one, toSubgroup_one, toSubgroupEquiv_one, equiv_eq_conj, mul_assoc,
        Units.val_one, zpow_one, inv_mul_cancel_left, mul_right_inj]
      erw [(d.compl 1).equiv_snd_eq_inv_mul]
      simp [mul_assoc]
    · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
      -- simp [equiv_symm_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul]
      simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one,
        Int.reduceNeg, zpow_neg, zpow_one, mul_assoc]
      erw [equiv_symm_eq_conj, (d.compl (-1)).equiv_snd_eq_inv_mul]
      simp [mul_assoc]

@[simp]
theorem prod_empty : (empty : NormalWord d).prod φ = 1 := by
  simp [ReducedWord.prod]

@[simp]
theorem prod_smul (g : HNNExtension G A B φ) (w : NormalWord d) :
    (g • w).prod φ = g * w.prod φ := by
  induction g using induction_on generalizing w with
  | of => simp [of_smul_eq_smul]
  | t => simp [t_smul_eq_unitsSMul, prod_unitsSMul]
  | mul => simp_all [mul_smul, mul_assoc]
  | inv x ih =>
    rw [← mul_right_inj x, ← ih]
    simp

@[simp]
theorem prod_smul_empty (w : NormalWord d) :
    (w.prod φ) • empty = w := by
  induction w using consRecOn with
  | ofGroup => simp [ofGroup, ReducedWord.prod, of_smul_eq_smul, group_smul_def]
  | cons g u w h1 h2 ih =>
    rw [prod_cons, ← mul_assoc, mul_smul, ih, mul_smul, t_pow_smul_eq_unitsSMul,
      of_smul_eq_smul, unitsSMul]
    rw [dif_neg (not_cancels_of_cons_hyp u w h2)]
    -- Before https://github.com/leanprover/lean4/pull/2644, this was just
    -- simp [unitsSMulGroup, (d.compl _).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) h1,
    --   -SetLike.coe_sort_coe]
    -- ext <;> simp [-SetLike.coe_sort_coe]
    simp only [unitsSMulGroup, (d.compl _).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) h1,
      (d.compl _).equiv_snd_eq_inv_mul, inv_one, one_mul, mul_inv_cancel, one_smul, smul_cons]
    ext <;> simp

variable (d)
/-- The equivalence between elements of the HNN extension and words in normal form. -/
noncomputable def equiv : HNNExtension G A B φ ≃ NormalWord d :=
  { toFun := fun g => g • empty,
    invFun := fun w => w.prod φ,
    left_inv := fun g => by simp [prod_smul]
    right_inv := fun w => by simp }

theorem prod_injective : Injective
    (fun w => w.prod φ : NormalWord d → HNNExtension G A B φ) :=
  (equiv φ d).symm.injective

instance : FaithfulSMul (HNNExtension G A B φ) (NormalWord d) :=
  ⟨fun h => by simpa using congr_arg (fun w => w.prod φ) (h empty)⟩

end NormalWord

open NormalWord

theorem of_injective : Function.Injective (of : G → HNNExtension G A B φ) := by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  refine Function.Injective.of_comp
    (f := ((· • ·) : HNNExtension G A B φ → NormalWord d → NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [funext_iff, of_smul_eq_smul])

namespace ReducedWord

theorem exists_normalWord_prod_eq
    (d : TransversalPair G A B) (w : ReducedWord G A B) :
    ∃ w' : NormalWord d, w'.prod φ = w.prod φ ∧
      w'.toList.map Prod.fst = w.toList.map Prod.fst ∧
      ∀ u ∈ w.toList.head?.map Prod.fst,
      w'.head⁻¹ * w.head ∈ toSubgroup A B (-u) := by
  suffices ∀ w : ReducedWord G A B,
      w.head = 1 → ∃ w' : NormalWord d, w'.prod φ = w.prod φ ∧
      w'.toList.map Prod.fst = w.toList.map Prod.fst ∧
      ∀ u ∈ w.toList.head?.map Prod.fst,
      w'.head ∈ toSubgroup A B (-u) by
    by_cases hw1 : w.head = 1
    · simp only [hw1, inv_mem_iff, mul_one]
      exact this w hw1
    · rcases this ⟨1, w.toList, w.chain⟩ rfl with ⟨w', hw'⟩
      exact ⟨w.head • w', by
        simpa [ReducedWord.prod, mul_assoc] using hw'⟩
  intro w hw1
  rcases w with ⟨g, l, chain⟩
  dsimp at hw1; subst hw1
  induction l with
  | nil =>
    exact
      ⟨{ head := 1
         toList := []
         mem_set := by simp
         chain := List.isChain_nil }, by simp⟩
  | cons a l ih =>
    rcases ih (List.isChain_cons.1 chain).2 with ⟨w', hw'1, hw'2, hw'3⟩
    clear ih
    refine ⟨(t^(a.1 : ℤ) * of a.2 : HNNExtension G A B φ) • w', ?_, ?_⟩
    · rw [prod_smul, hw'1]
      simp [ReducedWord.prod]
    · have : ¬ Cancels a.1 (a.2 • w') := by
        simp only [Cancels, group_smul_head, group_smul_toList, Option.map_eq_some_iff,
          Prod.exists, exists_and_right, exists_eq_right, not_and, not_exists]
        intro hS x hx
        have hx' := congr_arg (Option.map Prod.fst) hx
        rw [← List.head?_map, hw'2, List.head?_map, Option.map_some] at hx'
        have : w'.head ∈ toSubgroup A B a.fst := by
          simpa using hw'3 _ hx'
        rw [mul_mem_cancel_right this] at hS
        have : a.fst = -a.fst := by
          have hl : l ≠ [] := by rintro rfl; simp_all
          have : a.fst = (l.head hl).fst := (List.isChain_cons.1 chain).1 (l.head hl)
            (List.head?_eq_some_head _) hS
          rwa [List.head?_eq_some_head hl, Option.map_some, ← this, Option.some_inj] at hx'
        simp at this
      simp [mul_smul, of_smul_eq_smul, t_pow_smul_eq_unitsSMul, unitsSMul, dif_neg this, ← hw'2]

/-- Two reduced words representing the same element of the `HNNExtension G A B φ` have the same
length corresponding list, with the same pattern of occurrences of `t^1` and `t^(-1)`,
and also the `head` is in the same left coset of `toSubgroup A B (-u)`, where `u : ℤˣ`
is the exponent of the first occurrence of `t` in the word. -/
theorem map_fst_eq_and_of_prod_eq {w₁ w₂ : ReducedWord G A B}
    (hprod : w₁.prod φ = w₂.prod φ) :
    w₁.toList.map Prod.fst = w₂.toList.map Prod.fst ∧
     ∀ u ∈ w₁.toList.head?.map Prod.fst,
      w₁.head⁻¹ * w₂.head ∈ toSubgroup A B (-u) := by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  rcases exists_normalWord_prod_eq φ d w₁ with ⟨w₁', hw₁'1, hw₁'2, hw₁'3⟩
  rcases exists_normalWord_prod_eq φ d w₂ with ⟨w₂', hw₂'1, hw₂'2, hw₂'3⟩
  have : w₁' = w₂' :=
    NormalWord.prod_injective φ d (by dsimp only; rw [hw₁'1, hw₂'1, hprod])
  subst this
  refine ⟨by rw [← hw₁'2, hw₂'2], ?_⟩
  simp only [← leftCoset_eq_iff] at *
  intro u hu
  rw [← hw₁'3 _ hu, ← hw₂'3 _]
  rwa [← List.head?_map, ← hw₂'2, hw₁'2, List.head?_map]

/-- **Britton's Lemma**. Any reduced word whose product is an element of `G`, has no
occurrences of `t`. -/
theorem toList_eq_nil_of_mem_of_range (w : ReducedWord G A B)
    (hw : w.prod φ ∈ (of.range : Subgroup (HNNExtension G A B φ))) :
    w.toList = [] := by
  rcases hw with ⟨g, hg⟩
  let w' : ReducedWord G A B := { ReducedWord.empty G A B with head := g }
  have : w.prod φ = w'.prod φ := by simp [w', ReducedWord.prod, hg]
  simpa [w'] using (map_fst_eq_and_of_prod_eq φ this).1

end ReducedWord

end HNNExtension
