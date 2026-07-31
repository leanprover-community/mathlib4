/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max
import GreensRelations.Order

/-!
# The Factorization Forest Theorem

This file defines the basic structures for the Factorization Forest Theorem.

## References
* [T. Colcombet, *The Factorization Forest Theorem*][colombet2008]
-/

namespace FactorizationForest

section SplitDefinitions

variable {S α : Type*} [Semigroup S] [LinearOrder α]

variable {h : ℕ}

/-- A multiplicative labeling over a linearly ordered set into a semigroup,
satisfying the property that `σ x y * σ y z = σ x z`. -/
structure MultiplicativeLabeling (S α : Type*) [Semigroup S] [LinearOrder α] where
  σ : α → α → S
  prop : ∀ x y z : α, x < y → y < z → σ x y * σ y z = σ x z

/-- A split is a function assigning each element of `α` a bounded integer rank in `Fin h`. -/
abbrev Split (α : Type*) (h : ℕ) := α → Fin h

/-- `splitRelation s x y` states that `x` and `y` share the same rank under `s`,
and any element bounded between them has a rank at most that of `x` and `y`. -/
abbrev SplitRelation (s : Split α h) (x y : α) : Prop :=
  s x = s y ∧ ∀ z, min x y ≤ z → z ≤ max x y → s z ≤ s (min x y)

/-- A split function is normalized if
  the minimal element of `α` receives the maximal possible rank. -/
abbrev IsNormalized [Fintype α] [Nonempty α] [Nonempty (Fin h)] (s : Split α h) : Prop :=
  let min_α := Finset.min' Finset.univ Finset.univ_nonempty
  s min_α = Finset.max' Finset.univ Finset.univ_nonempty

/-- `IsRamsey L s` holds if for any equivalence class under the split relation,
all pairs within that class evaluate to the exact same idempotent. -/
abbrev IsRamsey (L : MultiplicativeLabeling S α) (s : Split α h) : Prop :=
  (∀ x y : α, x < y → SplitRelation s x y → L.σ x y * L.σ x y = L.σ x y) ∧
  (∀ x y u v : α, x < y → u < v →
    SplitRelation s x y → SplitRelation s u v → SplitRelation s x u →
    L.σ x y = L.σ u v)

end SplitDefinitions

section WordDefinitions

/-- A multiplicative labeling induced by a word `u`,
  where `σ i j = eval(u[i..j])`. -/
abbrev wordLabeling {A S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) : MultiplicativeLabeling S (Fin (u.length + 1)) where
  σ := fun i j => eval ((u.drop i.val).take (j.val - i.val))
  prop := by
    intros x y z hxy hyz
    let u_xy := (u.drop x.val).take (y.val - x.val)
    let u_yz := (u.drop y.val).take (z.val - y.val)
    let u_xz := (u.drop x.val).take (z.val - x.val)
    have not_empty_xy_yz : u_xy ≠ [] ∧ u_yz ≠ [] := by
      simp [u_xy, u_yz]
      omega
    have concat_xy_yz_eq_xz : u_xy ++ u_yz = u_xz := by
      have index_diff_eq : z.val - x.val = (y.val - x.val) + (z.val - y.val) := by
        omega
      have drop_eq_nested_drop : u.drop y.val = (u.drop x.val).drop (y.val - x.val) := by
        simp
        grind
      grind
    grind

end WordDefinitions

section TreeDefinitions

/-- A factorization tree over an alphabet `A`. -/
inductive FactorizationTree (A : Type*)
| leaf (a : A)
| binary (left right : FactorizationTree A) (word : List A) (height : ℕ)
| nary (children : List (FactorizationTree A)) (word : List A) (height : ℕ)

/-- The word (leaf sequence) stored in a factorization tree. -/
abbrev FactorizationTree.word {A : Type*} :
    FactorizationTree A → List A
| leaf a => [a]
| binary _ _ w _ => w
| nary _ w _ => w

/-- The height of a factorization tree. -/
abbrev FactorizationTree.height {A : Type*} :
    FactorizationTree A → ℕ
| leaf _ => 0
| binary _ _ _ h => h
| nary _ _ h => h

/-- A factorization tree is Ramsey if its n-ary nodes
  all evaluate to the same idempotent. -/
inductive IsRamseyTree {A S : Type*} [Semigroup S]
    (eval : List A → S) :
    FactorizationTree A → Prop
| leaf (a : A) : IsRamseyTree eval (FactorizationTree.leaf a)
| binary (l r : FactorizationTree A) (w : List A) (h : ℕ) :
    IsRamseyTree eval l → IsRamseyTree eval r → IsRamseyTree eval (FactorizationTree.binary l r w h)
| nary (cs : List (FactorizationTree A)) (w : List A) (h : ℕ) :
    cs.length ≥ 3 → (∀ c ∈ cs, IsRamseyTree eval c) →
    (∃ (e : S), e * e = e ∧ ∀ c ∈ cs, eval (FactorizationTree.word c) = e) →
    IsRamseyTree eval (FactorizationTree.nary cs w h)

end TreeDefinitions

section nD

variable {S : Type*} [Semigroup S] [Fintype S]

open Classical in
/-- The number of elements in a D-class that are H-related to an idempotent.
Returns 2 for non-regular D-classes as a default. -/
noncomputable abbrev nD (D : Set S) : ℕ :=
  if IsRegularDClass D then
    (Finset.univ.filter (fun x ↦
      x ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH x e
    )).card
  else
    2

open Classical in
/-- The value `nD D` is strictly positive for any Green's D-class. -/
theorem nD_pos (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) : 0 < nD D := by
  dsimp [nD]
  split_ifs with hReg
  · obtain ⟨e, heD, he_idem⟩ := (isRegularDClass_iff_exists_idempotent D hD).mp hReg
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heD, e, heD, he_idem,
      IsGreenH.refl _⟩⟩
  · decide

end nD

section LabelingProperties

variable {S : Type*} [Semigroup S]

/-- The set of elements whose Green's J-class is greater than or equal to that of `a`. -/
abbrev jUp (a : S) : Set S := { b | GreenJClass.mk a ≤ GreenJClass.mk b }

/-- States that all strictly ordered pairs in the labeling `σ` map to elements in the set `U`. -/
abbrev labelingIn {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (U : Set S) : Prop :=
  ∀ x y : α, x < y → σ.σ x y ∈ U

/-- The J-class of a factor in a multiplicative labeling is
bounded below by the J-class of the product. -/
lemma labeling_factor_le_J {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (u v w x : α)
    (huv : u ≤ v) (hvw : v < w) (hwx : w ≤ x) :
    GreenJClass.mk (σ.σ u x) ≤ GreenJClass.mk (σ.σ v w) := by
  rcases huv.eq_or_lt with rfl | h_uv
  · rcases hwx.eq_or_lt with rfl | h_wx
    · exact le_rfl
    · exact (σ.prop u w x hvw h_wx).symm ▸
        (IsGreenJRel.mul_right (σ.σ w x) rfl : GreenJClass.mk _ ≤ _)
  · rcases hwx.eq_or_lt with rfl | h_wx
    · exact (σ.prop u v w h_uv hvw).symm ▸
        (IsGreenJRel.mul_left (σ.σ u v) rfl : GreenJClass.mk _ ≤ _)
    · exact (σ.prop u v x h_uv (hvw.trans h_wx)).symm ▸ (σ.prop v w x hvw h_wx).symm ▸
        le_trans (IsGreenJRel.mul_left (σ.σ u v) rfl : GreenJClass.mk _ ≤ _)
          (IsGreenJRel.mul_right (σ.σ w x) rfl : GreenJClass.mk _ ≤ _)

variable [Finite S]

/-- If the product of a prefix is D-related to an element,
then the extended product is also D-related to it. -/
lemma isGreenD_of_prefix (a : S) {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (h_img : labelingIn σ (jUp a))
    (u v w : α) (huv : u < v) (hvw : v ≤ w) (hD : IsGreenD (σ.σ u v) a) :
    IsGreenD (σ.σ u w) a := by
  rcases hvw.eq_or_lt with rfl | hvw_lt
  · exact hD
  · exact isGreenD_of_isGreenJ (GreenJClass.mk_eq_mk_iff.mp (le_antisymm
      (GreenJClass.mk_eq_mk_iff.mpr (isGreenJ_of_isGreenD hD) ▸
        labeling_factor_le_J σ u u v w le_rfl huv hvw)
      (h_img u w (huv.trans hvw_lt))))

end LabelingProperties

end FactorizationForest
