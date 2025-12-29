/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

public import Mathlib.Topology.Coherent
public import Mathlib.Topology.UnitInterval

public import Mathlib.Topology.Category.UProp
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Topology.Category.TopCat.Limits.Basic

public import Mathlib.Order.Category.Preord
public import Mathlib.Topology.Order.UpperLowerSetTopology

public import Mathlib.Data.FunLike.Fintype
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Data.Nat.EvenOddRec
public import Mathlib.Data.Fin.SuccPred

public import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.TautoSet


/-!
# Separation

The standard separation axioms in topology can be represented categorically as lifting properties.
In this file, we provide the basic definitions of the topological spaces used in this approach.

## Main definitions

We give names and a minimal API to a number of topological spaces used to define separation axioms:

* `Discrete2` is the discrete space on two points.
* `Codiscrete2` is the codiscrete space on two points.
* `Z3` is the preorder with three points `L, R ≤ 0`.
  * `O2C1` is the lower-set topology on `Z3`, the space with two open points and one closed point.
  * `O1C2` is the upper-set topology on `Z3`, space with one open point and two closed points.
* `O1N2` is the topology on three points with one open point and two inseparable points.
* `N2C1` is the topology on three points with two inseparable points and one closed point.
* `Z5` is the preorder with five points `L, M ≤ 0` and `M, R` ≤ 1.
  * `O3C2` is the lower-set topology on `Z5`, the space with three open points and two closed
    points.
  * `O2C3` is the upper-set topology on `Z5`, the space with two open points and three closed
    points.
* `OIC2` is the space formed by replacing the single open point in `O1C2` with a copy of the unit
  interval, so that `0 ⤳ L` and `1 ⤳ R`.

## Notation



## Implementation details

We have allowed convenience of usage to take precedence over consistency of internal structure for
these types. For example, `Discrete2` is usually used as a domain for maps, and so is defined as an
inductive type with two constructors so that functions out of it can be defined by pattern matching.
In contrast, `Codiscrete2` is usually used as a codomain, and so is defined as `ULift Bool` so that
the preimages of its two points can be easily described as simply `{x | (f x).down}` and
`{x | ¬(f x).down}`.


## References

* https://ncatlab.org/nlab/show/separation+axioms+in+terms+of+lifting+properties

## Tags

Foobars, barfoos
-/


@[expose] public section


/-- Prove that `a` is decidable by constructing a boolean `b` and a proof that `b ↔ a`.
(This is sometimes taken as an alternate definition of decidability.) -/
@[expose]
def decidable_of_bool' {a : Prop} : ∀ (b : Bool), (b ↔ a) → Decidable a
  | true, h => isTrue (h.1 rfl)
  | false, h => isFalse (mt h.2 Bool.noConfusion)


universe u v
open CategoryTheory Topology TopologicalSpace ContinuousMap Set
open scoped Filter

namespace TopCat
open CategoryTheory Limits

/-- The discrete space on two points. -/
inductive Discrete2 : Type u where | zero | one deriving Fintype, DecidableEq, Inhabited, Repr

instance : TopologicalSpace Discrete2 := ⊥
namespace Discrete2

instance : DiscreteTopology Discrete2 := ⟨rfl⟩

lemma «forall» {p : Discrete2 → Prop} :
    (∀ z, p z) ↔ p .zero ∧ p .one := by
  constructor
  · intro h; exact ⟨h _, h _⟩
  · rintro ⟨h₀, h₁⟩ (_ | _) <;> assumption

lemma «exists» {p : Discrete2 → Prop} :
    (∃ z, p z) ↔ p .zero ∨ p .one := by
  constructor
  · rintro ⟨z, hz⟩; cases z <;> simp [hz]
  · rintro (h | h) <;> exact ⟨_, h⟩

lemma ne : Discrete2.zero ≠ Discrete2.one := by simp

set_option linter.unusedVariables false in
/-- Construct a continuous map out of `Discrete2` with two distinct points. (Including the
distinctness requirement in the definition allows us to write more useful instances for `hom`.) -/
def hom {X} [TopologicalSpace X] (x y : X) (hxy : x ≠ y) : C(Discrete2, X) where
  toFun | .zero => x | .one => y

instance {X : TopCat} {x y : X} (hxy : x ≠ y) : Mono (ofHom <| hom x y hxy) := by
  rw [TopCat.mono_iff_injective]
  rintro (_ | _) (_ | _) h <;> {symm_saturate; simp_all [hom]}

/-- Construct a continuous map out of `Discrete2` with two arbitrary points. -/
def hom' {X} [TopologicalSpace X] (x y : X) : C(Discrete2, X) where
  toFun | .zero => x | .one => y

@[simp] lemma hom_zero {X} [TopologicalSpace X] {x y : X} (hxy : x ≠ y) :
  (hom x y hxy) .zero = x := rfl
@[simp] lemma hom_one {X} [TopologicalSpace X] {x y : X} (hxy : x ≠ y) :
  (hom x y hxy) .one = y := rfl

/-- The homeomorphism swapping the two points of `Discrete2`. -/
@[simps!]
def swap : Discrete2 ≃ₜ Discrete2 where
  toFun | .zero => .one | .one => .zero
  invFun | .zero => .one | .one => .zero
  left_inv | .zero => rfl | .one => rfl
  right_inv | .zero => rfl | .one => rfl

end Discrete2

/-- The codiscrete space on two points. -/
def Codiscrete2 : Type u := ULift Bool
  deriving Fintype, DecidableEq, Inhabited

instance : TopologicalSpace Codiscrete2 := ⊤

namespace Codiscrete2

@[match_pattern] abbrev zero : Codiscrete2 := ⟨false⟩
@[match_pattern] abbrev one : Codiscrete2 := ⟨true⟩

@[ext]
lemma ext {x y : Codiscrete2} (h : x.down = y.down) : x = y := by cases x; cases y; congr

@[simp, elab_as_elim, cases_eliminator, induction_eliminator]
def cases {C : Codiscrete2 → Sort v}
    (h0 : C .zero) (h1 : C .one) : (x : Codiscrete2) → C x
| .zero => h0 | .one => h1

instance : CodiscreteTopology Codiscrete2 := ⟨rfl⟩


lemma «forall» {p : Codiscrete2 → Prop} :
    (∀ z, p z) ↔ p .zero ∧ p .one := by
  constructor
  · intro h; exact ⟨h _, h _⟩
  · rintro ⟨h₀, h₁⟩ (_ | _) <;> assumption

lemma «exists» {p : Codiscrete2 → Prop} :
    (∃ z, p z) ↔ p .zero ∨ p .one := by
  constructor
  · rintro ⟨⟨⟨⟩⟩, hz⟩ <;> simp [hz]
  · rintro (h | h) <;> exact ⟨_, h⟩

lemma ne : Codiscrete2.zero ≠ Codiscrete2.one := by simp [ULift.ext_iff, Codiscrete2]

/-- For any continuous map `f : C(Codiscrete2, X)`, the points `f .zero` and `f .one` are
inseparable. (For the definition witnessing that this condition is sufficient to construct a
continuous map, see `Codiscrete2.homOfInseparable`.) -/
lemma inseparable {X : TopCat} (f : C(Codiscrete2, X)) : Inseparable (f .zero) (f .one) :=
  continuous_codiscrete_dom _ |>.mp f.continuous _ _

/-- A continuous map out of `Codiscrete2` can be made from any pair of inseparable points.
(For the fact that any such map is of this form, see `Codiscrete2.inseparable`.) -/
def homOfInseparable {X : TopCat} {x y : X} (hxy : Inseparable x y) : C(Codiscrete2, X) where
  toFun | .zero => x | .one => y
  continuous_toFun := by
    rw [continuous_codiscrete_dom]
    rintro (_ | _) (_ | _) <;> simp [Inseparable.rfl, hxy, hxy.symm]

@[simp]
lemma homOfInseparable_apply_zero {X : TopCat} (x y : X) (hxy : Inseparable x y) :
    (homOfInseparable hxy) .zero = x := rfl

@[simp]
lemma homOfInseparable_apply_one {X : TopCat} (x y : X) (hxy : Inseparable x y) :
    (homOfInseparable hxy) .one = y := rfl

/-- The homeomorphism swapping the two points of `Codiscrete2`. -/
@[simps!]
def swap : Codiscrete2 ≃ₜ Codiscrete2 where
  toFun | .zero => .one | .one => .zero
  invFun | .zero => .one | .one => .zero
  left_inv | .zero => rfl | .one => rfl
  right_inv | .zero => rfl | .one => rfl
  continuous_toFun := by continuity
  continuous_invFun := by continuity

end Codiscrete2

/-- The preorder `L, R ≤ 0`. Taking the lower-set topology gives us `O2C1`; the upper-set topology,
`O1C2`. -/
inductive Z3 : Type u where | zero | left | right deriving Fintype, DecidableEq, Inhabited, Repr

namespace Z3
@[mk_iff]
inductive spec : Z3 → Z3 → Prop where
  | refl (x) : spec x x
  | left_zero : spec left zero
  | right_zero : spec right zero

attribute [refl] spec.refl

@[simps]
instance : Preorder Z3 where
  le := spec
  le_refl := spec.refl
  le_trans {x y z} := by rintro ⟨⟩ ⟨⟩ <;> constructor

instance : DecidableRel spec := fun x y ↦
  decidable_of_bool' (match x, y with
    | .left, .zero => true
    | .right, .zero => true
    | _ , _ => x == y)
  (by casesm* Z3 <;> simp [spec_iff])

instance : DecidableLE Z3 := inferInstanceAs (DecidableRel spec)

lemma «forall» {p : Z3 → Prop} : (∀ z, p z) ↔ p .left ∧ p .zero ∧ p .right := by
  constructor
  · intro h; exact ⟨h _, h _, h _⟩
  · rintro ⟨hL, h0, hR⟩ (_ | _ | _) <;> assumption

lemma «exists» {p : Z3 → Prop} : (∃ z, p z) ↔ p .left ∨ p .zero ∨ p .right := by
  constructor
  · rintro ⟨z, hz⟩; cases z <;> simp [hz]
  · rintro (h | h | h) <;> exact ⟨_, h⟩

end Z3

/-- The topology `L ⟶ 0 ⟵ R` with two open points and one closed point. -/
inductive O2C1 : Type u where | as (x : Z3) deriving DecidableEq, Inhabited

namespace O2C1
open Function

@[match_pattern] abbrev left : O2C1 := as Z3.left
@[match_pattern] abbrev zero : O2C1 := as Z3.zero
@[match_pattern] abbrev right : O2C1 := as Z3.right

@[elab_as_elim, cases_eliminator, induction_eliminator, simp]
def casesOn' {C : O2C1 → Sort*} (x : O2C1)
    (zero : C zero) (left : C left) (right : C right) : C x :=
  x.casesOn (Z3.casesOn · zero left right)

@[simps]
def equivZ3 : O2C1 ≃ Z3 where
  toFun | as x => x
  invFun | x => as x

instance : Preorder O2C1 := .lift equivZ3
instance : TopologicalSpace O2C1 := Topology.lowerSet _

lemma le_def (x y : O2C1) : x ≤ y ↔ Z3.spec x.1 y.1 := by rfl

instance : DecidableRel (@Specializes O2C1 _) := fun x y ↦
  decidable_of_iff (x.1 ≤ y.1) (by simp [IsLowerSet.specializes_iff_le, le_def])

instance : DecidableLE O2C1 := fun x y ↦
  decidable_of_iff (x.1 ≤ y.1) (by simp [le_def])

lemma «forall» {p : O2C1 → Prop} : (∀ z, p z) ↔ p .left ∧ p .zero ∧ p .right := by
  simp [equivZ3.forall_congr_left, Z3.forall]

lemma «exists» {p : O2C1 → Prop} : (∃ z, p z) ↔ p .left ∨ p .zero ∨ p .right := by
  simp [equivZ3.exists_congr_left, Z3.exists]

@[simp] lemma isOpen_left : IsOpen {left} := by
  rw [IsLowerSet.isOpen_iff_isLowerSet, IsLowerSet]; rintro ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩; constructor

@[simp] lemma isOpen_right : IsOpen {right} := by
  rw [IsLowerSet.isOpen_iff_isLowerSet, IsLowerSet]; rintro ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩; constructor

@[simp] lemma isClosed_zero : IsClosed {zero} := by
  rw [IsLowerSet.isClosed_iff_isUpper, IsUpperSet]; rintro ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩; constructor

@[simp] lemma specializes_left_zero : left ⤳ zero := by decide
@[simp] lemma specializes_right_zero : right ⤳ zero := by decide

lemma basis : IsTopologicalBasis {univ, {left}, {right}} := by
  fapply isTopologicalBasis_of_isOpen_of_nhds (by simp)
  intro x; cases x <;> intro u hu uO
  · simp; simpa [eq_univ_iff_forall] using fun x ↦ x.casesOn' hu
      (specializes_left_zero.mem_open uO hu) (specializes_right_zero.mem_open uO hu)
  all_goals simp [hu]

def πL : of O2C1 ⟶ of UProp := isOpen_left.toHom
def πR : of O2C1 ⟶ of UProp := isOpen_right.toHom

section preimage
variable {X} [TopologicalSpace X]
variable (f : C(X, O2C1))

end preimage

section lift

open scoped Classical in
/-- A morphism into `O2C1` can be constructed from a pair of disjoint open sets. -/
noncomputable abbrev lift {X : TopCat} {s t : Set X}
    (hs : IsOpen s) (ht : IsOpen t) (h : Disjoint s t) : X ⟶ of O2C1 :=
  ofHom (map hs ht h)
where
  map {X} [TopologicalSpace X]
    {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) (h : Disjoint s t) : C(X, O2C1) :=
{ toFun x := if x ∈ s then O2C1.left else if x ∈ t then O2C1.right else O2C1.zero
  continuous_toFun := by
    rw [O2C1.basis.continuous_iff]
    rintro s (rfl | rfl | rfl)
    · simp
    all_goals rw [← setOf_eq_eq_singleton, preimage_setOf_eq]
    · conv in _ = _  => tactic => change _ = (a ∈ s); split_ifs <;> simpa [O2C1]
      exact hs
    · conv in _ = _  => tactic =>
        change _ = (a ∈ t)
        split_ifs
        · simpa [O2C1] using h.notMem_of_mem_left ‹_›
        all_goals simpa [O2C1]
      exact ht }

variable {X} [TopologicalSpace X] {s t : Set X} {hs : IsOpen s} {ht : IsOpen t} {h : Disjoint s t}

@[simp]
lemma lift_eq_left_iff {x : X} : lift.map hs ht h x = O2C1.left ↔ x ∈ s where
  mp h := by simpa [O2C1, lift.map, mk_apply, ite_eq_iff] using h
  mpr h₁ := by simp only [lift.map, mk_apply, ite_eq_left_iff]; split_ifs with h₂ <;> simp [h₁]

alias ⟨_, lift_eq_left⟩ := lift_eq_left_iff

@[simp]
lemma lift_eq_right_iff {x : X} : lift.map hs ht h x = O2C1.right ↔ x ∈ t where
  mp h := by simp_all [lift.map, ite_eq_iff]
  mpr h₁ := by
    simp only [lift.map, mk_apply]
    split_ifs with h₂
    · exfalso; exact h.notMem_of_mem_right h₁ h₂
    · rfl

alias ⟨_, lift_eq_right⟩ := lift_eq_right_iff

@[simp]
lemma lift_eq_zero_iff {x : X} : lift.map hs ht h x = O2C1.zero ↔ x ∉ s ∧ x ∉ t where
  mp h := by simp only [lift.map, mk_apply] at h; split_ifs at h with h₁ h₂ <;> simp_all
  mpr | ⟨h₁, h₂⟩ => by simp only [lift.map, mk_apply]; split_ifs; simp_all

lemma lift_eq_zero {x : X} (h₁ : x ∉ s) (h₂ : x ∉ t) :
    lift.map hs ht h x = O2C1.zero := by
  simp only [lift.map, mk_apply]; split_ifs; rfl

open scoped Classical in
@[simp low]
lemma lift_eq {x : X} : lift.map hs ht h x =
    if x ∈ s then O2C1.left else if x ∈ t then O2C1.right else O2C1.zero := rfl

@[simp]
lemma preimage_lift_left : lift.map hs ht h ⁻¹' {left} = s := by
  ext x
  rw [mem_preimage, mem_singleton_iff]
  constructor <;> intro h
  · by_contra! h!
    simp [lift.map, mk_apply, h!, ite_eq_iff] at h
  · exact lift_eq_left h

@[simp]
lemma preimage_lift_right : lift.map hs ht h ⁻¹' {right} = t := by
  ext x
  rw [mem_preimage, mem_singleton_iff]
  constructor <;> intro h
  · by_contra! h!
    simp [lift.map, mk_apply, h!, ite_eq_iff] at h
  · exact lift_eq_right h

/-- The homeomorphism that swaps `left` and `right`. -/
def swap : O2C1 ≃ₜ O2C1 :=
  let toFun : C(O2C1, O2C1) :=
    { toFun x := x.casesOn' O2C1.zero O2C1.right O2C1.left
      continuous_toFun := by
        rw [O2C1.basis.continuous_iff]
        rintro s (rfl | rfl | rfl)
        · simp
        · convert isOpen_right; ext ⟨⟨⟩⟩ <;> simp
        · convert isOpen_left; ext ⟨⟨⟩⟩ <;> simp }
{ toFun
  invFun := toFun
  left_inv x := by rcases x with ⟨⟨⟩⟩ <;> rfl
  right_inv x := by rcases x with ⟨⟨⟩⟩ <;> rfl
  continuous_toFun := toFun.continuous_toFun
  continuous_invFun := toFun.continuous_toFun }

@[simp] lemma swap_apply (x : O2C1) : swap x = x.casesOn' O2C1.zero O2C1.right O2C1.left := rfl

@[simp] lemma swap_symm : swap.symm = swap := rfl

end lift

@[simp↓]
lemma comp_πL_eq_iff {X : TopCat.{u}} {f g : X ⟶ of O2C1} :
    f ≫ O2C1.πL = g ≫ O2C1.πL ↔ ∀ x, f x = O2C1.left ↔ g x = O2C1.left := by
  simp [O2C1.πL, Set.ext_iff]

@[simp↓]
lemma comp_πR_eq_iff {X : TopCat.{u}} {f g : X ⟶ of O2C1} :
    f ≫ O2C1.πR = g ≫ O2C1.πR ↔ ∀ x, f x = O2C1.right ↔ g x = O2C1.right := by
  simp [O2C1.πR, Set.ext_iff]

@[ext]
lemma hom_ext {X : TopCat} {f g : X ⟶ of O2C1}
    (hL : f ≫ O2C1.πL = g ≫ O2C1.πL) (hR : f ≫ O2C1.πR = g ≫ O2C1.πR) : f = g := by
  ext x
  simp only [comp_πL_eq_iff, comp_πR_eq_iff] at hL hR
  specialize hL x; specialize hR x
  generalize hy : f x = y, hz : g x = z at *; change O2C1 at y z
  cases y <;> cases z <;> simp_all

end O2C1

/-- The indicator function from `Discrete2` to `O2C1`, sending zero to left and one to right.
A space `X` is `T2` iff every mono `Discrete 2 ⟶ X` arises as a factorization of this map. -/
@[simps]
def disjointNhdsIndicator : C(Discrete2, O2C1) where
  toFun | .zero => .left | .one => .right

/-- The left embedding of `UProp` into `O2C1`. -/
noncomputable def uPropToO2C1L : of UProp ⟶ of O2C1 :=
  UProp.desc O2C1.specializes_left_zero

/-- The right embedding of `UProp` into `O2C1`. -/
noncomputable def uPropToO2C1R : of UProp ⟶ of O2C1 :=
  UProp.desc O2C1.specializes_right_zero

@[reassoc]
lemma uPropToO2C1L_swap : uPropToO2C1L.{u} ≫ (isoOfHomeo O2C1.swap).hom = uPropToO2C1R := by
  apply ConcreteCategory.coe_ext; rw [UProp.funext_iff]
  simp [uPropToO2C1R, uPropToO2C1L, Hom.hom, TopCat.coe_of]

/-- `uPropToO2C1L` is a closed embedding.. -/
lemma uPropToO2C1L_isClosedEmbedding : IsClosedEmbedding uPropToO2C1L.{u} where
  eq_induced := by
    ext s
    constructor
    · intro hs
      rw [UProp.isOpen_iff_empty_or_top_mem] at hs
      rcases hs with rfl | hT
      · exact @isOpen_empty _ (induced _ _)
      · rw [isOpen_induced_iff]
        by_cases hF : ⊥ ∈ s
        · obtain rfl : s = univ := by ext <;> simp_all
          use univ, isOpen_univ; exact preimage_univ
        · obtain rfl : s = {⊤} := by ext <;> simp_all
          use {O2C1.left}, O2C1.isOpen_left; ext <;> simp [uPropToO2C1L]
    · revert s
      change (_ : TopologicalSpace _) ≤ _
      apply Continuous.le_induced uPropToO2C1L.continuous
  injective := by
    unfold Function.Injective
    simp [uPropToO2C1L]
  isClosed_range := by
    rw [← isOpen_compl_iff]
    convert O2C1.isOpen_right
    ext ⟨⟨⟩⟩ <;> simp [uPropToO2C1L]

/-- `uPropToO2C1R` is a closed embedding. -/
lemma uPropToO2C1R_isClosedEmbedding : IsClosedEmbedding uPropToO2C1R.{u} := by
  simpa [← uPropToO2C1L_swap] using
    IsClosedEmbedding.comp O2C1.swap.isClosedEmbedding uPropToO2C1L_isClosedEmbedding

namespace O2C1

/-- A continuous map out of `O2C1` can be made from any pair of points that both specialize
to the same point. -/
abbrev desc {X : TopCat.{u}} {x y z : X} (hx : x ⤳ z) (hy : y ⤳ z) : of O2C1 ⟶ X :=
  ofHom (map hx hy)
where
  map {X : Type u} [TopologicalSpace X] {x y z : X} (hx : x ⤳ z) (hy : y ⤳ z) : C(O2C1, X) :=
    let toFun : O2C1 → X | .zero => z | .left => x | .right => y
  { toFun
    continuous_toFun := by
      fconstructor; intro s hs
      rw [O2C1.basis.isOpen_iff]
      have hz : z ∈ s → range toFun ⊆ s := by
        rintro hz _ ⟨a, rfl⟩; cases a
        all_goals
          have : x ∈ s := hx.mem_open hs hz
          have : y ∈ s := hy.mem_open hs hz
          simp_all [toFun]
      simp +contextual [O2C1.forall, toFun, hz] }

@[simp]
lemma desc_apply_left {X : TopCat} {x y z : X} (hx : x ⤳ z) (hy : y ⤳ z) :
    desc.map hx hy O2C1.left = x := rfl

@[simp]
lemma desc_apply_right {X : TopCat} {x y z : X} (hx : x ⤳ z) (hy : y ⤳ z) :
    desc.map hx hy O2C1.right = y := rfl

@[simp]
lemma desc_apply_zero {X : TopCat} {x y z : X} (hx : x ⤳ z) (hy : y ⤳ z) :
    desc.map hx hy O2C1.zero = z := rfl

lemma specializes_of_hom_left {X : TopCat} (f : of O2C1 ⟶ X) : f .left ⤳ f .zero := by
  exact Specializes.map specializes_left_zero f.continuous

lemma specializes_of_hom_right {X : TopCat} (f : of O2C1 ⟶ X) : f .right ⤳ f .zero := by
  exact Specializes.map specializes_right_zero f.continuous

end O2C1

/-- The topology `L ⟵ 1 ⟶ R` with two closed points and one open point. -/
inductive O1C2 : Type u where | as (x : Z3)
  deriving DecidableEq, Inhabited
-- def O1C2 : Type u := WithUpperSet Z3
--   deriving Inhabited, Fintype, DecidableEq, Preorder, DecidableLE, TopologicalSpace, Repr

namespace O1C2

@[match_pattern] abbrev one : O1C2 := .as Z3.zero
@[match_pattern] abbrev left : O1C2 := .as Z3.left
@[match_pattern] abbrev right : O1C2 := .as Z3.right


@[elab_as_elim, cases_eliminator, induction_eliminator, simp]
def casesOn' {C : O1C2 → Sort*} (x : O1C2) (one : C one) (left : C left) (right : C right) : C x :=
  x.casesOn (Z3.casesOn · one left right)

@[simps]
def equivZ3 : O1C2 ≃ Z3 where
  toFun | as x => x
  invFun | x => as x

instance : Preorder O1C2 := .lift equivZ3
instance : TopologicalSpace O1C2 := Topology.upperSet _

lemma le_def (x y : O1C2) : x ≤ y ↔ Z3.spec x.1 y.1 := by rfl

instance : DecidableRel (@Specializes O1C2 _) := fun x y ↦
  decidable_of_iff (equivZ3 y ≤ equivZ3 x) (by simp [IsUpperSet.specializes_iff_le, le_def])

instance : DecidableLE O1C2 := fun x y ↦
  decidable_of_iff (equivZ3 x ≤ equivZ3 y) (by simp [le_def])

@[ext]
lemma funext {α} {f g : O1C2 → α}
    (h₀ : f one = g one) (h₁ : f left = g left) (h₂ : f right = g right) : f = g := by
  ext x; cases x <;> simp_all

@[ext]
lemma set_ext {s t : Set O1C2}
    (h₀ : one ∈ s ↔ one ∈ t) (h₁ : left ∈ s ↔ left ∈ t) (h₂ : right ∈ s ↔ right ∈ t) : s = t := by
  ext x; cases x <;> simp_all

@[simp] lemma specializes_one_left : one ⤳ left := by decide
@[simp] lemma specializes_one_right : one ⤳ right := by decide

@[simp]
lemma isOpen_one : IsOpen {one} := by
  simp_rw [IsUpperSet.isOpen_iff_isUpperSet]
  rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩ ⟨⟩; rfl

@[simp]
lemma isClosed_left : IsClosed {left} := by
  rw [IsUpperSet.isClosed_iff_isLower, IsLowerSet]
  rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩ ⟨⟩; rfl

@[simp]
lemma isClosed_right : IsClosed {right} := by
  rw [IsUpperSet.isClosed_iff_isLower, IsLowerSet]
  rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩ ⟨⟩; rfl

@[simp]
lemma isClosed_left_right : IsClosed {left, right} := by
  rw [← isOpen_compl_iff]; convert isOpen_one; ext <;> simp

lemma isOpen_nonempty_iff_one_mem {s : Set O1C2} (h₀ : s.Nonempty) : IsOpen s ↔ one ∈ s where
  mp hs := by
    rcases h₀ with ⟨_ | _ | _, h₀⟩
    · exact h₀
    · exact specializes_one_left.mem_open hs h₀
    · exact specializes_one_right.mem_open hs h₀
  mpr hs := by
    match em (left ∈ s), em (right ∈ s) with
    | .inl hL, .inl hR => convert isOpen_univ; ext <;> simpa
    | .inl hL, .inr hR =>
      rw [← isClosed_compl_iff]
      have : sᶜ = {right} := by ext <;> simpa [O1C2]
      simp [this]
    | .inr hL, .inl hR =>
      rw [← isClosed_compl_iff]
      have : sᶜ = {left} := by ext <;> simpa [O1C2]
      simp [this]
    | .inr hL, .inr hR =>
      obtain rfl : s = {one} := by ext <;> simpa [O1C2]
      exact isOpen_one

lemma isOpen_iff_empty_or_one_mem {s : Set O1C2} :
    IsOpen s ↔ s = ∅ ∨ one ∈ s := by
  rcases em (s = ∅) with rfl | h₀
  · simp
  · simp [isOpen_nonempty_iff_one_mem (nonempty_iff_ne_empty.mpr h₀), h₀]

lemma continuous_iff_specializes {X} [TopologicalSpace X] {f : O1C2 → X} :
    Continuous f ↔ f one ⤳ f left ∧ f one ⤳ f right where
  mp hf := ⟨specializes_one_left.map hf, specializes_one_right.map hf⟩
  mpr h := by
    constructor
    intro s hs
    by_cases h₀ : (f ⁻¹' s).Nonempty
    · rw [isOpen_nonempty_iff_one_mem h₀]
      rcases h₀ with ⟨x, hx⟩
      cases x with
      | one => assumption
      | left => exact h.1.mem_open hs hx
      | right => exact h.2.mem_open hs hx
    · simp [not_nonempty_iff_eq_empty] at h₀; simp [h₀]

abbrev desc {X : TopCat} {x y z : X} (hy : x ⤳ y) (hz : x ⤳ z) : of O1C2 ⟶ X :=
  ofHom (map hy hz)
where
  map {X : Type u} [TopologicalSpace X] {x y z : X} (hy : x ⤳ y) (hz : x ⤳ z) : C(O1C2, X) :=
    let toFun a := O1C2.casesOn' a x y z
  { toFun
    continuous_toFun := by simp [continuous_iff_specializes, toFun, hy, hz] }

@[simp]
lemma desc_apply_left {X} [TopologicalSpace X] {x y z : X} (hy : x ⤳ y) (hz : x ⤳ z) :
    desc.map hy hz O1C2.left = y := rfl

@[simp]
lemma desc_apply_one {X} [TopologicalSpace X] {x y z : X} (hy : x ⤳ y) (hz : x ⤳ z) :
    desc.map hy hz O1C2.one = x := rfl

@[simp]
lemma desc_apply_right {X} [TopologicalSpace X] {x y z : X} (hy : x ⤳ y) (hz : x ⤳ z) :
    desc.map hy hz O1C2.right = z := rfl

lemma specializes_of_hom_left {X} [TopologicalSpace X] (f : C(O1C2, X)) : f one ⤳ f left := by
  exact Specializes.map specializes_one_left f.continuous

lemma specializes_of_hom_right {X} [TopologicalSpace X] (f : C(O1C2, X)) : f one ⤳ f right := by
  exact Specializes.map specializes_one_right f.continuous

lemma not_disjoint_nhds {X} [TopologicalSpace X] (f : C(O1C2, X)) :
    ¬ Disjoint (𝓝 (f left)) (𝓝 (f right)) := by
  rw [disjoint_iff_inf_le, le_bot_iff]; intro h
  have hL := specializes_of_hom_left f
  have hR := specializes_of_hom_right f
  have := le_inf hL hR
  simp [h, le_bot_iff, nhds_neBot.ne] at this

lemma basis : IsTopologicalBasis {{one}, {one, left}, {one, right}} := by
  fapply isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ (rfl | rfl | rfl)
    · exact isOpen_one
    · rw [← isClosed_compl_iff]
      convert isClosed_right; ext <;> simp
    · rw [← isClosed_compl_iff]
      convert isClosed_left; ext <;> simp
  · intro x s hs hxs
    rw [isOpen_iff_empty_or_one_mem] at hxs; rcases hxs with rfl | hxs
    · simp at hs
    · cases x using O1C2.casesOn'
      · use {one}; simp [hs]
      · use {one, left}; simp [insert_subset_iff, hxs, hs]
      · use {one, right}; simp [insert_subset_iff, hxs, hs]


end O1C2

/-- The left embedding of `UProp` into `O1C2`. -/
noncomputable def uPropToO1C2L : of UProp ⟶ of O1C2 :=
  UProp.desc O1C2.specializes_one_left

/-- The right embedding of `UProp` into `O1C2`. -/
noncomputable def uPropToO1C2R : of UProp ⟶ of O1C2 :=
  UProp.desc O1C2.specializes_one_right

namespace O1C2

open scoped Classical Set.Notation in
/-- A morphism into `O1C2` can be constructed from a pair of disjoint closed sets. -/
noncomputable abbrev lift {X : TopCat} {U V : Set X} (hU : IsClosed U) (hV : IsClosed V)
    (hUV : Disjoint U V) : X ⟶ of O1C2 :=
  ofHom <| map hU hV hUV
where
  map {X : Type u} [TopologicalSpace X] {U V : Set X} (hU : IsClosed U) (hV : IsClosed V)
      (hUV : Disjoint U V) : C(X, O1C2) :=
    IsCoherentWith.liftPair hU.isOpen_compl hV.isOpen_compl
      (by simpa [disjoint_iff_inter_eq_empty, ← compl_univ_iff, compl_inter] using hUV)
      (hV.preimage_val.toHom' ≫ uPropToO1C2R).hom (hU.preimage_val.toHom' ≫ uPropToO1C2L).hom
      fun x hxU hxV => by
        have hxU' : ⟨x, hxV⟩ ∈ Vᶜ ↓∩ Uᶜ := by simp at hxU; simp [hxU]
        have hxV' : ⟨x, hxU⟩ ∈ Uᶜ ↓∩ Vᶜ := by simp at hxV; simp [hxV]
        simp [hU.preimage_val.toHom_apply_of_notMem hxU', uPropToO1C2L, uPropToO1C2R,
        hV.preimage_val.toHom_apply_of_notMem hxV']

open scoped Classical Set.Notation in
@[simp]
lemma lift_apply {X} [TopologicalSpace X] {U V : Set X} {hU : IsClosed U} {hV : IsClosed V}
    {hUV : Disjoint U V} (x : X) :
    lift.map hU hV hUV x =
      if x ∈ U then O1C2.left else if x ∈ V then O1C2.right else O1C2.one := by
  split_ifs with hxU hxV
  · have : x ∈ Vᶜ := hUV.notMem_of_mem_left hxU
    have hxU' : ⟨x, this⟩ ∈ Vᶜ ↓∩ U := by simp [hxU]
    simp [lift.map, IsCoherentWith.liftPair_apply_of_mem_right this, uPropToO1C2L,
    hU.preimage_val.toHom_apply_of_mem hxU']
  · have hxV' : ⟨x, hxU⟩ ∈ Uᶜ ↓∩ V := by simp [hxV]
    rw [← mem_compl_iff] at hxU
    simp [lift.map, IsCoherentWith.liftPair_apply_of_mem_left hxU, uPropToO1C2R,
    hV.preimage_val.toHom_apply_of_mem hxV']
  · rw [← mem_compl_iff] at hxU
    have hxV' : ⟨x, hxU⟩ ∉ Uᶜ ↓∩ V := by simp [hxV]
    simp [lift.map, IsCoherentWith.liftPair_apply_of_mem_left hxU, uPropToO1C2R,
    hV.preimage_val.toHom_apply_of_notMem hxV']

  -- <;> simp [lift.map, IsCoherentWith.liftPair_apply_of_mem_left ‹_›]
@[simp]
lemma preimage_lift_left {X} [TopologicalSpace X] {U V : Set X} (hU : IsClosed U)
    (hV : IsClosed V) (hUV : Disjoint U V) :
    lift.map hU hV hUV ⁻¹' {O1C2.left} = U := by
  ext; simp [ite_eq_iff]

@[simp]
lemma preimage_lift_right {X} [TopologicalSpace X] {U V : Set X} (hU : IsClosed U)
    (hV : IsClosed V) (hUV : Disjoint U V) :
    lift.map hU hV hUV ⁻¹' {O1C2.right} = V := by
  ext; simp +contextual [ite_eq_iff, hUV.notMem_of_mem_right]

@[simp]
lemma preimage_lift_one {X} [TopologicalSpace X] {U V : Set X} (hU : IsClosed U)
    (hV : IsClosed V) (hUV : Disjoint U V) :
    lift.map hU hV hUV ⁻¹' {O1C2.one} = (U ∪ V)ᶜ := by
  ext x; simp +contextual [ite_eq_iff]

end O1C2

/-- The topology
```
    L ⟵ ⟶ R
      🡖   🡗
        0
```
with one closed point and two inseparable points. -/
inductive N2C1 : Type u where | zero | left | right deriving Fintype, DecidableEq, Inhabited, Repr

namespace N2C1

instance : TopologicalSpace N2C1 := generateFrom {{left, right}}

@[simp]
lemma isOpen_one : IsOpen {left, right} := .basic _ (by simp)

@[simp]
lemma isClosed_zero : IsClosed {zero} := by
  rw [← isOpen_compl_iff]
  convert isOpen_one using 1
  ext (_ | _ | _) <;> simp

lemma nhds_zero : 𝓝 zero = ⊤ := by
  rw [nhds_generateFrom]
  simp only [mem_singleton_iff, mem_setOf_eq, iInf_eq_top, and_imp]
  rintro _ h₀ rfl; simp at h₀

lemma specializes_left_zero : left ⤳ zero := by
  simp [Specializes, nhds_generateFrom, ↓nhds_zero]

lemma specializes_right_zero : right ⤳ zero := by
  simp [Specializes, nhds_generateFrom, ↓nhds_zero]

lemma basis : IsTopologicalBasis {univ, {left, right}} where
  exists_subset_inter := by simp
  sUnion_eq := by simp
  eq_generateFrom := by simp; rfl

lemma inseparable_left_right : Inseparable left right := by
  simp [inseparable_iff_mem_closure, basis.mem_closure_iff]

/-- A hom from `N2C1` can be made from a pair of inseparable points and a third point which
generalizes to either, thus both. -/
abbrev homOfSpecializesInseparable {X : TopCat.{u}} {x y z : X}
    (h₁ : Inseparable x y) (h₂ : x ⤳ z) : of N2C1 ⟶ X :=
  ofHom (map h₁ h₂)
where
  map {X} [TopologicalSpace X] {x y z : X} (h₁ : Inseparable x y) (h₂ : x ⤳ z) : C(N2C1, X) :=
    let toFun : N2C1.{u} → X | .left => x | .zero => z | .right => y
  { toFun
    continuous_toFun := by
      constructor; intro s hs
      rw [N2C1.basis.isOpen_iff]
      rintro (_ | _ | _) hs'
      · use univ, mem_insert _ _, mem_univ _
        rintro (_ | _ | _) - <;> simp_all [toFun, h₂.mem_open hs, ← h₁.mem_open_iff hs]
      all_goals
      · use {left, right}, by simp, by simp
        rintro _ (rfl | rfl) <;>
          { simp [toFun] at hs'; simp_all [toFun, ↓h₁.mem_open_iff hs] }}

section
variable {X : TopCat} {x y z : X} (h₁ : Inseparable x y) (h₂ : x ⤳ z)

@[simp]
lemma homOfSpecializesInseparable_apply_left :
  homOfSpecializesInseparable.map h₁ h₂ N2C1.left = x := rfl

@[simp]
lemma homOfSpecializesInseparable_apply_right :
  homOfSpecializesInseparable.map h₁ h₂ N2C1.right = y := rfl

@[simp]
lemma homOfSpecializesInseparable_apply_zero :
  homOfSpecializesInseparable.map h₁ h₂ N2C1.zero = z := rfl

lemma specializes_of_hom_left (f : of N2C1 ⟶ X) : f left ⤳ f zero := by
  exact Specializes.map specializes_left_zero f.continuous

lemma specializes_of_hom_right (f : of N2C1 ⟶ X) : f right ⤳ f zero := by
  exact Specializes.map specializes_right_zero f.continuous

lemma inseparable_of_hom (f : of N2C1 ⟶ X) : Inseparable (f left) (f right) := by
  exact Inseparable.map inseparable_left_right f.continuous
end

end N2C1

/-- The topology
```
        1
      🡗   🡖
    L ⟵ ⟶ R
```
with one open point and two inseparable points. -/
inductive O1N2 : Type u where | left | one | right deriving Fintype, DecidableEq, Inhabited, Repr

namespace O1N2

instance : TopologicalSpace O1N2 := generateFrom {{.one}}

@[simp]
lemma isOpen_one : IsOpen {one} := .basic _ (by simp)

@[simp]
lemma nhds_left : 𝓝 left = ⊤ := by
  rw [nhds_generateFrom]
  simp +contextual [and_comm (b := _ = {one})]

@[simp]
lemma nhds_right : 𝓝 right = ⊤ := by
  rw [nhds_generateFrom]
  simp +contextual [and_comm (b := _ = {one})]

lemma specializes_one_left : one ⤳ left := by simp [Specializes]
lemma specializes_one_right : one ⤳ right := by simp [Specializes]

lemma inseparable_left_right : Inseparable left right := by
  unfold Inseparable; simp

lemma basis : IsTopologicalBasis {univ, {one}} where
  exists_subset_inter := by simp
  sUnion_eq := by simp
  eq_generateFrom := by simp; rfl

/-- A hom from `O1N2`- can be made from a pair of inseparable points and a third point which
specializes to either, thus both. -/
abbrev homOfSpecializesInseparable {X : TopCat.{u}} {x y z : X}
    (h₁ : x ⤳ y) (h₂ : Inseparable y z) : of O1N2 ⟶ X :=
  ofHom (map h₁ h₂)
where
  map {X} [TopologicalSpace X] {x y z : X} (h₁ : x ⤳ y) (h₂ : Inseparable y z) : C(O1N2, X) :=
    let toFun : O1N2.{u} → X | .left => y | .one => x | .right => z
  { toFun
    continuous_toFun := by
      constructor; intro s hs
      rw [O1N2.basis.isOpen_iff]
      have : z ∈ s ∨ y ∈ s → toFun ⁻¹' s = univ := by
        rintro (hz | hy)
        focus have : y ∈ s := h₂.mem_open_iff hs |>.mpr hz
        all_goals
          have : x ∈ s := h₁.mem_open hs ‹_›
          ext (_ | _ | _) <;> simp [toFun, *, ← h₂.mem_open_iff hs]
      rintro (_ | _ | _) hs'
      rotate_left
      · use {one}, by simp, mem_singleton one, by simpa using hs'
      all_goals
      · use univ, by simp, mem_univ _
        simp [toFun] at hs'; simp [this, hs'] }

@[simp]
lemma homOfSpecializesInseparable_apply_left {X : TopCat} {x y z : X} (h₁ : x ⤳ y)
    (h₂ : Inseparable y z) : homOfSpecializesInseparable.map h₁ h₂ O1N2.left = y := rfl

@[simp]
lemma homOfSpecializesInseparable_apply_one {X : TopCat} {x y z : X} (h₁ : x ⤳ y)
    (h₂ : Inseparable y z) : homOfSpecializesInseparable.map h₁ h₂ O1N2.one = x := rfl

@[simp]
lemma homOfSpecializesInseparable_apply_right {X : TopCat} {x y z : X} (h₁ : x ⤳ y)
    (h₂ : Inseparable y z) : homOfSpecializesInseparable.map h₁ h₂ O1N2.right = z := rfl

lemma specializes_of_hom_left {X : TopCat} (f : of O1N2 ⟶ X) : f one ⤳ f left := by
  exact Specializes.map specializes_one_left f.continuous

lemma specializes_of_hom_right {X : TopCat} (f : of O1N2 ⟶ X) : f one ⤳ f right := by
  exact Specializes.map specializes_one_right f.continuous

lemma inseparable_of_hom {X : TopCat} (f : of O1N2 ⟶ X) : Inseparable (f left) (f right) := by
  exact Inseparable.map inseparable_left_right f.continuous

end O1N2

/-- The preorder `L, M ≤ 0`, `M, R ≤ 1`. Putting the lower set topology on this gives `O3C2`;
putting the upper set topology on this gives `O2C3`. -/
inductive Z5 : Type u where | left | zero | mid | one | right
  deriving Fintype, DecidableEq, Inhabited, Repr
namespace Z5
@[mk_iff]
inductive spec : Z5 → Z5 → Prop where
  | refl x : spec x x
  | left_zero : spec .left .zero
  | mid_zero : spec .mid .zero
  | mid_one : spec .mid .one
  | right_one : spec .right .one

attribute [refl] spec.refl

@[simps]
instance : Preorder Z5 where
  le := spec
  le_refl := spec.refl
  le_trans a b c h₁ h₂ := by
    casesm* Z5, spec _ _
    all_goals simp [spec_iff]

instance : DecidableRel spec := fun x y ↦
  let b : Bool :=
    match x, y with
    | left, zero => true
    | mid, zero => true
    | mid, one => true
    | right, one => true
    | a, b => a = b
  decidable_of_bool' b (by cases x <;> cases y <;> simp [b, spec_iff])

instance : DecidableLE Z5 := instDecidableRelSpec

lemma «forall» {P : Z5 → Prop} :
    (∀ x, P x) ↔ P .left ∧ P .zero ∧ P .mid ∧ P .one ∧ P .right := by
  constructor
  · intro h; simp [h]
  · rintro ⟨hL, hZ, hM, hO, hR⟩ x; cases x <;> simp [hL, hZ, hM, hO, hR]

lemma «exists» {P : Z5 → Prop} :
    (∃ x, P x) ↔ P .left ∨ P .zero ∨ P .mid ∨ P .one ∨ P .right := by
  constructor
  · rintro ⟨x, hx⟩; cases x <;> simp [hx]
  · rintro (hL | hZ | hM | hO | hR) <;> simpa using ⟨_, ‹_›⟩

namespace Lex

attribute [simp] Z5.ctorIdx

lemma idx_inj {x y : Z5} : (Z5.ctorIdx x = Z5.ctorIdx y) ↔ x = y := by
  casesm* Z5 <;> simp

-- We'd like to recognize when a value of `Z5` has been pinned down by its index, but that only
-- makes sense when we have a concrete element of `Z5` to work with; there's no obvious way to do
-- this other than a `simp` lemma for each case.
@[simp] lemma idx_eq_0_iff {x : Z5} : Z5.ctorIdx x = 0 ↔ x = Z5.left  := by cases x <;> simp
@[simp] lemma idx_eq_1_iff {x : Z5} : Z5.ctorIdx x = 1 ↔ x = Z5.zero  := by cases x <;> simp
@[simp] lemma idx_eq_2_iff {x : Z5} : Z5.ctorIdx x = 2 ↔ x = Z5.mid   := by cases x <;> simp
@[simp] lemma idx_eq_3_iff {x : Z5} : Z5.ctorIdx x = 3 ↔ x = Z5.one   := by cases x <;> simp
@[simp] lemma idx_eq_4_iff {x : Z5} : Z5.ctorIdx x = 4 ↔ x = Z5.right := by cases x <;> simp

@[simp]
lemma idx_toLex {x} : Z5.ctorIdx (toLex x) = Z5.ctorIdx x := by rfl

/-- A second, linear order on `Z5`. Mostly used to better exploit symmetries. -/
@[simps]
instance : LinearOrder (Lex Z5) where
  le := (Z5.ctorIdx · ≤ Z5.ctorIdx ·)
  lt := (Z5.ctorIdx · < Z5.ctorIdx ·)
  le_refl x := by rfl
  le_trans x y z hxy hyz := by grw [hxy, hyz]
  le_antisymm x y hxy hyx := by casesm* Lex Z5 <;> simp at *
  le_total x y := by casesm* Lex Z5 <;> simp at *
  lt_iff_le_not_ge x y := by casesm* Lex Z5 <;> simp
  toDecidableLE := inferInstance

-- TODO does the `↓ high` even do anything useful here?
@[simp↓ high]
lemma toLex_le {x y : Z5} : toLex x ≤ toLex y ↔ Z5.ctorIdx x ≤ Z5.ctorIdx y := by rfl

end Lex

end Z5

-- TODO goes in ???
@[match_pattern] def toLex' {α} (x : α) : Lex α := toLex x

/-- The specialization topology `L ⟶ 0 ⟵ M ⟶ 1 ⟵ R`. -/
inductive O3C2 : Type u where | as (x : Z5)
  deriving Inhabited, DecidableEq, Repr

namespace O3C2

-- @[simps!] def equivZ5 : O3C2 ≃ Z5 := WithLowerSet.toLowerSet.symm

@[simps]
def equivZ5 : O3C2 ≃ Z5 where
  toFun := (·.1)
  invFun := as

@[match_pattern] abbrev left : O3C2 := as Z5.left
@[match_pattern] abbrev zero : O3C2 := as Z5.zero
@[match_pattern] abbrev mid : O3C2 := as Z5.mid
@[match_pattern] abbrev one : O3C2 := as Z5.one
@[match_pattern] abbrev right : O3C2 := as Z5.right

@[elab_as_elim, cases_eliminator, induction_eliminator, simp]
def casesOn' {C : O3C2 → Sort*} (x : O3C2) (left : C left) (zero : C zero) (mid : C mid)
    (one : C one) (right : C right) : C x :=
  x.casesOn (Z5.casesOn · left zero mid one right)

@[simps] instance : Preorder O3C2 := Preorder.lift equivZ5
instance : TopologicalSpace O3C2 := Topology.lowerSet _

namespace Lex
@[simps!] instance : LinearOrder (Lex O3C2) where
  le x y := (Z5.ctorIdx (ofLex x).1 ≤ Z5.ctorIdx (ofLex y).1)
  lt x y := (Z5.ctorIdx (ofLex x).1 < Z5.ctorIdx (ofLex y).1)
  min x y := if Z5.ctorIdx (ofLex x).1 ≤ Z5.ctorIdx (ofLex y).1 then x else y
  max x y := if Z5.ctorIdx (ofLex x).1 ≤ Z5.ctorIdx (ofLex y).1 then y else x
  __ := LinearOrder.lift' (ofLex.trans <| equivZ5.trans toLex) (Equiv.injective _)
end Lex

instance : DecidableRel (@Specializes O3C2 _) := fun x y ↦
  decidable_of_iff (x.1 ≤ y.1) (by simp [IsLowerSet.specializes_iff_le])

@[simps]
def flip : O3C2 ≃ₜ O3C2 where
  toFun | .left => .right | .zero => .one | .mid => .mid | .one => .zero | .right => .left
  invFun | .left => .right | .zero => .one | .mid => .mid | .one => .zero | .right => .left
  left_inv x := by rcases x with ⟨⟨⟩⟩ <;> rfl
  right_inv x := by rcases x with ⟨⟨⟩⟩ <;> rfl
  continuous_toFun := by
    rw [← IsLowerSet.monotone_iff_continuous]
    intro x y hxy
    casesm* O3C2, Z5
    all_goals simp [equivZ5, Z5.spec_iff] at hxy ⊢
  continuous_invFun := by
    rw [← IsLowerSet.monotone_iff_continuous]
    intro x y hxy
    casesm* O3C2, Z5
    all_goals simp [equivZ5, Z5.spec_iff] at hxy ⊢

abbrev inl : of O2C1 ⟶ of O3C2 :=
  ofHom map
where
  map : C(O2C1, O3C2) :=
  let toFun : O2C1.{u} → O3C2.{u} | .left => .left | .zero => .zero | .right => .mid
  { toFun
    continuous_toFun := by
      rw [← IsLowerSet.monotone_iff_continuous]
      rintro ⟨x⟩ ⟨⟩ (_ | _ | _)
      all_goals simp [toFun, Z5.spec_iff] }

abbrev inr : of O2C1 ⟶ of O3C2 :=
  ofHom map
where
  map : C(O2C1, O3C2) :=
  let toFun : O2C1.{u} → O3C2.{u} | .left => .mid | .zero => .one | .right => .right
  { toFun
    continuous_toFun := by
      rw [← IsLowerSet.monotone_iff_continuous]
      rintro ⟨x⟩ ⟨⟩ (_ | _ | _)
      all_goals simp [toFun, Z5.spec_iff] }

abbrev inm : of O1C2 ⟶ of O3C2 :=
  ofHom map
where
  map : C(O1C2, O3C2) :=
  let toFun : O1C2.{u} → O3C2.{u} | .left => .zero | .one => .mid | .right => .one
  { toFun
    continuous_toFun := by
      rw [← IsUpperSet.antitone_iff_continuous]
      rintro ⟨x⟩ ⟨⟩ (_ | _ | _)
      all_goals simp [toFun, Z5.spec_iff] }

lemma isPushout : IsPushout (terminal.homOfElement' O2C1.right) (terminal.homOfElement' O2C1.left)
    inl inr := by
  fconstructor
  · constructor; ext; simp [inl.map, inr.map]
  · constructor
    fapply PushoutCocone.isColimitAux'
    · intro s
      have w : s.inr O2C1.left = s.inl O2C1.right := by
        simpa using (elementwise_of% s.condition.symm) default
      use ofHom <| {
        toFun | .left => s.inl O2C1.left
              | .zero => s.inl O2C1.zero
              | .mid => s.inr O2C1.left
              | .one => s.inr O2C1.zero
              | .right => s.inr O2C1.right
        continuous_toFun := by
          constructor
          intro t ht
          rw [isOpen_iff_forall_specializes]
          rintro ⟨x⟩ ⟨y⟩ hxy hy
          rw [IsLowerSet.specializes_iff_le] at hxy
          cases hxy with
          | refl => assumption
          | left_zero | mid_zero =>
            have := ht.preimage s.inl.hom.continuous
            rw [isOpen_iff_forall_specializes] at this
            simpa [w] using this _ _ (by simp) hy
          | mid_one | right_one =>
            have := ht.preimage s.inr.hom.continuous
            rw [isOpen_iff_forall_specializes] at this
            simpa using this _ _ (by simp) hy }
      split_ands
      · ext ⟨⟨⟩⟩ <;> simp [inl, inl.map, inr, inr.map, w]
      · ext ⟨⟨⟩⟩ <;> simp [inl, inl.map, inr, inr.map, w]
      · intro m hmL hmR
        ext ⟨⟨⟩⟩ <;> {simp [inl, inl.map, inr, inr.map] at hmL hmR ⊢; simp [← hmL, ← hmR] }

open scoped Classical in
noncomputable abbrev liftOpen {X : TopCat} {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint (closure U) (closure V)) : X ⟶ of O3C2 :=
  ofHom (map hU hV hUV)
where
  codisjoint {X : Type u} [TopologicalSpace X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
      (hUV : Disjoint (closure U) (closure V)) : (closure V)ᶜ ∪ (closure U)ᶜ = univ := by
    simpa [← compl_inter, disjoint_iff_inter_eq_empty] using hUV.symm
  map {X : Type u} [TopologicalSpace X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
      (hUV : Disjoint (closure U) (closure V)) : C(X, O3C2) :=
    IsCoherentWith.liftPair isClosed_closure.isOpen_compl isClosed_closure.isOpen_compl
      (codisjoint hU hV hUV)
      (inl.map.comp <| O2C1.lift.map hU (isClosed_closure (s := U)).isOpen_compl
        (by grw [← subset_closure]; exact disjoint_compl_right) |>.comp .subtypeVal)
      (inr.map.comp <| O2C1.lift.map (isClosed_closure (s := V)).isOpen_compl hV
        (by grw [← subset_closure]; exact disjoint_compl_left) |>.comp .subtypeVal)
      (by simp +contextual [O2C1.lift_eq_left _, O2C1.lift_eq_right _, inl.map, inr.map])

open scoped Classical in
@[simp]
lemma liftOpen_apply {X} [TopologicalSpace X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint (closure U) (closure V)) (x : X) :
    liftOpen.map hU hV hUV x =
      if x ∈ U then O3C2.left else if x ∈ frontier U then O3C2.zero
        else if x ∈ V then O3C2.right else if x ∈ frontier V then O3C2.one
      else O3C2.mid := by
  have hU' (hU : x ∈ U) : x ∈ (closure V)ᶜ := hUV.notMem_of_mem_left <| subset_closure hU
  have hUf' (hUf : x ∈ frontier U) : x ∈ (closure V)ᶜ := hUV.notMem_of_mem_left <|
    frontier_subset_closure hUf
  have hV' (hV : x ∈ V) : x ∈ (closure U)ᶜ := hUV.notMem_of_mem_right <| subset_closure hV
  have hVf' (hVf : x ∈ frontier V) : x ∈ (closure U)ᶜ := hUV.notMem_of_mem_right <|
    frontier_subset_closure hVf
  split_ifs with hU hUf hV hVf
  · simp [liftOpen.map, IsCoherentWith.liftPair_apply_of_mem_left <| hU' hU, hU]; rfl
  · simp [liftOpen.map, IsCoherentWith.liftPair_apply_of_mem_left <| hUf' hUf, hU,
      frontier_subset_closure hUf]; rfl
  · simp [liftOpen.map, IsCoherentWith.liftPair_apply_of_mem_right <| hV' hV, hV,
    subset_closure hV]; rfl
  · simp [liftOpen.map, IsCoherentWith.liftPair_apply_of_mem_right <| hVf' hVf, hV,
      frontier_subset_closure hVf]; rfl
  · have : x ∈ (closure V)ᶜ := by
      rw [closure_eq_self_union_frontier, compl_union]
      exact ⟨hV, hVf⟩
    simp [liftOpen.map, IsCoherentWith.liftPair_apply_of_mem_left this, hU, hUf,
    closure_eq_self_union_frontier]; rfl

open scoped Classical in
noncomputable abbrev liftClosed {X : TopCat} {U V : Set X} (hU : IsClosed U) (hV : IsClosed V)
    (hUV : Disjoint U V) : X ⟶ of O3C2 :=
  ofHom <| map hU hV hUV
where
  map {X : Type u} [TopologicalSpace X] {U V : Set X} (hU : IsClosed U) (hV : IsClosed V)
      (hUV : Disjoint U V) : C(X, O3C2) :=
    inm.map.comp <| O1C2.lift.map hU hV hUV

open scoped Classical in
@[simp]
lemma liftClosed_apply {X} [TopologicalSpace X] {U V : Set X} (hU : IsClosed U) (hV : IsClosed V)
    (hUV : Disjoint U V) (x : X) :
    liftClosed.map hU hV hUV x =
      if x ∈ U then O3C2.zero else if x ∈ V then O3C2.one else O3C2.mid := by
  simp only [liftClosed.map, inm.map, ContinuousMap.comp_apply, O1C2.lift_apply, mk_apply]
  split_ifs <;> simp

end O3C2

inductive O2C3 : Type u where | as (x : Z5) deriving Inhabited, DecidableEq, Repr

namespace O2C3

@[simps]
def equivZ5 : O2C3 ≃ Z5 where
  toFun := (·.1)
  invFun := as

@[match_pattern] abbrev left : O2C3 := as Z5.left
@[match_pattern] abbrev zero : O2C3 := as Z5.zero
@[match_pattern] abbrev mid : O2C3 := as Z5.mid
@[match_pattern] abbrev one : O2C3 := as Z5.one
@[match_pattern] abbrev right : O2C3 := as Z5.right


@[elab_as_elim, cases_eliminator, induction_eliminator]
def casesOn' {C : O2C3 → Sort*} (x : O2C3) (left : C left) (zero : C zero) (mid : C mid)
    (one : C one) (right : C right) : C x :=
  x.casesOn (·.casesOn left zero mid one right)

lemma «forall» {C : O2C3 → Prop} : (∀ x, C x) ↔ C left ∧ C zero ∧ C mid ∧ C one ∧ C right where
  mp h := by split_ands <;> apply h
  mpr h x := by casesm* _ ∧ _; cases x <;> assumption

lemma «exists» {C : O2C3 → Prop} : (∃ x, C x) ↔ C left ∨ C zero ∨ C mid ∨ C one ∨ C right where
  mp | ⟨x, hx⟩ => by cases x <;> simp [hx]
  mpr h := by casesm* _ ∨ _ <;> exact ⟨_, ‹_›⟩

@[simps] instance : Preorder O2C3 := Preorder.lift equivZ5
instance : TopologicalSpace O2C3 := WithUpperSet.instTopologicalSpace

instance : DecidableRel (@Specializes O2C3 _) := fun x y ↦
  decidable_of_iff (y.1 ≤ x.1) (by simp [IsUpperSet.specializes_iff_le])

namespace Lex

@[simps!] instance : LinearOrder (Lex O2C3) where
  le x y := (Z5.ctorIdx (ofLex x).1 ≤ Z5.ctorIdx (ofLex y).1)
  lt x y := (Z5.ctorIdx (ofLex x).1 < Z5.ctorIdx (ofLex y).1)
  min x y := if Z5.ctorIdx (ofLex x).1 ≤ Z5.ctorIdx (ofLex y).1 then x else y
  max x y := if Z5.ctorIdx (ofLex x).1 ≤ Z5.ctorIdx (ofLex y).1 then y else x
  __ := LinearOrder.lift' (ofLex.trans <| equivZ5.trans toLex) (Equiv.injective _)

end Lex

lemma specializes_iff {x y : O2C3} : x ⤳ y ↔ x ≥ y := by simp [IsUpperSet.specializes_iff_le]

@[simp] lemma specializes_zero_left : zero ⤳ left := by decide
@[simp] lemma specializes_mid_zero : zero ⤳ mid := by decide
@[simp] lemma specializes_one_mid : one ⤳ mid := by decide
@[simp] lemma specializes_right_one : one ⤳ right := by decide

noncomputable abbrev inl : of O1C2 ⟶ of O2C3 :=
  ofHom map
where
  map : C(O1C2, O2C3) :=
  { toFun | .left => .left | .one => .zero | .right => .mid
    continuous_toFun := by
      rw [← IsUpperSet.monotone_iff_continuous]
      rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩
      all_goals simp [Z5.spec_iff] }

noncomputable abbrev inr : of O1C2 ⟶ of O2C3 :=
  ofHom map
where
  map : C(O1C2, O2C3) :=
  { toFun | .left => .mid | .one => .one | .right => .right
    continuous_toFun := by
      rw [← IsUpperSet.monotone_iff_continuous]
      rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩
      all_goals simp [Z5.spec_iff] }

noncomputable abbrev inm : of O2C1 ⟶ of O2C3 :=
  ofHom map
where
  map : C(O2C1, O2C3) :=
  { toFun | .left => .zero | .zero => .mid | .right => .one
    continuous_toFun := by
      rw [← IsLowerSet.antitone_iff_continuous]
      rintro ⟨x⟩ ⟨_⟩ ⟨⟩
      all_goals simp [Z5.spec_iff] }


lemma isClosed_singleton_left : IsClosed {left} := by
  rw [IsUpperSet.isClosed_iff_isLower, IsLowerSet]
  rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩ ⟨⟨⟩⟩; rfl

lemma isClosed_singleton_right : IsClosed {right} := by
  rw [IsUpperSet.isClosed_iff_isLower, IsLowerSet]
  rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩ ⟨⟨⟩⟩; rfl

lemma isOpen_nhd_left : IsOpen {left, zero} := by
  rw [IsUpperSet.isOpen_iff_isUpperSet, IsUpperSet]
  rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩ ⟨⟨⟩⟩ <;> simp_all

lemma isOpen_nhd_right : IsOpen {right, one} := by
  rw [IsUpperSet.isOpen_iff_isUpperSet, IsUpperSet]
  rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩ ⟨⟨⟩⟩ <;> simp_all

lemma nhd_preimages_disjoint {X : TopCat} (f : X ⟶ of O2C3) :
    Disjoint (f ⁻¹' {left, zero}) (f ⁻¹' {right, one}) := by
  apply Disjoint.preimage; simp
  -- rw [disjoint_iff_inter_eq_empty, ← preimage_inter]
  -- convert preimage_empty; ext ⟨⟨⟩⟩ <;> simp

open scoped Classical in
noncomputable abbrev lift {X : TopCat} {U U' V V' : Set X} (hU : U ⊆ U') (hV : V ⊆ V')
    (closed_U : IsClosed U) (closed_V : IsClosed V) (open_U' : IsOpen U') (open_V' : IsOpen V')
    (disj : Disjoint U' V') : X ⟶ of O2C3 :=
  ofHom (map hU hV closed_U closed_V open_U' open_V' disj)
where
  map {X : Type u} [TopologicalSpace X] {U U' V V' : Set X} (hU : U ⊆ U') (hV : V ⊆ V')
    (closed_U : IsClosed U) (closed_V : IsClosed V) (open_U' : IsOpen U') (open_V' : IsOpen V')
    (disj : Disjoint U' V') : C(X, O2C3) :=
    ContinuousMap.liftCover fun | some true => U' | none => Uᶜ ∩ Vᶜ | some false => V'
      fun
      | some true =>
        UProp.desc.map specializes_zero_left |>.comp <| closed_U.toHom'.hom |>.comp .subtypeVal
      | none => inm.map.comp <| O2C1.lift.map open_U' open_V' disj |>.comp .subtypeVal
      | some false =>
        UProp.desc.map specializes_right_one |>.comp <| closed_V.toHom'.hom |>.comp .subtypeVal
      (by
        rintro (_ | _ | _) (_ | _ | _) x hxi hxj <;> simp only at hxi hxj ⊢
        · simp [closed_V.toHom_apply_of_notMem hxi.2, hxj, disj.notMem_of_mem_right, inm.map]
        · simp [closed_U.toHom_apply_of_notMem hxi.1, hxj, inm.map]
        · simp [closed_V.toHom_apply_of_notMem hxj.2, hxi, disj.notMem_of_mem_right, inm.map]
        · exfalso; exact disj.notMem_of_mem_left hxj hxi
        · simp [closed_U.toHom_apply_of_notMem hxj.1, hxi, inm.map]
        · exfalso; exact disj.notMem_of_mem_left hxi hxj)
      (by
        intro x
        by_cases hxU : x ∈ U
        · use some true; simp [open_U'.mem_nhds <| hU hxU]
        · by_cases hxV : x ∈ V
          · use some false; simp [open_V'.mem_nhds <| hV hxV]
          · have : x ∈ Uᶜ ∩ Vᶜ := ⟨hxU, hxV⟩
            use none; simp [closed_U.isOpen_compl.inter closed_V.isOpen_compl |>.mem_nhds this])

open scoped Classical in
@[simp]
lemma lift_apply {X} [TopologicalSpace X] {U U' V V' : Set X} {hU : U ⊆ U'} {hV : V ⊆ V'}
      {closed_U : IsClosed U} {closed_V : IsClosed V} {open_U' : IsOpen U'} {open_V' : IsOpen V'}
      {disj : Disjoint U' V'} (x : X) :
    lift.map hU hV closed_U closed_V open_U' open_V' disj x =
      if x ∈ U then left else if x ∈ U' then zero
        else if x ∈ V then right else if x ∈ V' then one
      else mid := by
  split_ifs with hxU hxU' hxV hxV' <;> unfold lift.map
  · rw [ContinuousMap.liftCover_apply (i := some true) x (hU hxU)]
    simp [closed_U.toHom_apply_of_mem hxU]
  · rw [ContinuousMap.liftCover_apply (i := some true) x hxU']
    simp [closed_U.toHom_apply_of_notMem hxU]
  · rw [ContinuousMap.liftCover_apply (i := some false) x (hV hxV)]
    simp [closed_V.toHom_apply_of_mem hxV]
  · rw [ContinuousMap.liftCover_apply (i := some false) x hxV']
    simp [closed_V.toHom_apply_of_notMem hxV]
  · rw [ContinuousMap.liftCover_apply (i := none) x (And.intro hxU hxV)]
    simp [inm.map, hxU', hxV']

end O2C3


lemma preimage_insert {X Y} (f : X → Y) (y : Y) (s : Set Y) :
    f ⁻¹' (insert y s) = (f ⁻¹' {y}) ∪ (f ⁻¹' s) := by
  ext x; simp

lemma preimage_insert' {X Y} (f : X → Y) (y : Y) (s : Set Y) :
    f ⁻¹' (insert y s) = { x | f x = y } ∪ (f ⁻¹' s) := by
  ext x; simp

section
open scoped unitInterval

inductive OIC2 : Type u where | left | ofI (x : I) | right deriving Inhabited

namespace OIC2
-- #synth OfNat I 0

instance : Zero OIC2 := ⟨ofI 0⟩
instance : One OIC2 := ⟨ofI 1⟩

@[simp] lemma ofI_zero : ofI 0 = (0 : OIC2) := rfl
@[simp] lemma ofI_one : ofI 1 = (1 : OIC2) := rfl

instance : NeZero (1 : OIC2) := ⟨by simp [← ofI_zero, ← ofI_one]⟩

section
variable {P : OIC2 → Prop}

lemma «forall» : (∀ x : OIC2, P x) ↔ (P .left ∧ (∀ x, P (ofI x)) ∧ P .right) where
  mp h := ⟨h .left, h ∘' ofI, h .right⟩
  mpr h | .left => h.1 | .ofI x => h.2.1 x | .right => h.2.2

lemma «exists» : (∃ x : OIC2, P x) ↔ (P .left ∨ (∃ x, P (ofI x)) ∨ P .right) where
  mp h := by rcases h with ⟨_ | z | _, hx⟩ <;> grind
  mpr
    | Or.inl hL => ⟨.left, hL⟩
    | Or.inr (Or.inl ⟨x, hx⟩) => ⟨.ofI x, hx⟩
    | Or.inr (Or.inr hR) => ⟨.right, hR⟩

end

open scoped Classical in
instance : TopologicalSpace OIC2.{u} :=
  coinduced (if · = (⊤ : UProp.{u}) then 0 else .left) inferInstance ⊔
    coinduced ofI inferInstance ⊔
    coinduced (if · = (⊤ : UProp.{u}) then 1 else .right) inferInstance

open scoped Classical in
@[simps]
noncomputable def inl : C(UProp, OIC2) where
  toFun x := if x = ⊤ then 0 else .left
  continuous_toFun := by
    grw [continuous_iff_coinduced_le, instTopologicalSpace, ← le_sup_left, ← le_sup_left]

open scoped Classical in
@[simps]
noncomputable def inr : C(UProp, OIC2) where
  toFun x := if x = ⊤ then 1 else .right
  continuous_toFun := by
    grw [continuous_iff_coinduced_le, instTopologicalSpace, ← le_sup_right]

@[fun_prop, continuity]
lemma continuous_ofI : Continuous ofI := by
  grw [continuous_iff_coinduced_le, instTopologicalSpace, ← le_sup_left, ← le_sup_right]

open scoped Classical in
@[simps!]
noncomputable abbrev inI : of (ULift I) ⟶ of OIC2.{u} :=
  ofHom map
where
  map := .comp { toFun := ofI } .uliftDown

-- lemma topology_eq_coinduced :
--     instTopologicalSpace.{u} = coinduced inl.{u} inferInstance ⊔
--       coinduced ofI inferInstance ⊔ coinduced inr.{u} inferInstance := rfl

@[simp] lemma range_inl : range inl = {left, 0} := by ext x; simp [inl, or_comm, eq_comm]
@[simp] lemma range_inr : range inr = {right, 1} := by ext x; simp [inr, or_comm, eq_comm]


-- Note: in the following, replacing `erw [isOpen_sup]` with
-- `unfold instTopologicalSpace; rw [isOpen_sup]` fails,
-- and with `unfold instTopologicalSpace; rw [isOpen_sup (t₁ := coinduced)]`, times out.
lemma isOpen_iff_preimages {S : Set OIC2} :
    IsOpen S ↔ IsOpen (inl ⁻¹' S) ∧ IsOpen (ofI ⁻¹' S) ∧ IsOpen (inr ⁻¹' S) := by
  erw [isOpen_sup, isOpen_sup]; simp_rw [isOpen_coinduced, and_assoc]; rfl

@[simp]
lemma isOpen_range_ofI : IsOpen (range ofI.{u}) := by
  erw [isOpen_sup, isOpen_sup]; simp_rw [isOpen_coinduced]
  simp [preimage, eq_ite_iff, ← ofI_zero, ← ofI_one]

@[simp]
lemma isClosed_singleton_left : IsClosed {left.{u}} := by
  erw [← isOpen_compl_iff, isOpen_sup, isOpen_sup]; simp_rw [isOpen_compl_iff, isClosed_coinduced]
  simp [preimage, ite_eq_iff]

@[simp]
lemma isClosed_singleton_right : IsClosed {right.{u}} := by
  erw [← isOpen_compl_iff, isOpen_sup, isOpen_sup]; simp_rw [isOpen_compl_iff, isClosed_coinduced]
  simp [preimage, ite_eq_iff]

@[simp]
lemma isClosed_left_zero : IsClosed {left, 0} := by
  erw [← isOpen_compl_iff, isOpen_sup, isOpen_sup]; simp_rw [isOpen_compl_iff, isClosed_coinduced]
  simp [preimage, ite_eq_iff, ← ofI_zero, setOf_or, ← UProp.univ_eq]; simp

@[simp]
lemma isClosed_right_one : IsClosed {right, 1} := by
  erw [← isOpen_compl_iff, isOpen_sup, isOpen_sup]; simp_rw [isOpen_compl_iff, isClosed_coinduced]
  simp [preimage, ite_eq_iff, ← ofI_one, setOf_or, ← UProp.univ_eq]; simp

lemma continuous_dom_iff {X} [TopologicalSpace X] (f : OIC2 → X) :
    Continuous f ↔ Continuous (f ∘ inl) ∧ Continuous (f ∘ ofI) ∧ Continuous (f ∘ inr) := by
  simp [continuous_iff_coinduced_le, instTopologicalSpace, coinduced_sup, coinduced_compose,
  Function.comp_def, and_assoc]

-- @[simp]
noncomputable def toO1C2 : C(OIC2, O1C2) :=
  O1C2.lift.map isClosed_singleton_left isClosed_singleton_right (by simp)

@[simp] lemma toO1C2_left : toO1C2 .left = O1C2.left := by simp [toO1C2]
@[simp] lemma toO1C2_ofI (x : I) : toO1C2 (ofI x) = O1C2.one := by simp [toO1C2]
@[simp] lemma toO1C2_right : toO1C2 .right = O1C2.right := by simp [toO1C2]

@[simp] lemma preimage_toO1C2_one : toO1C2 ⁻¹' {O1C2.one} = range ofI := by
  ext ⟨⟩ <;> simp [toO1C2]

@[simp] lemma preimage_toO1C2_left : toO1C2 ⁻¹' {O1C2.left} = {left} := by
  ext ⟨⟩ <;> simp [toO1C2]

@[simp] lemma preimage_toO1C2_right : toO1C2 ⁻¹' {O1C2.right} = {right} := by
  ext ⟨⟩ <;> simp [toO1C2]

def toI : C(OIC2, I) :=
  let toFun : OIC2 → I := fun  | .left => 0 | .ofI x => x | .right => 1
{ toFun
  continuous_toFun := by
    have : AlexandrovDiscrete UProp := inferInstanceAs (AlexandrovDiscrete <| ULift Prop)
    rw [continuous_dom_iff]
    split_ands <;> first
      | simpa [toFun, Function.comp_def] using continuous_id
      | rw [continuous_iff_spec_monotone]; simp [toFun] }

@[simp] lemma toI_left : toI .left = 0 := rfl
@[simp] lemma toI_right : toI .right = 1 := rfl
@[simp, higher_order toI_ofI] lemma toI_ofI_apply (x : I) : toI (ofI x) = x := rfl

attribute [simp] toI_ofI

lemma embedding_ofI : IsEmbedding ofI :=
  .of_leftInverse toI_ofI_apply toI.continuous continuous_ofI

lemma specializes_zero_left : 0 ⤳ left := by
  convert UProp.specializes.map inl.continuous <;> simp

lemma specializes_one_right : 1 ⤳ right := by
  convert UProp.specializes.map inr.continuous <;> simp

def flip : OIC2 ≃ₜ OIC2 :=
  let toFun | left => right | ofI x => ofI (σ x) | right => left
  have continuous_toFun : Continuous toFun := by
    have : AlexandrovDiscrete UProp := inferInstanceAs (AlexandrovDiscrete <| ULift Prop)
    rw [continuous_dom_iff]
    split_ands <;> first
      | simpa [toFun, Function.comp_def] using continuous_ofI.comp' unitInterval.continuous_symm
      | rw [continuous_iff_spec_monotone]
        simp [toFun, specializes_refl, specializes_one_right, specializes_zero_left]
{ toFun
  invFun := toFun
  left_inv := by rintro ⟨⟩ <;> simp [toFun]
  right_inv := by rintro ⟨⟩ <;> simp [toFun]
  continuous_toFun
  continuous_invFun := continuous_toFun }

@[simp] lemma flip_left : flip left = right := rfl
@[simp] lemma flip_right : flip right = left := rfl
@[simp] lemma flip_zero : flip (0 : OIC2) = (1 : OIC2) := by simp [flip]
@[simp] lemma flip_one : flip (1 : OIC2) = (0 : OIC2) := by simp [flip]
@[simp] lemma flip_ofI (x : I) : flip (ofI x) = ofI (σ x) := rfl
@[simp] lemma flip_symm : flip.symm = flip := rfl

@[simp, higher_order toI_flip]
lemma toI_flip_apply (x : OIC2) : toI (flip x) = σ (toI x) := by cases x <;> simp [toI, flip]

attribute [simp] toI_flip

lemma flip_preimage (s : Set OIC2) : flip ⁻¹' s = flip '' s := by
  rw [flip.image_eq_preimage_symm]; rfl

lemma nhds_left : 𝓝 left.{u} = (𝓝 (0 : I)).comap toI.{u} := by --⊔ pure left.{u} := by
  have hbot : (0 : I) = ⊥ := by rw [← isMin_iff_eq_bot]; rintro ⟨r, hr₁, hr₂⟩; simp
  rw [hbot]
  apply Filter.HasBasis.ext (nhds_basis_opens left) (nhds_bot_basis.comap toI) --|>.sup_pure left)
  · intro s ⟨hs, sO⟩
    have : 0 ∈ s := specializes_zero_left.mem_open sO hs
    have sO' := Metric.isOpen_iff.mp <| sO.preimage inI.continuous
    obtain ⟨ε, pos, hε⟩ := sO' 0 this
    use ⟨min ε 1, by positivity, by simp⟩, by simp [← hbot, ← Subtype.coe_lt_coe, pos]
    replace hε x := @hε x
    rintro (_ | ⟨z, hz₁, hz₂⟩ | _) hz --<;> simp [← Icc.mk_zero, ← Icc.mk_one] at hz
    · assumption
    · simpa using hε ⟨z, hz₁, hz₂⟩ (by simp [dist, abs_lt] at hz ⊢; grind)
    · simp [← Icc.mk_one] at hz
  · rintro ⟨r, hr₁, hr₂⟩ (pos : 0 < r)
    refine ⟨_, ⟨⟨specializes_zero_left.mem_open ?o
        (by simp [← Subtype.coe_lt_coe, pos]), ?o⟩, subset_refl _⟩⟩
    exact (isOpen_Iio.preimage toI.continuous)

open Filter unitInterval in
lemma nhds_right : 𝓝 right.{u} = (𝓝 (1 : I)).comap toI.{u} := by  -- ⊔ pure right.{u} := by
  have htop : (1 : I) = ⊤ := by
    rw [← isMax_iff_eq_top]; rintro ⟨r, hr₁, hr₂⟩; simp [← Icc.mk_one, hr₂]
  rw [htop, flip.nhds_eq_comap, flip_right, nhds_left, --comap_sup,
  comap_comap]
  erw [toI_flip, ← comap_comap, symmHomeomorph.comap_nhds_eq]
  simp [htop]

@[simp] lemma range_ofI_inter_preimage_toI {s : Set I} : range ofI ∩ toI ⁻¹' s = ofI '' s := by
  ext ⟨⟩ <;> simp [toI]

open Filter in
lemma topology_eq_induced : instTopologicalSpace.{u} =
    induced toO1C2 inferInstance ⊓ induced toI inferInstance := by
  have basis₁ {a} := O1C2.basis.nhds_hasBasis (a := a) |>.comap toO1C2.{u}
  have basisᵢ {b} := Metric.nhds_basis_ball (x := b) |>.comap toI.{u}
  let Δ : C(OIC2, OIC2 × OIC2) := { toFun x := (x, x), continuous_toFun := by fun_prop }
  have : induced toO1C2.{u} inferInstance ⊓ induced toI inferInstance =
      induced (prodMk toO1C2 toI) inferInstance := by
    have : prodMk toO1C2.{u} toI = (prodMap toO1C2 toI) ∘ Δ := by ext x <;> simp [Δ]
    simp only [prodMap, this, ← induced_compose, Prod.map_def, coe_mk, ← prod_induced_induced]
    simp [instTopologicalSpaceProd, induced_compose, Function.comp_def]; rfl
  rw [this]
  apply IsInducing.eq_induced
  rw [isInducing_iff_nhds]
  intro
  | left | right =>
    simp [nhds_left, nhds_right, nhds_prod_eq, comap_prod]
    simpa [prodMk, Function.comp_def, basisᵢ.le_basis_iff basis₁, OIC2.forall,
    subset_def] using ⟨1, by simp, by simp [dist]⟩
  | ofI z =>
    have emb : IsEmbedding (fun x : I ↦ (O1C2.one.{u}, x)) := isEmbedding_prodMkRight O1C2.one
    have : toO1C2.prodMk toI ∘ ofI = (O1C2.one.{u}, ·) := by ext <;> simp
    rw [← Function.comp_apply (f := toO1C2.prodMk toI), this, ← emb.map_nhds_of_mem, ← this,
    ← map_map, comap_map,
    embedding_ofI.map_nhds_of_mem _ (isOpen_range_ofI.mem_nhds (mem_range_self z))]
    · rintro ⟨⟩ ⟨⟩ h <;> simp [toO1C2] at h <;> simp [h]
    · rw [show range (O1C2.one, ·) = {O1C2.one} ×ˢ univ by ext ⟨⟩; simp [eq_comm]]
      simp [prod_mem_nhds_iff, O1C2.isOpen_one.mem_nhds]

lemma continuous_rng_iff {X} [TopologicalSpace X] (f : X → OIC2) :
    Continuous f ↔ Continuous (toO1C2 ∘ f) ∧ Continuous (toI ∘ f) := by
  simp [topology_eq_induced, continuous_iff_le_induced, induced_inf, induced_compose, le_inf_iff]

abbrev lift {X : TopCat.{u}} (f : X ⟶ of O1C2) (g : X ⟶ of (ULift I))
    (h₀ : ∀ x, f x = O1C2.left → g x = ⟨0⟩) (h₁ : ∀ x, f x = O1C2.right → g x = ⟨1⟩) :
    X ⟶ of OIC2 :=
  ofHom <| map (Hom.hom f) (uliftDown.comp <| Hom.hom g)
    (by simpa [ULift.ext_iff] using h₀) (by simpa [ULift.ext_iff] using h₁)
where
  map {X} [TopologicalSpace X] (f : C(X, O1C2)) (g : C(X, I))
    (h₀ : ∀ x, f x = O1C2.left → g x = 0) (h₁ : ∀ x, f x = O1C2.right → g x = 1) :
      C(X, OIC2) :=
    { toFun x :=
        if f x = O1C2.left then OIC2.left
        else if f x = O1C2.right then OIC2.right
        else ofI (g x)
      continuous_toFun := by
        have h₀ : f ⁻¹' {O1C2.left} ⊆ g ⁻¹' {0} := by intro x; simpa using h₀ x
        have h₁ : f ⁻¹' {O1C2.right} ⊆ g ⁻¹' {1} := by intro x; simpa using h₁ x
        simp_rw [continuous_rng_iff, Function.comp_def]
        conv in toO1C2 _ => simp only [apply_ite toO1C2]
        conv in toI _ => simp only [apply_ite toI]
        simp only [toO1C2_left, toO1C2_right, toO1C2_ofI, toI_left, toI_right, toI_ofI_apply]
        split_ands
        · convert O1C2.lift.map (O1C2.isClosed_left.preimage f.continuous)
            (O1C2.isClosed_right.preimage f.continuous) (by apply Disjoint.preimage; simp)
            |>.continuous with x
          simp
        · constructor
          classical simp_rw [preimage_if, preimage_const, ← compl_setOf,
          ← mem_singleton_iff, ← preimage_setOf_eq, setOf_mem_eq]
          intro s hs
          split_ifs with hs₀ hs₁ hs₁ --<;> simp
          · have hfₗ : f ⁻¹' {O1C2.left} ⊆ g ⁻¹' s := by grw [h₀]; apply preimage_mono; simp [hs₀]
            have hfᵣ : f ⁻¹' {O1C2.right} ⊆ g ⁻¹' s := by grw [h₁]; apply preimage_mono; simp [hs₁]
            rw [union_inter_distrib_left, ← union_assoc]
            simpa [union_inter_distrib_left, union_assoc, union_eq_self_of_subset_left hfᵣ,
            union_eq_self_of_subset_left hfₗ] using hs.preimage g.continuous
          · have hf₁ : f ⁻¹' {O1C2.left} ⊆ g ⁻¹' s := by grw [h₀]; apply preimage_mono; simp [hs₀]
            have hf₂ : f ⁻¹' {O1C2.left} ⊆ (⇑f ⁻¹' {O1C2.right})ᶜ := by
              rw [subset_compl_iff_disjoint_right]; apply Disjoint.preimage; simp
            simpa [union_eq_self_of_subset_left hf₁, union_eq_self_of_subset_left hf₂,
            union_inter_distrib_left] using (hs.preimage g.continuous).inter
              (O1C2.isClosed_right.preimage f.continuous).isOpen_compl
          · have : f ⁻¹' {O1C2.right} ⊆ g ⁻¹' s := by grw [h₁]; apply preimage_mono; simp [hs₁]
            simpa [union_inter_distrib_left, union_eq_self_of_subset_left this] using
              (hs.preimage g.continuous).inter
                (O1C2.isClosed_left.preimage f.continuous).isOpen_compl
          · simpa using ((hs.preimage g.continuous).inter
                (O1C2.isClosed_right.preimage f.continuous).isOpen_compl).inter
              (O1C2.isClosed_left.preimage f.continuous).isOpen_compl }

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_comp_toO1C2 {X : TopCat.{u}} {f : X ⟶ of O1C2} {g : X ⟶ of (ULift I)}
    {h₀ : ∀ x, f x = O1C2.left → g x = ⟨0⟩} {h₁ : ∀ x, f x = O1C2.right → g x = ⟨1⟩} :
    lift f g h₀ h₁ ≫ ofHom toO1C2 = f := by
  ext x; cases hf : f x using O1C2.casesOn' <;> simp [lift, lift.map, toO1C2, hf]

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_comp_toI {X : TopCat.{u}} {f : X ⟶ of O1C2} {g : X ⟶ of (ULift I)}
    {h₀ : ∀ x, f x = O1C2.left → g x = ⟨0⟩} {h₁ : ∀ x, f x = O1C2.right → g x = ⟨1⟩} :
    lift f g h₀ h₁ ≫ ofHom (.comp uliftUp toI) = g := by
  ext x; cases hf : f x using O1C2.casesOn' <;> simp [lift, lift.map, toI, hf, h₀, h₁]

end OIC2
end
end TopCat
