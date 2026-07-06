/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.LocallyFinsupp
public import Mathlib.Data.Finite.Defs
public import Mathlib.Topology.Spectral.Prespectral
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Algebraic Cycles

In this file we define algebraic cycles on a scheme `X` with coefficients in a type `R` and provide
some basic API for working with them. We define an algebraic cycle on a scheme `X` with
coefficients in a type `R` to be functions `c : X → R` whose support is locally finite.

Here we're making use of the equivalence between irreducible closed subsets of a scheme and their
generic points in order to reuse the API in Function.locallyFinsupp, hence the slightly
nonstandard definition.
-/

@[expose] public section

open AlgebraicGeometry Set Order LocallyRingedSpace Topology TopologicalSpace
  CategoryTheory

section LocallyFinsuppPushforward
open Set Order Topology TopologicalSpace

variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsSpectralMap f) (w : X → R)

namespace Function
namespace locallyFinsupp

section Zero
variable [Zero R]

variable (f) in
/--
Implementation detail for the pushforward; the support of a locally finsupp function on `X`
intersected with the preimage of a point `z : Y` along a function `f : X ⟶ Y`.
-/
def preimageSupport (c : X → R) (z : Y) : Set X :=
  f ⁻¹' {z} ∩ c.support

/--
A function `f` has finite preimage support with respect to a function `c : X → R` where `R` has a
zero element if its fibers all have finite intersection with the support of `c`.

This is a nonstandard notion and is mainly here to define the pushforward of algebraic cycles.
In this case, we define the pushforward with respect to quasicompact morphisms which automatically
satisfy this property, so in practice this definition shouldn't be exposed to the user too much.
-/
def PreimageSupportFinite (c : X → R) (f : X → Y) : Prop :=
    ∀ (z : Y), (preimageSupport f c z).Finite

lemma _root_.IsProperMap.preimageSupportFinite (c : locallyFinsupp X R)
    (f : X → Y) (hf : IsProperMap f) : PreimageSupportFinite c f := by
  intro z
  exact LocallyFiniteSupport.finite_inter_support_of_isCompact
    c.locallyFiniteSupport <| hf.isCompact_preimage isCompact_singleton

end Zero

section map

variable [Semiring R] {W : TopologicalSpace.Opens Y} (c : Function.locallyFinsupp X R)

lemma inter_preimageSupport_nonempty_finite (hf : IsSpectralMap f) (hW : IsCompact W.1) :
    (W.carrier ∩ {z : Y | (preimageSupport f c z).Nonempty}).Finite := by
  suffices (f ⁻¹' (W.carrier ∩ {z | (preimageSupport f c z).Nonempty}) ∩ c.support).Finite from
    (this.image f).subset (fun a ha ↦ by grind [preimageSupport, Set.Nonempty])
  rw [preimage_inter]
  suffices (f ⁻¹' W ∩ ⋃ z, preimageSupport f c z).Finite by
    apply Finite.subset this
    rw [Set.inter_assoc]
    exact Set.inter_subset_inter_right _ (fun p hp ↦ by simp_all [preimageSupport])
  rw [inter_iUnion]
  suffices (f ⁻¹' W.carrier ∩ c.support).Finite by
    grind [preimageSupport, Opens.carrier_eq_coe, iUnion_subset_iff, SetLike.mem_coe,
      Function.mem_support, Finite.subset]
  exact LocallyFiniteSupport.finite_inter_support_of_isCompact c.locallyFiniteSupport <|
    hf.2 W.is_open' hW

variable {N : Type*} [PrespectralSpace Y]

lemma map_locally_finite (hf : IsSpectralMap f)
    (hf' : PreimageSupportFinite c f) (y : Y) :
    ∃ t ∈ 𝓝 y, (t ∩ Function.support fun z ↦
    ∑ x ∈ (hf' z).toFinset, (c x) * w x).Finite := by
  obtain ⟨W, hW⟩ : ∃ W : TopologicalSpace.Opens Y, IsCompact W.1 ∧ y ∈ W := by
    obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
        (by simp : y ∈ ⊤) (by simp)
    use ⟨U, hU.1.1⟩
    exact ⟨hU.1.2, hU.2.1⟩
  use W
  refine ⟨IsOpen.mem_nhds (Opens.isOpen W) hW.2, ?_⟩
  suffices (W.carrier ∩ {z : Y | (preimageSupport f c z).Nonempty}).Finite by
    apply Finite.subset this
    apply inter_subset_inter_right
    intro x
    contrapose!
    simp +contextual [Set.not_nonempty_iff_eq_empty]
  exact inter_preimageSupport_nonempty_finite c hf hW.1

variable (f) in
/--
The pushforward of a function `c` of locally finite support
by a spectral map whose fibers intersect `c` in finitely many places
with respect to a weight function `w`. This is mainly used when interpreting locally finsupp
functions as algebraic cycles (in this case the weight function corresponds to a dimension or
codimension function).
-/
@[simps]
noncomputable
def map (hf : IsSpectralMap f) (hf' : PreimageSupportFinite c f) : Function.locallyFinsupp Y R where
  toFun z := (∑ x ∈ (hf' z).toFinset, (c x) * w x)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := map_locally_finite w c hf hf' z

/--
Pushforward preserves cycles of pure dimension `d` in the dimension grading.
-/
lemma map_homogeneous (s : Set X) (t : Set Y) (hc : c.support ⊆ s)
    (hf' : PreimageSupportFinite c f)
    (h : ∀ x : X, x ∈ s → w x ≠ 0 → f x ∈ t) :
    (map f w c hf hf').support ⊆ t := by
  intro y hy
  simp only [map, preimageSupport, Function.mem_support, ne_eq] at hy
  obtain ⟨x, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  simp only [Finite.mem_toFinset, mem_inter_iff, mem_preimage, mem_singleton_iff,
    Function.mem_support, ne_eq] at hx
  specialize h x (hc hx.1.2)
  grind

lemma preimageSupportFinite_id : PreimageSupportFinite c id := by
  intro z
  simp [preimageSupport, toFinite ({z} ∩ locallyFinsuppWithin.support c)]

/--
The pushforward of `c` along the identity morphism is `c`.
-/
@[simp]
lemma map_id [PrespectralSpace X] (hw : ∀ z : X, w z = 1) :
    map id w c isSpectralMap_id (preimageSupportFinite_id c) = c := by
  ext z
  obtain h | h : (c z ≠ 0 ∧ (preimageSupportFinite_id c z).toFinset = {z}) ∨
        (c z = 0 ∧ (preimageSupportFinite_id c z).toFinset = ∅) := by
    grind [Finite.toFinset, preimageSupport, Function.mem_support]
  · simp_all
  · simp_all

end map
end locallyFinsupp
end Function

end LocallyFinsuppPushforward


universe u v
variable {X Y : Scheme.{u}} {R : Type*}

/--
Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a function from `X` to `Z`
with locally finite support.

Here we're making use of the equivalence between irreducible closed subsets of a scheme and their
generic points in order to reuse the API in Function.locallyFinsupp, hence the slightly
nonstandard definition.
-/
abbrev AlgebraicCycle (X : Scheme.{u}) (R : Type*) [Zero R] := Function.locallyFinsupp X R

variable (f : X ⟶ Y)

noncomputable
instance moduleResidueFieldExtension (x : X) :
    Module (IsLocalRing.ResidueField ↑(Y.presheaf.stalk (f x)))
    (IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) :=
  letI := RingHom.toAlgebra (IsLocalRing.ResidueField.map (f.stalkMap x).hom)
  Algebra.toModule

/--
Degree of `f` at a point `x` is defined to be the degree of the associated field extension
from `κ(f x)` to `κ(x)`. We return a default value of zero when this degree is either infinite
or undefined.
-/
noncomputable
def _root_.AlgebraicGeometry.Scheme.Hom.degree (x : X) : ℕ := @Module.finrank
    (IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)))
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) _ _ _

namespace AlgebraicGeometry.AlgebraicCycle
section restrict

variable [Zero R] (D : AlgebraicCycle X R) (t : Set X)
/--
Restriction of an algebraic cycle to some set. This is distinct from `Function.locallyFinsuppWithin`
because here we get something which is still just a locally finsupp function on the whole space.
-/
noncomputable
def restrict : AlgebraicCycle X R where
  toFun z := by
    classical
    exact if z ∈ t then D z else 0
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨U, hU⟩ := D.supportLocallyFiniteWithinDomain z hz
    use U, hU.1
    apply Finite.subset hU.2
    apply inter_subset_inter (Subset.refl U)
    simp

open Classical in
lemma restrict_apply (z : X) : D.restrict t z = if z ∈ t then D z else 0 := rfl

@[simp]
lemma restrict_eq_of_mem (z : X) (hz : z ∈ t) :
    D.restrict t z = D z := dif_pos hz

@[simp]
lemma restrict_eq_zero_of_not_mem (z : X) (hz : z ∉ t) :
    D.restrict t z = 0 := dif_neg hz

lemma restrict_eqOn : Set.EqOn (D.restrict t) D t := by
  intro _ _
  simp_all

lemma restrict_eqOn_compl : Set.EqOn (D.restrict t) 0 tᶜ := by
  intro _ hx
  simp_all

@[simp]
lemma restrict_eq_zero_of_eq_zero {z : X} (hD : D z = 0) : (D.restrict t) z = 0 := by
  by_cases o : z ∈ t <;> simp_all

variable {D t}
lemma restrict_support_subset_support : (D.restrict t).support ⊆ D.support := by
  simp_all only [Function.support_subset_iff, ne_eq, Function.mem_support]
  intro x hx
  contrapose hx
  simp_all

lemma restrict_support_subset : (D.restrict t).support ⊆ t := by
  intro z
  by_cases o : z ∈ t <;> simp_all

lemma restrict_support_of_subset {X : Scheme.{u}} {R : Type*} [Zero R] {D : AlgebraicCycle X R}
    {t s : Set X} (h : D.support ⊆ s) : (D.restrict t).support ⊆ s :=
  Subset.trans restrict_support_subset_support h

lemma restrict_support_subset_inter {X : Scheme.{u}} {R : Type*} [Zero R] {D : AlgebraicCycle X R}
    {t s : Set X} (h : D.support ⊆ s) : (D.restrict t).support ⊆ s ∩ t :=
  subset_inter_iff.mpr ⟨Subset.trans restrict_support_subset_support h, restrict_support_subset⟩

@[simp]
lemma restrict_univ {X : Scheme.{u}} {R : Type*} [Zero R] {D : AlgebraicCycle X R} :
    D.restrict univ = D := by
  ext z
  simp

lemma restrict_subset {X : Scheme.{u}} {R : Type*} [Zero R] {D : AlgebraicCycle X R} {t s : Set X}
    (h : t ⊆ s) {z : X} (hz : z ∈ t) : D.restrict t z = D.restrict s z := by simp [hz, h hz]

end restrict

variable [Semiring R] (c : AlgebraicCycle X R)
/--
Implementation detail for pushforward: function used to define the coefficient of the pushforward
of a cycle `c` at a point `z = f x`, as in stacks `02R3`.
-/
noncomputable
def mapAux {N : Type*} [DecidableEq N] {Y : Scheme} (f : X ⟶ Y) (wx : X → N) (wy : Y → N) (x : X) :
    ℕ := if wx x = wy (f.base x) then f.degree x else 0

open Function locallyFinsupp
lemma _root_.AlgebraicGeometry.Scheme.Hom.preimageSupportFinite [QuasiCompact f] :
    PreimageSupportFinite c f :=
  fun z ↦ LocallyFiniteSupport.finite_inter_support_of_isCompact c.locallyFiniteSupport <|
    AlgebraicGeometry.Scheme.Hom.isCompact_preimage_singleton f z

/--
The pushforward of algebraic cycles with respect to a quasicompact morphism of schemes. The
arguments `wx` and `wy` are gradings of the algebraic cycle, which is necessary information for the
function determining how to adjust the coefficients of the cycle. Typically in
applications these will be some notions of dimension or codimension. The most common notion of
dimension is `Order.height`, and the most common notion of codimension is `Order.coheight`, though
more sophisticated notions exist in the literature which are useful when sufficient
equidimensionality hypotheses cannot be assumed.
-/
noncomputable
def pushforward [QuasiCompact f] {N : Type*} [DecidableEq N] (c : AlgebraicCycle X R)
    (wx : X → N) (wy : Y → N) : AlgebraicCycle Y R :=
  Function.locallyFinsupp.map f (Nat.cast (R := R) <| mapAux f wx wy ·) c
  f.isSpectralMap (f.preimageSupportFinite c)

lemma homgeneous_ext {R : Type*} [Zero R] {D₁ D₂ : AlgebraicCycle X R}
    {t : Set X} (hD₁ : D₁.support ⊆ t) (hD₂ : D₂.support ⊆ t)
    (h : ∀ a ∈ t, D₁ a = D₂ a) : D₁ = D₂ :=
  have h' : ∀ a, D₁ a = D₂ a := by
    intro a
    by_cases o : a ∈ t
    · exact h a o
    rw [support_subset_iff] at hD₁ hD₂
    specialize hD₁ a
    specialize hD₂ a
    simp_all
  DFunLike.ext _ _ h'

lemma homogeneous_le_iff {R : Type*} [Zero R] [Preorder R] {D₁ D₂ : AlgebraicCycle X R}
    {t : Set X} (hD₁ : D₁.support ⊆ t) (hD₂ : ∀ z ∈ tᶜ, D₂ z ≥ 0) :
    D₁ ≤ D₂ ↔ ∀ z ∈ t, D₁ z ≤ D₂ z := by
  peel with z
  refine ⟨by tauto, fun m ↦ ?_⟩
  by_cases o : z ∈ t
  · exact m o
  simp only [support_subset_iff, ne_eq] at hD₁
  specialize hD₁ z
  by_cases p : D₁ z = 0
  · simp_all
  specialize hD₁ p
  contradiction

end AlgebraicGeometry.AlgebraicCycle
