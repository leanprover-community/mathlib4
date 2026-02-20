/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Topology.LocallyFinsupp
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Algebraic Cycles

In this define algebraic cycles on a scheme `X` with coefficients in a type `Z` and provide some
basic API for working with them. We define an algebraic cycle on a scheme `X` with coefficients
in a type `Z` to be functions `c : X → Z` whose support is locally finite.

Here we're making use of the equivalence between irreducible closed subsets of a scheme and their
generic points in order to reuse the API in Function.locallyFinsupp, hence the slightly
nonstandard definition.
-/

@[expose] public section

open AlgebraicGeometry Set Order LocallyRingedSpace Topology TopologicalSpace
  CategoryTheory

universe u v
variable (R : Type*)
         [CommRing R]
         (i : ℕ)
         (X : Scheme.{u})
         {Y : Scheme.{u}}
         (Z : Type*)

/--
Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a function from `X` to `Z`
with locally finite support.

Here we're making use of the equivalence between irreducible closed subsets of a scheme and their
generic points in order to reuse the API in Function.locallyFinsupp, hence the slightly
nonstandard definition.
-/
abbrev AlgebraicCycle (X : Scheme.{u}) (Z : Type*) [Zero Z] :=
    Function.locallyFinsupp X Z

namespace AlgebraicCycle

/--
In the context of algebraic cycles, gradings tend to be defined using functions on
the components of the cycles (mainly different notions of dimension and codimension).
Here we define a notion of grading defined by such a dimension/codimension function.
-/
structure Grading [AddMonoid Z] (N : Type*) where
  /--
  The "dimension function" associated with the grading.
  -/
  dim : X → N
  /--
  Given `d` in `N`, we have an additive submonoid of `d`-homogeneous cycles.
  -/
  homogeneousCycles (d : N) : AddSubmonoid (AlgebraicCycle X Z)
  /--
  Proof that `homogeneousCycles d` is the set of `d`-homogeneous cycles.
  -/
  homogeneousCycles_carrier (d : N) : (homogeneousCycles d).carrier =
    {c : AlgebraicCycle X Z | ∀ x ∈ c.support, dim x = d} := by aesop

/--
Submonoid of cycles of pure dimension `d`.
-/
def dimensionGradingAddSubmonoid [AddMonoid Z] (d : ℕ∞) :
    AddSubmonoid (AlgebraicCycle X Z) where
  carrier := {c : AlgebraicCycle X Z | ∀ x ∈ c.support, height x = d}
  add_mem' c₁ c₂ := by
    rename_i a b
    simp_all only [Function.mem_support, ne_eq, mem_setOf_eq,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    intro x hx
    have : ¬ a x = 0 ∨ ¬ b x = 0 := by
      by_contra h
      simp_all
    exact Or.elim this (c₁ x) (c₂ x)
  zero_mem' := by simp

/--
Grading on `AlgebraicCycle X Z` by dimension, where dimension of a point is defined to be the
height in the specialization order. Note this notion of dimension falls apart a bit outside of
contexts where there are some equidimensionality hypotheses. In these contexts, the theory of
dimension functions is more appropriate to use.
-/
noncomputable
def dimensionGrading [AddMonoid Z] : Grading X Z ℕ∞ where
  dim := Order.height
  homogeneousCycles := dimensionGradingAddSubmonoid X Z

/--
Submonoid of cycles of pure codimension `d`.
-/
def codimensionGradingAddSubmonoid [AddMonoid Z] (d : ℕ∞) :
    AddSubmonoid (AlgebraicCycle X Z) where
  carrier := {c : AlgebraicCycle X Z | ∀ x ∈ c.support, coheight x = d}
  add_mem' c₁ c₂ := by
    rename_i a b
    simp_all only [Function.mem_support, ne_eq, mem_setOf_eq,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    intro x hx
    have : ¬ a x = 0 ∨ ¬ b x = 0 := by
      by_contra h
      simp_all
    exact Or.elim this (c₁ x) (c₂ x)
  zero_mem' := by simp

/--
Grading on `AlgebraicCycle X Z` by codimension, where codimension of a point is defined to be the
coheight in the specialization order. Note this notion of codimension falls apart a bit outside of
contexts where there are some equidimensionality hypotheses. In these contexts, the theory of
dimension functions is more appropriate to use.
-/
noncomputable
def codimensionGrading [AddMonoid Z] : Grading X Z ℕ∞ where
  dim := Order.coheight
  homogeneousCycles := codimensionGradingAddSubmonoid X Z

variable {X Z}

section Zero

variable (f : X ⟶ Y)
         [Zero Z]
         (c : AlgebraicCycle X Z)
         (x : X)
         (z : Y)

/--
The cycle containing a single point with a chosen coefficient
-/
noncomputable
def single (coeff : Z) : AlgebraicCycle X Z where
  toFun := Set.indicator {x} (Function.const X coeff)
  supportWithinDomain' := by simp only [support_indicator]; exact LE.le.subset fun _ a_1 ↦ trivial
  supportLocallyFiniteWithinDomain' z hz :=
    ⟨⊤, ⟨Filter.univ_mem' fun a ↦ trivial, by simp [← Function.const_def, toFinite]⟩⟩

/--
Implementation detail for the pushforward; the support of a cycle on X intersected with the preimage
of a point z : Y along a morphism f : X ⟶ Y.
-/
def preimageSupport : Set X :=
  f.base ⁻¹' {z} ∩ c.support

/--
Implementation detail for the pushforward; the support of a cycle on X intersected with the preimage
of a point z : Y along a quasicompact morphism f : X ⟶ Y is finite.
-/
lemma preimageSupport_finite [qf : QuasiCompact f] :
    (preimageSupport f c z).Finite := LocallyFiniteSupport.finite_inter_support_of_isCompact
  c.locallyFiniteSupport  <| f.isCompact_preimage_singleton z

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
def _root_.AlgebraicGeometry.LocallyRingedSpace.Hom.degree : ℕ := @Module.finrank
    (IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)))
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) _ _ _

end Zero

/--
The usual degree function of a morphism of schemes `f : X ⟶ Y` at a point `x : X`
is defined to be the degree of the associated field extension from `κ(f x)` to `κ(x)`, and can be
viewed a kind of correction factor with respect to which one can define the pushforward of algebraic
cycles.

The class `HasDegree Z` states the properties needed of such a degree function to define a sensible
notion of pushforward from `AlgebraicCycle X Z` to `AlgebraicCycle Y Z`.
-/
class HasDegree (Z : Type*) [Semiring Z] where
  /--
  The degree of a morrphism at a point
  -/
  degree : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → X → Z
  /--
  The degree of the identity at any point is `1`.
  -/
  degree_one {X : Scheme.{u}} (z : X) : degree (𝟙 X) z = 1

open Classical in
/--
Implementation detail for pushforward: function used to define the coefficient of the pushforward
of a cycle `c` at a point `z = f x`, as in stacks `02R3`.
-/
noncomputable
def mapAux {N : Type*} [Semiring Z] [HasDegree Z] {Y : Scheme}
    (gx : Grading X Z N) (gy : Grading Y Z N)
    (f : X ⟶ Y) (x : X) : Z :=
  if gx.dim x = gy.dim (f.base x) then HasDegree.degree f x else 0

section map

variable {Z : Type*} [Semiring Z] {W : Y.Opens} (hW : IsAffineOpen W)
  (f : X ⟶ Y) (c : AlgebraicCycle X Z)

lemma preimageSupport_inter_subset : W.carrier ∩ {z | (preimageSupport f c z).Nonempty} ⊆
    f.base '' (f.base ⁻¹' ((W.carrier ∩ {z | (preimageSupport f c z).Nonempty})) ∩ c.support) := by
  intro a ha
  rw [image_preimage_inter]
  suffices a ∈ f.base '' c.support from mem_inter ha this
  have := ha.2.some_mem
  simp only [preimageSupport, mem_inter_iff, mem_preimage, mem_singleton_iff,
    Function.mem_support, ne_eq, mem_image] at this ⊢
  exact ⟨ha.2.some, this.symm⟩

lemma preimageSupport_preimage_inter_subset : f.base ⁻¹' W.carrier ∩
    f.base ⁻¹' {z | (preimageSupport f c z).Nonempty} ∩ c.support ⊆
    f.base ⁻¹' W.carrier ∩ (⋃ z : Y, preimageSupport f c z) := by
  intro p hp
  simp only [Opens.carrier_eq_coe, preimageSupport, preimage_setOf_eq, mem_inter_iff,
    mem_preimage, SetLike.mem_coe, mem_setOf_eq, Function.mem_support, ne_eq, mem_iUnion,
    mem_singleton_iff, exists_and_right, exists_eq', true_and] at hp ⊢
  exact ⟨hp.1.1, hp.2⟩

variable [qc : QuasiCompact f]

lemma preimage_inter_support_finite_of_isAffineOpen (hW : IsAffineOpen W) :
    (f.base ⁻¹' W.carrier ∩ c.support).Finite :=
  LocallyFiniteSupport.finite_inter_support_of_isCompact c.locallyFiniteSupport <|
  qc.1 W.carrier W.is_open' <| AlgebraicGeometry.IsAffineOpen.isCompact hW

lemma iUnion_preimage_inter_support_finite_of_isAffineOpen (hW : IsAffineOpen W) :
    (⋃ _ : Y, f.base ⁻¹' W.carrier ∩ c.support).Finite := by
  suffices (f.base ⁻¹' W.carrier ∩ c.support).Finite by
    apply Finite.subset this
    intro a ha
    simp only [Opens.carrier_eq_coe, mem_iUnion, mem_inter_iff, mem_preimage,
      SetLike.mem_coe, Function.mem_support, ne_eq, exists_and_left, exists_const_iff] at ha ⊢
    exact ⟨ha.1, ha.2.2⟩
  exact preimage_inter_support_finite_of_isAffineOpen f c hW

lemma inter_nonempty_finite (hW : IsAffineOpen W)
   : (W.carrier ∩ {z : Y | (preimageSupport f c z).Nonempty}).Finite := by
  refine Finite.subset (Finite.image _ ?_) (preimageSupport_inter_subset f c)
  rw[preimage_inter]
  apply Finite.subset _ (preimageSupport_preimage_inter_subset f c)
  rw[inter_iUnion]
  suffices (⋃ i : Y, f.base ⁻¹' W.carrier ∩ c.support).Finite by
    apply Finite.subset this
    simp only [Opens.carrier_eq_coe, iUnion_subset_iff]
    intro y x hx
    simp only [mem_inter_iff, mem_preimage, SetLike.mem_coe,
      Function.mem_support, ne_eq, mem_iUnion, exists_and_left, exists_const_iff] at hx ⊢
    exact ⟨hx.1, ⟨Nonempty.intro y, hx.2.2⟩⟩
  exact iUnion_preimage_inter_support_finite_of_isAffineOpen f c hW

variable {N : Type*} [HasDegree Z]

/--
The pushforward of an algebraic cycle has locally finite support.
-/
lemma map_locally_finite (gx : Grading X Z N) (gy : Grading Y Z N) :
    ∀ z : Y, ∃ t ∈ 𝓝 z, (t ∩ Function.support fun z ↦
    ∑ x ∈ (preimageSupport_finite f c z).toFinset, (c x) * mapAux gx gy f x).Finite := by
  intro y
  obtain ⟨W, hW⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) (by simp)
  use W
  refine ⟨IsOpen.mem_nhds (Opens.isOpen W) hW.2.1, ?_⟩
  suffices (W.carrier ∩ {z : Y | (preimageSupport f c z).Nonempty}).Finite by
      apply Finite.subset this
      apply inter_subset_inter Set.Subset.rfl
      intro x
      simp only [Function.mem_support, ne_eq, mem_setOf_eq]
      contrapose!
      intro aux
      rw [Finset.sum_eq_zero]
      intro x hx
      simp_all
  exact inter_nonempty_finite f c hW.1

/--
The pushforward of an algebraic cycle by a quasicompact morphism.

Note that usually the pushforward is only defined for proper morphisms, and indeed we will need
properness to prove that the pushforward preserves rational equivalence.
-/
noncomputable
def map (gx : Grading X Z N) (gy : Grading Y Z N) : AlgebraicCycle Y Z
    where
  toFun z := (∑ x ∈ (preimageSupport_finite f c z).toFinset, (c x) * mapAux gx gy f x)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := map_locally_finite f c gx gy z

/--
Pushforward preserves cycles of pure dimension `d` in the dimension grading.
-/
lemma map_homogeneneous {d : ℕ∞} (c : AlgebraicCycle X Z)
    (hc : c ∈ (dimensionGrading X Z).homogeneousCycles d) :
    map f c (dimensionGrading X Z) (dimensionGrading Y Z) ∈
    (dimensionGrading Y Z).homogeneousCycles d := by
  simp only [dimensionGrading]
  intro y hy
  simp only [map, preimageSupport, mapAux, mul_ite, mul_zero, Function.mem_support,
    ne_eq] at hy
  obtain ⟨x, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  simp only [Finite.mem_toFinset, mem_inter_iff, mem_preimage, mem_singleton_iff,
    Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
  have : height x = d := hc x hx.1.2
  simp_all

/--
The pushforward of `c` along the identity morphism is `c`.
-/
@[simp]
lemma map_id (g : Grading X Z N) : map (𝟙 X) c g g = c := by
   ext z
   have : (c z ≠ 0 ∧ (preimageSupport_finite (𝟙 X) c z).toFinset = {z}) ∨
          (c z = 0 ∧ (preimageSupport_finite (𝟙 X) c z).toFinset = ∅) := by
    simp only [ne_eq, Finite.toFinset, preimageSupport, Scheme.Hom.id_base, TopCat.hom_id,
      ContinuousMap.coe_id, preimage_id_eq, id_eq, toFinset_eq_empty, singleton_inter_eq_empty,
      Function.mem_support, not_not, and_self]
    refine Or.elim (em (c z = 0)) (fun o ↦ Or.inr o) (fun o ↦ Or.inl ⟨o, Finset.ext (fun a ↦ ?_)⟩)
    simp only [mem_toFinset, mem_inter_iff, mem_singleton_iff, Function.mem_support, ne_eq,
      Finset.mem_singleton, and_iff_left_iff_imp]
    rintro rfl
    assumption
   suffices (map (𝟙 X) c g g).toFun z = c.toFun z from this
   obtain h | h := this
   all_goals simp only [map, mapAux, Scheme.Hom.id_base, TopCat.hom_id,
               ContinuousMap.id_apply, ↓reduceIte]
             rw[h.2]
             simp only [HasDegree.degree_one, mul_one, Finset.sum_singleton, Finset.sum_empty]
   · rfl
   · exact h.1.symm

end map

noncomputable instance instHasDegreeNat : HasDegree ℕ where
  degree := Hom.degree
  degree_one {M} x := by
    dsimp [Hom.degree]
    have (R : Type*) [CommSemiring R] : Semiring.toModule (R := R) =
      Algebra.toModule (R := R) (A := R) := rfl
    have := this (IsLocalRing.ResidueField ↑(M.presheaf.stalk x))
    let k := Module.finrank_self (IsLocalRing.ResidueField ↑(M.presheaf.stalk x))
    convert k
    rw [this]
    simp [moduleResidueFieldExtension]
    congr
    aesop

noncomputable instance : HasDegree ℤ where
  degree f x := ↑(Hom.degree f x)
  degree_one {M} x := by
    have := instHasDegreeNat.degree_one x
    dsimp [HasDegree.degree] at this
    rw [this]
    exact Int.ofNat_one

end AlgebraicCycle
