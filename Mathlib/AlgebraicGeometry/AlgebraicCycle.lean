/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Algebraic Cycles

We define algebraic cycles on a scheme `X` to be functions `c : X → ℤ` whose support is
locally finite.
-/

open AlgebraicGeometry Set Order LocallyRingedSpace Topology TopologicalSpace
  CategoryTheory

universe u v
variable (R : Type*)
         [CommRing R]
         (i : ℕ)
         {X Y : Scheme.{u}}
         (Z : Type*) --[Zero Z]

/--
Algebraic cycle on a scheme X.

Note I am not certain that this should be an abbrev. I'm also not sure if these definitions
should instead directly be about Function.locallyFinsuppWithin
-/
abbrev AlgebraicCycle (X : Scheme.{u}) (Z : Type*) [Zero Z] :=
    Function.locallyFinsuppWithin (⊤ : Set X) Z


namespace AlgebraicCycle

/-
I think this is the data we should take in whenever we want to talk about a grading. Since
everything should be mostly handled by typeclass inference, it should suffice to only explicitly
pass A around.
-/
/-variable {S ι : Type*} [AddMonoid Z] [SetLike S (AlgebraicCycle X Z)] [AddMonoid ι]
    [AddSubmonoidClass S (AlgebraicCycle X Z)] [DecidableEq ι]
    (A : ι → S) (X)-/
variable (X)
/--
Subgroup of cycles of pure dimension `d`.
-/
def dimensionGrading [AddMonoid Z] (d : ℕ∞) :
    AddSubmonoid (AlgebraicCycle X Z) where
  carrier := {c : AlgebraicCycle X Z | ∀ x ∈ c.support, height x = d}
  add_mem' c₁ c₂ := by
    rename_i a b
    simp_all only [top_eq_univ, Function.mem_support, ne_eq, mem_setOf_eq,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    intro x hx
    have : ¬ a x = 0 ∨ ¬ b x = 0 := by
      by_contra h
      simp_all
    exact Or.elim this (c₁ x) (c₂ x)
  zero_mem' := by simp


def dimensionGrading' (Z : Type*) [AddCommGroup Z] (d : ℕ∞) :
    AddSubgroup (AlgebraicCycle X Z) where
      __ := dimensionGrading X Z d
      neg_mem' c := by simp_all [dimensionGrading]




def codimensionGrading [AddCommGroup Z] (d : ℕ∞) :=
  {c : AlgebraicCycle X Z | ∀ x ∈ c.support, coheight x = d}

variable {X Z}

section Zero

variable (f : X ⟶ Y)
         [Zero Z]
         --[AddMonoid Z]
         (c : AlgebraicCycle X Z)
         (x : X)
         (z : Y)


/--
The cycle containing a single point with a chosen coefficient
-/
noncomputable
def single (coeff : Z) : AlgebraicCycle X Z where
  toFun := Set.indicator {x} (Function.const X coeff)
  supportWithinDomain' := by simp
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
 (preimageSupport f c z).Finite :=
 supportLocallyFiniteWithin_top_inter_compact_finite c.supportLocallyFiniteWithinDomain' <|
  QuasiCompact.isCompact_preimage_singleton f z

/--
Degree of `f` at a point `x` is defined to be the degree of the associated field extension
from `κ(f x)` to `κ(x)`. We return a default value of zero when this degree is either infinite
or undefined.
-/
noncomputable
def _root_.AlgebraicGeometry.LocallyRingedSpace.Hom.degree : ℕ := @Module.finrank
    (IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)))
    (IsLocalRing.ResidueField (X.presheaf.stalk x))
    (by infer_instance)
    (by infer_instance)
    (by have :=
      RingHom.toAlgebra (IsLocalRing.ResidueField.map (f.stalkMap x).hom);exact Algebra.toModule)

end Zero
open Classical in
/--
Implementation detail for pushforward: function used to define the coefficient of the pushforward
of a cycle `c` at a point `z = f x`, as in stacks 02R3.

Note: I'm not entirely sure if the case distinction here (and hence this definition) is necessary,
since the degree alread has a default value of zero whenever the degree of the field extension is
not finite.
-/
noncomputable
def mapAux {Y : Scheme} (f : X ⟶ Y) (x : X) : ℤ :=
  if height x = height (f.base x) then Hom.degree f x else 0



class _root_.HasDegree (Z : Type*) [Semiring Z] where
  degree : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → X → Z
  degree_one {X : Scheme.{u}} (z : X) : degree (𝟙 X) z = 1


open Classical in
noncomputable
def mapAux' [Semiring Z] {N : Type*} (h : {Y : Scheme.{u}} → Y → N)
    [HasDegree Z] {Y : Scheme} (f : X ⟶ Y) (x : X) : Z :=
  if h x = h (f.base x) then HasDegree.degree f x else 0

/-
I think this is the kind of thing we might want for, say, gradings that only work on particular
kinds of scheme (I'm thinking in particular of gradings explicitly involving some dimension
function, in which case our m would check if the scheme is of finite type over (S, δ) or
something).
-/
def h {Y : Scheme.{u}} (m : Scheme.{u} → Prop) (_ : m Y) (x : Y) : Z := sorry


/--
The pushforward of an algebraic cycle has locally finite support.

Note that while this could be part of the definition of map, we experienced significant performance
issues when instead writing this definition in the `supportLocallyFiniteWithinDomain'` field of the
`map` definition.

I feel the proof here is a bit too long, but I'm a little unsure of how I should shorten it.
-/
lemma map_locally_finite {Z : Type*} {Y : Scheme} [Semiring Z] [HasDegree Z]
    {N : Type*} (h : {Y : Scheme.{u}} → Y → N)
    (f : X ⟶ Y) [qc : QuasiCompact f] (c : AlgebraicCycle X Z) :
    ∀ z : Y, ∃ t ∈ 𝓝 z, (t ∩ Function.support fun z ↦
    ∑ x ∈ (preimageSupport_finite f c z).toFinset, (c x) * mapAux' h f x).Finite := by
  intro y
  obtain ⟨W, hW⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) (by aesop)
  have cpct : IsCompact (f.base ⁻¹' W) := qc.1 W.carrier W.is_open' <|
     AlgebraicGeometry.IsAffineOpen.isCompact hW.1
  use W
  refine ⟨IsOpen.mem_nhds (Opens.isOpen W) hW.2.1, ?_⟩

  have pbfinite : (f.base ⁻¹' W ∩ Function.support c).Finite :=
   supportLocallyFiniteWithin_top_inter_compact_finite c.supportLocallyFiniteWithinDomain' cpct

  suffices (W.carrier ∩ {z : Y | (preimageSupport f c z).Nonempty}).Finite by
      apply Finite.subset this
      apply inter_subset_inter Set.Subset.rfl
      intro x
      simp only [top_eq_univ, Function.mem_support, ne_eq, mem_setOf_eq]
      contrapose!
      intro aux
      rw [Finset.sum_eq_zero]
      intro x hx
      simp_all

  have : W.carrier ∩ {z | (preimageSupport f c z).Nonempty} ⊆
    f.base '' (f.base ⁻¹' ((W.carrier ∩ {z | (preimageSupport f c z).Nonempty})) ∩ c.support) := by
    intro a ha
    rw [image_preimage_inter]
    suffices a ∈ f.base '' c.support from mem_inter ha this
    have := ha.2.some_mem
    simp only [preimageSupport, top_eq_univ, mem_inter_iff, mem_preimage, mem_singleton_iff,
      Function.mem_support, ne_eq, mem_image] at this ⊢
    exact ⟨ha.2.some, this.symm⟩

  refine Finite.subset (Finite.image _ ?_) this
  rw[preimage_inter]
  have : f.base ⁻¹' W.carrier ∩ f.base ⁻¹' {z | (preimageSupport f c z).Nonempty} ∩ c.support ⊆
      f.base ⁻¹' W.carrier ∩ (⋃ z : Y, preimageSupport f c z) := by
    intro p hp
    simp only [Opens.carrier_eq_coe, preimageSupport, top_eq_univ, preimage_setOf_eq, mem_inter_iff,
      mem_preimage, SetLike.mem_coe, mem_setOf_eq, Function.mem_support, ne_eq, mem_iUnion,
      mem_singleton_iff, exists_and_right, exists_eq', true_and] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩

  apply Finite.subset _ this
  rw[inter_iUnion]
  simp[preimageSupport]
  suffices (⋃ i : Y, f.base ⁻¹' W.carrier ∩ c.support).Finite by
    apply Finite.subset this
    simp only [Opens.carrier_eq_coe, top_eq_univ, iUnion_subset_iff]
    intro y x hx
    simp only [mem_inter_iff, mem_preimage, SetLike.mem_coe, mem_singleton_iff,
      Function.mem_support, ne_eq, mem_iUnion, exists_and_left, exists_const_iff] at hx ⊢
    exact ⟨hx.1, ⟨Nonempty.intro y, hx.2.2⟩⟩

  suffices (f.base ⁻¹' W.carrier ∩ c.support).Finite by
    apply Finite.subset this
    intro a ha
    simp only [Opens.carrier_eq_coe, top_eq_univ, mem_iUnion, mem_inter_iff, mem_preimage,
      SetLike.mem_coe, Function.mem_support, ne_eq, exists_and_left, exists_const_iff] at ha ⊢
    exact ⟨ha.1, ha.2.2⟩

  exact pbfinite

/--
The pushforward of an algebraic cycle by a quasicompact morphism.

Note that usually the pushforward is only defined for proper morphisms, and indeed we will need
properness to prove that the pushforward preserves rational equivalence.
-/
noncomputable
def map {Z : Type*} {Y : Scheme.{u}} [Semiring Z] [HasDegree Z]
    {N : Type*} (h : {Y : Scheme.{u}} → Y → N) (f : X ⟶ Y) [qc : QuasiCompact f]
    (c : AlgebraicCycle X Z) : AlgebraicCycle Y Z
    where
  toFun z := (∑ x ∈ (preimageSupport_finite f c z).toFinset, (c x) * mapAux' h f x)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := map_locally_finite h f c z



/-
Here, instead of HomogeneousAddSubgroup, we want to have for a general grading A, that c ∈ A d.
I think this preservation property is not going to be true for an arbitrary grading (i.e. how could
it). It's certainly true for the dimension grading (as proven below),
and this being true should arguably be a condition of being a grading. The thing is, this will not
hold for codimension (since this is somehow a relative thing). Indeed, I think most of the reason
to favour the dimension grading is that there is this niceness w.r.t taking pushforwards (and
pullbacks). So if we want a common abstraction, this probably isn't the property to go for.

It's unclear to me what common property we could even have. Of course, one could argue that
homogeneity in some sense should be preserved, i.e. you may get knocked from A X i to A Y (σ i),
but there is still some mapping here.

I don't really know if we're going to need to have some equidimensionality assumption somewhere tbh.

-/

#check dimensionGrading
#check (fun {X : Scheme} (x : X) ↦ height x)


noncomputable instance : HasDegree ℕ where
  degree := Hom.degree
  degree_one := by simp [Hom.degree]

/--
Pushforward preserves cycles of pure dimension `d`.
-/
noncomputable
def map_homogeneneous {Y : Scheme.{u}} [Semiring Z] [HasDegree Z]
  {d : ℕ∞} (f : X ⟶ Y) [qc : QuasiCompact f]
  (c : dimensionGrading X Z d) : dimensionGrading Y Z d where
    val := map (fun {X : Scheme} (x : X) ↦ height x) f c
    property := by
      simp only [dimensionGrading]
      intro y hy
      simp [map, preimageSupport, mapAux'] at hy
      obtain ⟨x, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
      simp at hx
      have : height x = d := c.2 x hx.1.2
      simp_all

/--
The pushforward of `c` along the identity morphism is `c`.
-/
@[simp]
lemma map_id {Z : Type*} [Semiring Z] [HasDegree Z] (c : AlgebraicCycle X Z) :
    map (fun {X : Scheme} (x : X) ↦ height x) (𝟙 X) c = c := by
   ext z
   have : (c z ≠ 0 ∧ (preimageSupport_finite (𝟙 X) c z).toFinset = {z}) ∨
          (c z = 0 ∧ (preimageSupport_finite (𝟙 X) c z).toFinset = ∅) := by
    simp[preimageSupport_finite, preimageSupport, Finite.toFinset]
    refine Or.elim (em (c z = 0)) (fun o ↦ Or.inr o) (fun o ↦ Or.inl ⟨o, Finset.ext (fun a ↦ ?_)⟩)
    simp only [mem_toFinset, mem_inter_iff, mem_singleton_iff, Function.mem_support, ne_eq,
      Finset.mem_singleton, and_iff_left_iff_imp]
    rintro rfl
    assumption
   suffices (map (fun {X : Scheme} (x : X) ↦ height x) (𝟙 X) c).toFun z = c.toFun z from this
   obtain h | h := this
   all_goals simp only [top_eq_univ, map, mapAux', Scheme.id.base, TopCat.hom_id,
               ContinuousMap.id_apply, ↓reduceIte]
             rw[h.2]
             simp only [HasDegree.degree_one, mul_one, Finset.sum_singleton, Finset.sum_empty]
   · rfl
   · exact h.1.symm

end AlgebraicCycle
