/-
Copyright (c) 2025 HuanYu Zheng, Yi Yuan, Weichen Jiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HuanYu Zheng, Yi Yuan, Weichen Jiao
-/
import Mathlib.RingTheory.FilteredAlgebra.AssociatedGraded
import Mathlib.Algebra.Ring.Hom.Defs
/-!
# The filtered ring morphisms on rings
In this file, we define the filtered ring morphisms on rings and prove some basic properties of
them.

# Main definitions

* `FilteredHom` : Defines a morphism between general filtration (filtration of sets) that preserves
both the main and auxiliary filtered structures. This class describes a structure-preserving map
between two filtered sets `IsFiltration FA FA_lt` and `IsFiltration FB FB_lt` (types `A` and `B`).

* FilteredHom.comp : Defines the composition of two filtered morphisms
`f : FilteredHom FA FA_lt FB FB_lt` and `g : FilteredHom FB FB_lt FC FC_lt`, resulting in a new
morphism `f ∘ g : FilteredHom FA FA_lt FC FC_lt`.

* `FilteredRingHom` : Defines a morphism between filtered rings that preserves both the ring and
filtered morphism structures. This class combines the properties of a ring homomorphism and a
filtered morphism, ensuring that both the structure of the ring and its filtration are maintained
under the morphism.

`R →+* S` retrieves the ring homomorphism component of a filtered ring homomorphism,
which is responsible for preserving the ring structure between the source and target rings.
It allows direct access to the ring-theoretic aspects of the morphism, enabling operations
and proofs that focus on the algebraic structure independent of the filtration layers.

* `FilteredRingHom.IsStrict` : Defines a strict morphism, which is a filtered ring morphism `f`
between filtered rings `IsRingFiltration FR FR_lt` and `IsRingFiltration FS FS_lt`. It is strict if
`∀ p : ι`, the image of the `p`-th filtration layer of `FR` and `FR_lt` under `f` is exactly the
intersection of the image of `f` with the `p`-th filtration layer of `FS` and `FS_lt`, respectively.

* `FilteredRingHom.comp` : Defines the composition of filtered ring morphisms. Given two filtered
morphisms `f : FilteredRingHom FR FR_lt FS FS_lt` and `g : FilteredRingHom FS FS_lt FT FT_lt`, their
composition `g ∘ f` is defined by composing the underlying ring homomorphisms and ensuring
compatibility with the filtration structures.

* `Gf` : Defines the induced morphism on the `i`-th graded piece of the associated graded ring.
**Mathematically, it is `(Gf f i) ⟦x⟧ = ⟦f.toRingHom x⟧`**
(`x : FR i`, `⟦a⟧ : GradedPiece FR FR_lt i`)
Given a filtered ring homomorphism `f : FilteredRingHom FR FR_lt FS FS_lt`, this function takes an
element in the `i`-th graded piece of `FR` (represented as a quotient `FR i / FR_lt i`) and maps it
to the corresponding graded piece of `FS` by applying the ring homomorphism `f`, ensuring that the
result lies within the `i`-th filtration layer of `FS`. The construction respects the quotient
equivalence relation, making it a well-defined additive group homomorphism.

* `G` : Defines the induced graded ring morphism between associated graded rings.
**Mathematically, it is `G f = ⨁ Gf f i`**
Specifically, given a filtered ring morphism `f : FilteredRingHom FR FR_lt FS FS_lt`, this function
constructs an AddSubgroup homomorphism `G f` between the associated graded modules
`⨁ (FR i / FR_lt i)` and `⨁ (FS i / FS_lt i)` by applying `Gf f i` component-wise to each graded
piece and combining the results into a direct sum of additive group homomorphisms.
-/
section FilteredHom

variable {ι A B C α β σ: Type*} [Preorder ι] [SetLike α A] [SetLike β B] [SetLike σ C]

variable (FA : ι → α) (FA_lt : outParam <| ι → α) [IsFiltration FA FA_lt]
variable (FB : ι → β) (FB_lt : outParam <| ι → β) [IsFiltration FB FB_lt]
variable (FC : ι → σ) (FC_lt : outParam <| ι → σ) [IsFiltration FC FC_lt]

/-- Defines a morphism between general filtration (filtration of sets) that preserves both the main
and auxiliary filtered structures. This class describes a structure-preserving map between two
filtered sets `IsFiltration FA FA_lt` and `IsFiltration FB FB_lt` (types `A` and `B`).-/
class FilteredHom where
  /-- It is a map from `A` to `B` which maps each `FA i` pieces to corresponding `FB i` pieces, and
  maps `FA_lt i` pieces to corresponding `FB_lt i` pieces -/
  toFun : A → B
  pieces_wise : ∀ i : ι, ∀ a ∈ FA i, toFun a ∈ FB i
  pieces_wise_lt : ∀ i : ι, ∀ a ∈ FA_lt i, toFun a ∈ FB_lt i

variable (f : FilteredHom FA FA_lt FB FB_lt) (g : FilteredHom FB FB_lt FC FC_lt)

variable {FA FB FC FA_lt FB_lt FC_lt} in

/-- Defines the composition of two filtered morphisms `f : FilteredHom FA FA_lt FB FB_lt` and
`g : FilteredHom FB FB_lt FC FC_lt`, resulting in a new morphism
`f ∘ g : FilteredHom FA FA_lt FC FC_lt`.-/
def FilteredHom.comp : FilteredHom FA FA_lt FC FC_lt := {
  toFun := g.1.comp f.1
  pieces_wise := fun i a ha ↦ g.pieces_wise i (f.1 a) (f.pieces_wise i a ha)
  pieces_wise_lt := fun i a ha ↦ g.pieces_wise_lt i (f.1 a) (f.pieces_wise_lt i a ha)
}

/-- `f ∘ g` denotes the composition defined above. -/
infixl:100 " ∘ " => FilteredHom.comp

end FilteredHom



section FilteredRingHom

variable {ι R S T γ σ τ : Type*} [OrderedAddCommMonoid ι]

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R] [IsRingFiltration FR FR_lt]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S] [IsRingFiltration FS FS_lt]
variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T] [IsRingFiltration FT FT_lt]

/-- Defines a morphism between filtered rings that preserves both the ring and
filtered morphism structures. This class combines the properties of a ring homomorphism and a
filtered morphism, ensuring that both the structure of the ring and its filtration are maintained
under the morphism.
`R →+* S` retrieves the ring homomorphism component of a filtered ring homomorphism,
which is responsible for preserving the ring structure between the source and target rings.
It allows direct access to the ring-theoretic aspects of the morphism, enabling operations
and proofs that focus on the algebraic structure independent of the filtration layers.-/
class FilteredRingHom extends R →+* S, FilteredHom FR FR_lt FS FS_lt


open Set

variable {FR FS FR_lt FS_lt} in
/-- Defines a strict morphism, which is a filtered ring morphism `f` between filtered rings
`IsRingFiltration FR FR_lt` and `IsRingFiltration FS FS_lt`. It is strict if `∀ p : ι`, the image of
the `p`-th filtration layer of `FR` and `FR_lt` under `f` is exactly the intersection of the image
of `f` with the `p`-th filtration layer of `FS` and `FS_lt`, respectively.-/
class FilteredRingHom.IsStrict (f : outParam <| FilteredRingHom FR FR_lt FS FS_lt) : Prop where
  strict : ∀ p : ι, ∀ y : S, y ∈ f.toRingHom '' (FR p) ↔ (y ∈ (FS p) ∧ y ∈ range f.toFun)
  strict_lt : ∀ p : ι, ∀ y : S, y ∈ f.toRingHom '' (FR_lt p) ↔ (y ∈ (FS_lt p) ∧ y ∈ range f.toFun)

variable (g : FilteredRingHom FS FS_lt FT FT_lt) (f : FilteredRingHom FR FR_lt FS FS_lt)

variable {FR FS FT FR_lt FS_lt FT_lt} in
/-- Defines the composition of filtered ring morphisms. Given two filtered morphisms
`f : FilteredRingHom FR FR_lt FS FS_lt` and `g : FilteredRingHom FS FS_lt FT FT_lt`, their
composition `g ∘ f` is defined by composing the underlying ring homomorphisms and ensuring
compatibility with the filtration structures.-/
def FilteredRingHom.comp : FilteredRingHom FR FR_lt FT FT_lt := {
    g.toRingHom.comp f.toRingHom with
  pieces_wise := fun i a ha ↦ g.pieces_wise i (f.toFun a) (f.pieces_wise i a ha)
  pieces_wise_lt := fun i a ha ↦ g.pieces_wise_lt i (f.toFun a) (f.pieces_wise_lt i a ha)
}

/-- `f ∘ g` denotes the composition defined above. -/
infixl:100 " ∘ " => FilteredRingHom.comp

end FilteredRingHom



section DirectSum

open DirectSum

variable {ι R S T σR σS σT : Type*} [DecidableEq ι]

variable [Ring R] {FR : ι → σR} {FR_lt : outParam <| ι → σR} [SetLike σR R] [AddSubgroupClass σR R]
variable [Ring S] {FS : ι → σS} {FS_lt : outParam <| ι → σS} [SetLike σS S] [AddSubgroupClass σS S]
variable [Ring T] (FT : ι → σT) (FT_lt : outParam <| ι → σT) [SetLike σT T] [AddSubgroupClass σT T]

variable (f : FilteredRingHom FR FR_lt FS FS_lt)

/-- Defines the induced morphism on the `i`-th graded piece of the associated graded ring.
**Mathematically, it is `(Gf f i) ⟦x⟧ = ⟦f.toRingHom x⟧`**
(`x : FR i`, `⟦a⟧ : GradedPiece FR FR_lt i`)
Given a filtered ring homomorphism `f : FilteredRingHom FR FR_lt FS FS_lt`, this function takes an
element in the `i`-th graded piece of `FR` (represented as a quotient `FR i / FR_lt i`) and maps it
to the corresponding graded piece of `FS` by applying the ring homomorphism `f`, ensuring that the
result lies within the `i`-th filtration layer of `FS`. The construction respects the quotient
equivalence relation, making it a well-defined additive group homomorphism.-/
def Gf (i : ι) : GradedPiece FR FR_lt i →+ GradedPiece FS FS_lt i where
  toFun := by
    intro a
    use Quotient.lift (fun (s : FR i) ↦ GradedPiece.mk FS FS_lt
      ⟨f.toRingHom s, f.pieces_wise i s <| SetLike.coe_mem s⟩) (fun a b h ↦ ?_) a
    rw [← Quotient.eq_iff_equiv] at h
    have : f.toRingHom (- a + b) ∈ (FS_lt i) :=
      f.pieces_wise_lt i (⟨- a + b, QuotientAddGroup.eq.mp h⟩ : FR_lt i) <| QuotientAddGroup.eq.mp h
    rw [map_add, map_neg] at this
    exact QuotientAddGroup.eq.mpr this
  map_zero' := by
    have : (0 : GradedPiece FR FR_lt i) = ⟦0⟧ := rfl
    simp only[this, Quotient.lift_mk]
    simp only [ZeroMemClass.coe_zero, map_zero, QuotientAddGroup.eq_zero_iff]
    rfl
  map_add' := fun x y ↦ by
    obtain ⟨a, ha⟩ := Quotient.exists_rep x
    obtain ⟨b, hb⟩ := Quotient.exists_rep y
    have : x + y = ⟦a + b⟧ :=
      Mathlib.Tactic.Abel.subst_into_add x y ⟦a⟧ ⟦b⟧ ⟦a + b⟧ (id (Eq.symm ha)) (id (Eq.symm hb)) rfl
    rw[this, ← ha, ← hb]
    simp only [GradedPiece.mk_eq, Quotient.lift_mk]
    congr
    exact RingHom.map_add f.toRingHom a b

variable (g : FilteredRingHom FS FS_lt FT FT_lt)
omit [DecidableEq ι] in
lemma Gf_comp (x : AssociatedGraded FR FR_lt)(i : ι) :
    Gf g i (Gf f i (x i)) = Gf (g ∘ f) i (x i) := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep (x i)
  rw [← ha]
  congr

private noncomputable def GAux : (AssociatedGraded FR FR_lt) → (AssociatedGraded FS FS_lt) :=
  fun a ↦ mk (GradedPiece FS FS_lt) (DFinsupp.support a) <| fun i ↦ (Gf f i) (a i)

private lemma GAux_apply (x : AssociatedGraded FR FR_lt) (i : ι) : (GAux f x) i = Gf f i (x i) := by
  dsimp only [GAux]
  by_cases ixsupp : i ∈ DFinsupp.support x
  · simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, mk_apply_of_mem ixsupp]
  · simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, mk_apply_of_not_mem ixsupp]
    rw [DFinsupp.not_mem_support_iff.mp ixsupp, map_zero]

/-- Defines the induced graded ring morphism between associated graded rings.
**Mathematically, it is `G f = ⨁ Gf f i`**
Specifically, given a filtered ring morphism `f : FilteredRingHom FR FR_lt FS FS_lt`, this function
constructs an AddSubgroup homomorphism `G f` between the associated graded modules
`⨁ (FR i / FR_lt i)` and `⨁ (FS i / FS_lt i)` by applying `Gf f i` component-wise to each graded
piece and combining the results into a direct sum of additive group homomorphisms. -/
noncomputable def G : (AssociatedGraded FR FR_lt) →+ (AssociatedGraded FS FS_lt) where
  toFun := GAux f
  map_zero' := rfl
  map_add' := fun x y ↦ by
    ext i
    simp only [add_apply, GAux_apply, map_add]

theorem G_to_Gf (x : AssociatedGraded FR FR_lt)(i : ι) : (G f x) i = Gf f i (x i) := by
  simp only [G, AddMonoidHom.coe_mk, ZeroHom.coe_mk, GAux_apply]

theorem G_comp: (G g) ∘ (G f) = G (g ∘ f) := by
  ext x i
  simp only [G, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, GAux_apply]
  exact Gf_comp FT FT_lt f g x i

end DirectSum
