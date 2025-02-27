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
morphism `f.comp g : FilteredHom FA FA_lt FC FC_lt`.

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
composition `g.comp  f` is defined by composing the underlying ring homomorphisms and ensuring
compatibility with the filtration structures.

* `Gf` : Defines the induced morphism on the `i`-th graded piece of the associated graded ring.
(Mathematically, it is `(Gf f i) ⟦x⟧ = ⟦f.toRingHom x⟧`)
(`x : FR i`, `⟦a⟧ : GradedPiece FR FR_lt i`)
Given a filtered ring homomorphism `f : FilteredRingHom FR FR_lt FS FS_lt`, this function takes an
element in the `i`-th graded piece of `FR` (represented as a quotient `FR i / FR_lt i`) and maps it
to the corresponding graded piece of `FS` by applying the ring homomorphism `f`, ensuring that the
result lies within the `i`-th filtration layer of `FS`. The construction respects the quotient
equivalence relation, making it a well-defined additive group homomorphism.

* `G` : Defines the induced graded ring morphism between associated graded rings.
(Mathematically, it is `G f = ⨁ Gf f i`)
Specifically, given a filtered ring morphism `f : FilteredRingHom FR FR_lt FS FS_lt`, this function
constructs an AddSubgroup homomorphism `G f` between the associated graded modules
`⨁ (FR i / FR_lt i)` and `⨁ (FS i / FS_lt i)` by applying `Gf f i` component-wise to each graded
piece and combining the results into a direct sum of additive group homomorphisms.
-/
section

variable {ι A B C α β γ: Type*} [Preorder ι] [SetLike α A] [SetLike β B] [SetLike γ C]

variable (FA : ι → α) (FA_lt : outParam <| ι → α) [IsFiltration FA FA_lt]
variable (FB : ι → β) (FB_lt : outParam <| ι → β) [IsFiltration FB FB_lt]
variable (FC : ι → γ) (FC_lt : outParam <| ι → γ) [IsFiltration FC FC_lt]

/-- Defines a morphism between general filtration (filtration of sets) that preserves both the main
and auxiliary filtered structures. This class describes a structure-preserving map between two
filtered sets `IsFiltration FA FA_lt` and `IsFiltration FB FB_lt` (types `A` and `B`).-/
class FilteredHom where
  /-- It is a map from `A` to `B` which maps each `FA i` pieces to corresponding `FB i` pieces, and
  maps `FA_lt i` pieces to corresponding `FB_lt i` pieces -/
  toFun : A → B
  pieces_wise {i a} : a ∈ FA i → toFun a ∈ FB i
  pieces_wise_lt {i a} : a ∈ FA_lt i → toFun a ∈ FB_lt i

instance : CoeOut (FilteredHom FA FA_lt FB FB_lt) (A → B) :=
  ⟨fun a ↦ a.toFun⟩

namespace FilteredHom

variable (f : FilteredHom FA FA_lt FB FB_lt) (g : FilteredHom FB FB_lt FC FC_lt)

variable {FA FB FC FA_lt FB_lt FC_lt} in

def piece_wise_hom (i : ι) : FA i → FB i :=
  fun a ↦ ⟨f.toFun a, f.pieces_wise a.2⟩

/-- Defines the composition of two filtered morphisms `f : FilteredHom FA FA_lt FB FB_lt` and
`g : FilteredHom FB FB_lt FC FC_lt`, resulting in a new morphism
`f.comp g : FilteredHom FA FA_lt FC FC_lt`.-/
def comp : FilteredHom FA FA_lt FC FC_lt := {
  toFun := g.1.comp f.1
  pieces_wise := fun ha ↦ g.pieces_wise (f.pieces_wise ha)
  pieces_wise_lt := fun ha ↦ g.pieces_wise_lt (f.pieces_wise_lt ha) }

/-- Defines a strict morphism, which is a filtered ring morphism `f` between filtered rings
`IsRingFiltration FR FR_lt` and `IsRingFiltration FS FS_lt`. It is strict if `∀ p : ι`, the image of
the `p`-th filtration layer of `FR` and `FR_lt` under `f` is exactly the intersection of the image
of `f` with the `p`-th filtration layer of `FS` and `FS_lt`, respectively.-/
class IsStrict (f : outParam <| FilteredHom FA FA_lt FB FB_lt) : Prop where
  strict {p y} : y ∈ (FB p) → y ∈ Set.range f.toFun → y ∈ f.toFun '' (FA p)
  strict_lt {p y} : y ∈ (FB_lt p) → y ∈ Set.range f.toFun → y ∈ f.toFun '' (FA_lt p)

end FilteredHom

end

section

variable {ι R S T γ σ τ : Type*} [OrderedAddCommMonoid ι]

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S]
variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T]

/-- Defines a morphism between filtered rings that preserves both the ring and
filtered morphism structures. This class combines the properties of a ring homomorphism and a
filtered morphism, ensuring that both the structure of the ring and its filtration are maintained
under the morphism.

`R →+* S` retrieves the ring homomorphism component of a filtered ring homomorphism,
which is responsible for preserving the ring structure between the source and target rings.
It allows direct access to the ring-theoretic aspects of the morphism, enabling operations
and proofs that focus on the algebraic structure independent of the filtration layers.-/
class FilteredRingHom extends R →+* S, FilteredHom FR FR_lt FS FS_lt

namespace FilteredRingHom

variable (g : FilteredRingHom FS FS_lt FT FT_lt) (f : FilteredRingHom FR FR_lt FS FS_lt)

variable {FR FS FT FR_lt FS_lt FT_lt}

abbrev piece_wise_hom (i : ι) [AddSubgroupClass γ R] [AddSubgroupClass σ S]: FR i →+ FS i where
  toFun := FilteredHom.piece_wise_hom f.toFilteredHom i
  map_zero' := SetCoe.ext f.toRingHom.map_zero
  map_add' a b := SetCoe.ext (f.toRingHom.map_add a b)

/-- Defines the composition of filtered ring morphisms. Given two filtered morphisms
`f : FilteredRingHom FR FR_lt FS FS_lt` and `g : FilteredRingHom FS FS_lt FT FT_lt`, their
composition `g.comp f` is defined by composing the underlying ring homomorphisms and ensuring
compatibility with the filtration structures.-/
def comp : FilteredRingHom FR FR_lt FT FT_lt := {
    g.toRingHom.comp f.toRingHom with
  pieces_wise := fun ha ↦ g.pieces_wise (f.pieces_wise ha)
  pieces_wise_lt := fun ha ↦ g.pieces_wise_lt (f.pieces_wise_lt ha) }

end FilteredRingHom

end

section DirectSum

open DirectSum

namespace FilteredRingHom

variable {ι R S T σR σS σT : Type*} [DecidableEq ι]

variable [Ring R] {FR : ι → σR} {FR_lt : outParam <| ι → σR} [SetLike σR R] [AddSubgroupClass σR R]
variable [Ring S] {FS : ι → σS} {FS_lt : outParam <| ι → σS} [SetLike σS S] [AddSubgroupClass σS S]
variable [Ring T] (FT : ι → σT) (FT_lt : outParam <| ι → σT) [SetLike σT T] [AddSubgroupClass σT T]

variable (f : FilteredRingHom FR FR_lt FS FS_lt)

/-- Defines the induced morphism on the `i`-th graded piece of the associated graded ring.
(Mathematically, it is `(Gf f i) ⟦x⟧ = ⟦f.toRingHom x⟧`,
in which `x : FR i`, `⟦a⟧ : GradedPiece FR FR_lt i`)
Given a filtered ring homomorphism `f : FilteredRingHom FR FR_lt FS FS_lt`, this function takes an
element in the `i`-th graded piece of `FR` (represented as a quotient `FR i / FR_lt i`) and maps it
to the corresponding graded piece of `FS` by applying the ring homomorphism `f`, ensuring that the
result lies within the `i`-th filtration layer of `FS`. The construction respects the quotient
equivalence relation, making it a well-defined additive group homomorphism.-/
def GradedPieceHom (i : ι) : GradedPiece FR FR_lt i →+ GradedPiece FS FS_lt i :=
  QuotientAddGroup.map _ _ (piece_wise_hom f i)
    (fun x hx ↦ by simpa using f.pieces_wise_lt hx)

@[inherit_doc]
scoped[FilteredRingHom] notation:9000 "Gr(" i ")[" f "]" => GradedPieceHom f i

variable (g : FilteredRingHom FS FS_lt FT FT_lt)

omit [DecidableEq ι] in
lemma GradedPieceHom_comp_apply (x : AssociatedGraded FR FR_lt) (i : ι) :
    Gr(i)[g] (Gr(i)[f] (x i)) = Gr(i)[g.comp f] (x i) := QuotientAddGroup.induction_on (x i) <|
  fun y ↦ by
  simp only [GradedPieceHom, QuotientAddGroup.map_mk]
  rfl

private noncomputable def AssociatedGradedRingHomAux :
    (AssociatedGraded FR FR_lt) → (AssociatedGraded FS FS_lt) :=
  fun a ↦ DirectSum.mk (GradedPiece FS FS_lt) (DFinsupp.support a) (fun i ↦ Gr(i)[f] (a i))

private lemma AssociatedGradedRingHomAux_apply (x : AssociatedGraded FR FR_lt) (i : ι) :
    (AssociatedGradedRingHomAux f x) i = Gr(i)[f] (x i) := by
  dsimp only [AssociatedGradedRingHomAux]
  by_cases ixsupp : i ∈ DFinsupp.support x
  · simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, mk_apply_of_mem ixsupp]
  · simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, mk_apply_of_not_mem ixsupp]
    rw [DFinsupp.not_mem_support_iff.mp ixsupp, map_zero]

/-- Defines the induced graded ring morphism between associated graded rings.
(Mathematically, it is `G f = ⨁ Gf f i`)
Specifically, given a filtered ring morphism `f : FilteredRingHom FR FR_lt FS FS_lt`, this function
constructs an AddSubgroup homomorphism `G f` between the associated graded modules
`⨁ (FR i / FR_lt i)` and `⨁ (FS i / FS_lt i)` by applying `Gf f i` component-wise to each graded
piece and combining the results into a direct sum of additive group homomorphisms. -/
noncomputable def AssociatedGradedRingHom [OrderedAddCommMonoid ι]
    [hasGMul FR FR_lt] [hasGMul FS FS_lt] :
    (AssociatedGraded FR FR_lt) →+* (AssociatedGraded FS FS_lt) where
  toFun := AssociatedGradedRingHomAux f
  map_zero' := rfl
  map_add' := fun x y ↦ by
    ext i
    simp only [add_apply, AssociatedGradedRingHomAux_apply, map_add]
  map_one' := by
    ext i
    simp only [AssociatedGradedRingHomAux_apply]
    show Gr(i)[f] (((of (GradedPiece FR FR_lt) 0) (1 : GradedPiece FR FR_lt 0)) i) =
      (of (GradedPiece FS FS_lt) 0) (1 : GradedPiece FS FS_lt 0) i
    simp only [DirectSum.of_apply]
    by_cases eq0 : 0 = i
    · have : Gr(0)[f] 1 = 1 := by
        show ⟦((f.piece_wise_hom 0) 1)⟧ = ⟦1⟧
        congr
        exact Subtype.val_injective f.toRingHom.map_one
      convert this
      <;> simp [eq0]
    · simp [eq0]
  map_mul' x y := by

    sorry

@[inherit_doc]
scoped[FilteredRingHom] notation:9000 "Gr[" f "]" => AssociatedGradedRingHom f

variable [OrderedAddCommMonoid ι] [hasGMul FR FR_lt] [hasGMul FS FS_lt] [hasGMul FT FT_lt]

theorem AssociatedGradedRingHom_to_GradedPieceHom (x : AssociatedGraded FR FR_lt) (i : ι) :
    (Gr[f] x) i = Gr(i)[f] (x i) := by
  simp [AssociatedGradedRingHom, AssociatedGradedRingHomAux_apply]

theorem AssociatedGradedRingHom_comp: Gr[g].comp Gr[f] = Gr[g.comp f] := by
  ext x i
  simpa [AssociatedGradedRingHom, AssociatedGradedRingHomAux_apply]
    using GradedPieceHom_comp_apply FT FT_lt f g _ _

end FilteredRingHom

end DirectSum
