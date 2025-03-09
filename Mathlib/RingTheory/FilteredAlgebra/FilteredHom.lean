/-
Copyright (c) 2025 HuanYu Zheng, Yi Yuan, Weichen Jiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HuanYu Zheng, Yi Yuan, Weichen Jiao
-/
import Mathlib.RingTheory.FilteredAlgebra.AssociatedGraded
/-!
# The filtered ring morphisms on rings

In this file, we define the filtered ring morphisms on rings and prove some basic properties of
them.

# Main definitions

* `FilteredHom` : A morphism between general filtration (filtration of sets) that preserves
both the main and auxiliary filtered structures. This class describes a structure-preserving map
between two filtered sets `IsFiltration FA FA_lt` and `IsFiltration FB FB_lt` (types `A` and `B`).

* `FilteredHom.comp` : The composition of two filtered morphisms
`f : FilteredHom FA FA_lt FB FB_lt` and `g : FilteredHom FB FB_lt FC FC_lt`, resulting in a new
morphism `f.comp g : FilteredHom FA FA_lt FC FC_lt`.

* `FilteredHom.IsStrict` : A strict filtered ring morphism, which is a filtered ring
morphism `f` between filtered rings `IsRingFiltration FR FR_lt` and `IsRingFiltration FS FS_lt`
alongside with the property that `∀ p : ι`, the image of the `p`-th filtration layer of `FR`
and `FR_lt` under `f` is exactly the intersection of the image of `f` with the `p`-th
filtration layer of `FS` and `FS_lt` respectively.

* `FilteredAddGroupHom` : A morphism between filtered abelian groups that preserves both the
group and filtered morphism structures.

* `FilteredAddGroupHom.comp` : The composition of filtered ring morphisms. Given two filtered
abelian group morphisms `f : FilteredAddGroupHom FA FA_lt FB FB_lt` and
`g : FilteredAddGroupHom FB FB_lt FC FC_lt`, their composition `g.comp  f` is defined by composing
the underlying group homomorphisms and ensuring compatibility with the filtration structures.

* `FilteredAddGroupHom.GradedPieceHom` :
The induced morphism on the `i`-th graded piece of the associated graded group
(written as `Gr(i)[f]`, where `f` is the filtered abelian group morphism).
Given a filtered abelian group homomorphism `f : FilteredAddGroupHom FA FA_lt FB FB_lt`, this
function takes an element in the `i`-th graded piece of `FA` (represented as a quotient
`FA i / FA_lt i`) and maps it to the corresponding graded piece of `FB` by applying the group
homomorphism `f`, ensuring that the result lies within the `i`-th filtration layer of `FB`.
The construction respects the quotient equivalence relation, making it a well-defined additive
group homomorphism.

* `FilteredAddGroupHom.AssociatedGradedAddMonoidHom` :
The induced graded group morphism between associated graded groups by giving
the component-wise map `GradedPieceHom f`
(Mathematically, it is `Gr[f] = ⨁ Gr(i)[f]`).

-/
section

variable {ι A B C α β γ: Type*} [Preorder ι] [SetLike α A] [SetLike β B] [SetLike γ C]

variable (FA : ι → α) (FA_lt : outParam <| ι → α) [IsFiltration FA FA_lt]
variable (FB : ι → β) (FB_lt : outParam <| ι → β) [IsFiltration FB FB_lt]
variable (FC : ι → γ) (FC_lt : outParam <| ι → γ) [IsFiltration FC FC_lt]

/-- A morphism between general filtration (filtration of sets) that preserves both the main
and auxiliary filtered structures. This class describes a structure-preserving map between two
filtered sets `IsFiltration FA FA_lt` and `IsFiltration FB FB_lt` (types `A` and `B`).-/
@[ext]
class FilteredHom where
  /-- It is a map from `A` to `B` which maps each `FA i` pieces to corresponding `FB i` pieces, and
  maps `FA_lt i` pieces to corresponding `FB_lt i` pieces -/
  toFun : A → B
  pieces_wise {i a} : a ∈ FA i → toFun a ∈ FB i
  pieces_wise_lt {i a} : a ∈ FA_lt i → toFun a ∈ FB_lt i

instance : FunLike (FilteredHom FA FA_lt FB FB_lt) A B where
  coe f := f.toFun
  coe_injective' _ _ hfg := FilteredHom.ext hfg

namespace FilteredHom

variable (g : FilteredHom FB FB_lt FC FC_lt) (f : FilteredHom FA FA_lt FB FB_lt)

variable {FA FB FC FA_lt FB_lt FC_lt} in

/-- Filtered morphism restricted to its `i`-th filtration layer.-/
def piece_wise_hom (i : ι) : FA i → FB i :=
  Subtype.map f (fun _ ha ↦ f.pieces_wise ha)

/-- The composition of two filtered morphisms,
obtained from the composition of the underlying function.-/
def comp : FilteredHom FA FA_lt FC FC_lt := {
  toFun := g.1.comp f.1
  pieces_wise ha := g.pieces_wise (f.pieces_wise ha)
  pieces_wise_lt ha := g.pieces_wise_lt (f.pieces_wise_lt ha) }

/-- A filtered morphism `f : FilteredHom FA FA_lt FB FB_lt` `IsStrict` if it strictly map
the `p`-th filtration layer of `FA` and `FA_lt` to intersection of the image of `f` with the `p`-th
filtration layer of `FB` and `FB_lt` respectively, for every `p : ι`.-/
class IsStrict (f : outParam <| FilteredHom FA FA_lt FB FB_lt) : Prop where
  strict {p y} : y ∈ (FB p) → y ∈ Set.range f.toFun → y ∈ f.toFun '' (FA p)
  strict_lt {p y} : y ∈ (FB_lt p) → y ∈ Set.range f.toFun → y ∈ f.toFun '' (FA_lt p)

end FilteredHom

end

section

variable {ι A B C α β γ: Type*} [SetLike α A] [SetLike β B] [SetLike γ C]

variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

variable (FA : ι → α) (FA_lt : outParam <| ι → α)
variable (FB : ι → β) (FB_lt : outParam <| ι → β)
variable (FC : ι → γ) (FC_lt : outParam <| ι → γ)

/-- A morphism between filtered abelian groups that preserves both the
group and filtered morphism structures. -/
class FilteredAddGroupHom extends FilteredHom FA FA_lt FB FB_lt, A →+ B

/-- Reinterpret a `FilteredAddGroupHom` as a `AddMonoidHom`. -/
add_decl_doc FilteredAddGroupHom.toAddMonoidHom

instance : Coe (FilteredAddGroupHom FA FA_lt FB FB_lt) (FilteredHom FA FA_lt FB FB_lt) :=
  ⟨fun a ↦ a.toFilteredHom⟩

instance : CoeOut (FilteredAddGroupHom FA FA_lt FB FB_lt) (A →+ B) :=
  ⟨fun a ↦ a.toAddMonoidHom⟩

namespace FilteredAddGroupHom

variable  (g : FilteredAddGroupHom FB FB_lt FC FC_lt) (f : FilteredAddGroupHom FA FA_lt FB FB_lt)

variable {FA FB FC FA_lt FB_lt FC_lt}

/-- The composition of filtered abelian group morphisms,
obtained from the composition of underlying group homomorphisms.-/
def comp : FilteredAddGroupHom FA FA_lt FC FC_lt where
  __ := g.toAddMonoidHom.comp f.toAddMonoidHom
  pieces_wise ha := g.pieces_wise (f.pieces_wise ha)
  pieces_wise_lt ha := g.pieces_wise_lt (f.pieces_wise_lt ha)

variable [AddSubgroupClass α A]

lemma IsStrict.strict [FilteredHom.IsStrict FA FA_lt FB FB_lt f] {p y} :
    y ∈ (FB p) → y ∈ f.range → y ∈ AddSubgroup.map f (AddSubgroup.ofClass (FA p)) :=
  FilteredHom.IsStrict.strict

lemma IsStrict.strict_lt [FilteredHom.IsStrict FA FA_lt FB FB_lt f] {p y} :
    y ∈ (FB_lt p) → y ∈ f.range → y ∈ AddSubgroup.map f (AddSubgroup.ofClass (FA_lt p)) :=
  FilteredHom.IsStrict.strict_lt

variable [AddSubgroupClass β B] [AddSubgroupClass γ C]

/-- A filtered abelian group morphism restricted to its `i`-th filtration layer.-/
abbrev piece_wise_hom (i : ι) : FA i →+ FB i where
  toFun := FilteredHom.piece_wise_hom f.toFilteredHom i
  map_zero' := SetCoe.ext f.toAddMonoidHom.map_zero
  map_add' a b := SetCoe.ext (f.toAddMonoidHom.map_add a b)

/-- Additive group homomorphism between graded pieces induced by
`f : FilteredAddGroupHom FA FA_lt FB FB_lt`. -/
def GradedPieceHom (i : ι) : GradedPiece FA FA_lt i →+ GradedPiece FB FB_lt i :=
  QuotientAddGroup.map _ _ (f.piece_wise_hom i)
    (fun x hx ↦ by simpa using f.pieces_wise_lt hx)

@[inherit_doc]
scoped[FilteredAddGroupHom] notation:9000 "Gr(" i ")[" f "]" => GradedPieceHom f i

@[simp]
lemma GradedPieceHom_apply_mk_eq_mk_piece_wise_hom {i : ι} (x : FA i) :
    Gr(i)[f] (GradedPiece.mk FA FA_lt x) = (GradedPiece.mk FB FB_lt (f.piece_wise_hom i x)) :=
  rfl

lemma GradedPieceHom_comp_apply (i : ι) (x : GradedPiece FA FA_lt i) :
    Gr(i)[g] (Gr(i)[f] x) = Gr(i)[g.comp f] x :=
  QuotientAddGroup.induction_on x (fun _ ↦ rfl)

lemma GradedPieceHom_comp (i : ι) : Gr(i)[g].comp Gr(i)[f]  = Gr(i)[g.comp f] := by
  ext x
  exact GradedPieceHom_comp_apply g f i x

/-- Additive group homomorphism (between direct sum of graded pieces) induced by
`GradedPieceHom i f` where `f : FilteredAddGroupHom FA FA_lt FB FB_lt`. -/
noncomputable def AssociatedGradedAddMonoidHom :
    (AssociatedGraded FA FA_lt) →+ (AssociatedGraded FB FB_lt) :=
  DirectSum.map (GradedPieceHom f)

@[inherit_doc]
scoped[FilteredAddGroupHom] notation:9000 "Gr[" f "]" => AssociatedGradedAddMonoidHom f

@[simp]
lemma AssociatedGradedAddMonoidHom_apply (x : AssociatedGraded FA FA_lt) (i : ι) :
    (Gr[f] x) i = Gr(i)[f] (x i) := rfl

@[simp]
lemma AssociatedGradedAddMonoidHom_apply_of [DecidableEq ι] {i : ι} (x : GradedPiece FA FA_lt i) :
    (Gr[f] (AssociatedGraded.of x)) = AssociatedGraded.of (Gr(i)[f] x) :=
  DirectSum.map_of (GradedPieceHom f) i x

theorem AssociatedGradedAddMonoidHom_comp_eq_comp: Gr[g].comp Gr[f] = Gr[g.comp f] := by
  apply Eq.trans (DirectSum.map_comp (GradedPieceHom f) (GradedPieceHom g)).symm
  simp only [GradedPieceHom_comp, AssociatedGradedAddMonoidHom]

end FilteredAddGroupHom

end
