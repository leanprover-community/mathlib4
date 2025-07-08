/-
Copyright (c) 2025 HuanYu Zheng, Yi Yuan, Weichen Jiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HuanYu Zheng, Yi Yuan, Weichen Jiao, Nailin Guan
-/
import Mathlib.RingTheory.FilteredAlgebra.AssociatedGraded
/-!
# The filtered ring morphisms on rings

In this file, we define the filtered ring morphisms on rings and prove some basic properties of
them.

# Main definitions

* `FilteredHom` : Function that preserve the filtered structrue.

* `FilteredHom.piece_wise_hom` : The filtered abelian group morphism obtained from the
restriction of a `FilteredHom` to its `i`-th filtration.

* `FilteredHom.IsStrict` : A filtered morphism `f : FilteredHom FA FA_lt FB FB_lt` `IsStrict` if
it strictly map the `p`-th filtration of `FA` and `FA_lt` to the intersection of the image of `f`
with the `p`-th filtration of `FB` and `FB_lt` respectively, for every `p : ι`.

* `FilteredAddGroupHom` : A morphism between filtered abelian groups that preserves both the
group and filtered structures.

* `FilteredAddGroupHom.GradedPieceHom` : Additive group homomorphism between graded pieces,
induced by the `piece_wise_hom` of a `FilteredAddGroupHom`.

* `FilteredAddGroupHom.AssociatedGradedAddMonoidHom` :
The induced graded additive group morphism between associated graded additive groups,
obtained from the component-wise map `GradedPieceHom f`.

-/
section

section

/-- The class of functions that preserve the filtered structrue. -/
class FilteredHomClass (F : Type*) {A B α β ι : Type*} [FunLike F A B]
    [SetLike α A] (FA : ι → α) (FA_lt : outParam <| ι → α)
    [SetLike β B] (FB : ι → β) (FB_lt : outParam <| ι → β) : Prop where
  pieces_wise (f : F) {i a} : a ∈ FA i → f a ∈ FB i
  pieces_wise_lt (f : F) {i a} : a ∈ FA_lt i → f a ∈ FB_lt i

end

variable {ι A B C α β γ : Type*} [SetLike α A] [SetLike β B] [SetLike γ C]

variable (FA : ι → α) (FA_lt : outParam <| ι → α)
variable (FB : ι → β) (FB_lt : outParam <| ι → β)
variable (FC : ι → γ) (FC_lt : outParam <| ι → γ)

/-- Function that preserve the filtered structrue. -/
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

instance : FilteredHomClass (FilteredHom FA FA_lt FB FB_lt) FA FA_lt FB FB_lt where
  pieces_wise f := f.pieces_wise
  pieces_wise_lt f := f.pieces_wise_lt

namespace FilteredHom

variable (g : FilteredHom FB FB_lt FC FC_lt) (f : FilteredHom FA FA_lt FB FB_lt)

variable {FA FB FA_lt FB_lt} in
/-- The filtered abelian group morphism obtained from the
restriction of a `FilteredHom` to its `i`-th filtration. -/
def piece_wise_hom (i : ι) : FA i → FB i :=
  Subtype.map f (fun _ ha ↦ f.pieces_wise ha)

/-- The identity map as a `FilteredHom` of same filtration. -/
def id : FilteredHom FA FA_lt FA FA_lt where
  toFun := _root_.id
  pieces_wise ha := ha
  pieces_wise_lt ha := ha

variable {FA FB FC FA_lt FB_lt FC_lt} in
/-- The composition of two filtered morphisms,
obtained from the composition of the underlying function. -/
def comp : FilteredHom FA FA_lt FC FC_lt where
  toFun := g.1.comp f.1
  pieces_wise ha := g.pieces_wise (f.pieces_wise ha)
  pieces_wise_lt ha := g.pieces_wise_lt (f.pieces_wise_lt ha)

/-- A filtered morphism `f : FilteredHom FA FA_lt FB FB_lt` `IsStrict` if it strictly map
the `p`-th filtration of `FA` and `FA_lt` to the intersection of the image of `f` with
the `p`-th filtration of `FB` and `FB_lt` respectively, for every `p : ι`. -/
class IsStrict (f : outParam <| FilteredHom FA FA_lt FB FB_lt) : Prop where
  strict {p y} : y ∈ (FB p) → y ∈ Set.range f.toFun → y ∈ f.toFun '' (FA p)
  strict_lt {p y} : y ∈ (FB_lt p) → y ∈ Set.range f.toFun → y ∈ f.toFun '' (FA_lt p)

end FilteredHom

end

section

variable {ι A B C α β γ : Type*} [SetLike α A] [SetLike β B] [SetLike γ C]

variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

variable (FA : ι → α) (FA_lt : outParam <| ι → α)
variable (FB : ι → β) (FB_lt : outParam <| ι → β)
variable (FC : ι → γ) (FC_lt : outParam <| ι → γ)

/-- A morphism between filtered abelian groups that preserves both the
group and filtered structures. -/
@[ext]
class FilteredAddGroupHom extends FilteredHom FA FA_lt FB FB_lt, A →+ B

/-- Reinterpret a `FilteredAddGroupHom` as a `AddMonoidHom`. -/
add_decl_doc FilteredAddGroupHom.toAddMonoidHom

instance : Coe (FilteredAddGroupHom FA FA_lt FB FB_lt) (FilteredHom FA FA_lt FB FB_lt) :=
  ⟨fun a ↦ a.toFilteredHom⟩

instance : FunLike (FilteredAddGroupHom FA FA_lt FB FB_lt) A B where
  coe f := f.toFun
  coe_injective' _ _ h := FilteredAddGroupHom.ext h

instance : AddMonoidHomClass (FilteredAddGroupHom FA FA_lt FB FB_lt) A B where
  map_add f := map_add f.toAddMonoidHom
  map_zero f := map_zero f.toAddMonoidHom

instance : FilteredHomClass (FilteredAddGroupHom FA FA_lt FB FB_lt) FA FA_lt FB FB_lt where
  pieces_wise f := f.pieces_wise
  pieces_wise_lt f := f.pieces_wise_lt

namespace FilteredAddGroupHom

/-- The identity map as a `FilteredAddGroupHom` of same filtration. -/
def id : FilteredAddGroupHom FA FA_lt FA FA_lt where
  __ := AddMonoidHom.id A
  pieces_wise ha := ha
  pieces_wise_lt ha := ha

variable (g : FilteredAddGroupHom FB FB_lt FC FC_lt) (f : FilteredAddGroupHom FA FA_lt FB FB_lt)

variable {FA FB FC FA_lt FB_lt FC_lt}

/-- The composition of filtered abelian group morphisms,
obtained from the composition of underlying group homomorphisms. -/
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

/-- The `AddMonoidHom` version of `FilteredHom.piece_wise_hom`. -/
abbrev piece_wise_hom (i : ι) : FA i →+ FB i where
  toFun := FilteredHom.piece_wise_hom f.toFilteredHom i
  map_zero' := SetCoe.ext f.toAddMonoidHom.map_zero
  map_add' a b := SetCoe.ext (f.toAddMonoidHom.map_add a b)

/-- Additive group homomorphism between graded pieces,
induced by the `piece_wise_hom` of a `FilteredAddGroupHom`. -/
def GradedPieceHom (i : ι) : GradedPiece FA FA_lt i →+ GradedPiece FB FB_lt i :=
  QuotientAddGroup.map _ _ (f.piece_wise_hom i)
    (fun x hx ↦ by simpa using f.pieces_wise_lt hx)

@[inherit_doc]
scoped[FilteredAddGroupHom] notation:9000 "Gr+(" i ")[" f "]" => GradedPieceHom f i

@[simp]
lemma GradedPieceHom_apply_mk_eq_mk_piece_wise_hom {i : ι} (x : FA i) :
    Gr+(i)[f] (GradedPiece.mk FA FA_lt x) = (GradedPiece.mk FB FB_lt (f.piece_wise_hom i x)) :=
  rfl

lemma GradedPieceHom_comp_apply (i : ι) (x : GradedPiece FA FA_lt i) :
    Gr+(i)[g] (Gr+(i)[f] x) = Gr+(i)[g.comp f] x :=
  QuotientAddGroup.induction_on x (fun _ ↦ rfl)

lemma GradedPieceHom_comp (i : ι) : Gr+(i)[g].comp Gr+(i)[f]  = Gr+(i)[g.comp f] := by
  ext x
  exact GradedPieceHom_comp_apply g f i x

/-- The induced graded additive group morphism between associated graded additive groups,
obtained from the component-wise map `GradedPieceHom f`. -/
noncomputable def AssociatedGradedAddMonoidHom :
    (AssociatedGraded FA FA_lt) →+ (AssociatedGraded FB FB_lt) :=
  DirectSum.map (GradedPieceHom f)

@[inherit_doc]
scoped[FilteredAddGroupHom] notation:9000 "Gr+[" f "]" => AssociatedGradedAddMonoidHom f

@[simp]
lemma AssociatedGradedAddMonoidHom_apply (x : AssociatedGraded FA FA_lt) (i : ι) :
    (Gr+[f] x) i = Gr+(i)[f] (x i) := rfl

@[simp]
lemma AssociatedGradedAddMonoidHom_apply_of [DecidableEq ι] {i : ι} (x : GradedPiece FA FA_lt i) :
    (Gr+[f] (AssociatedGraded.of x)) = AssociatedGraded.of (Gr+(i)[f] x) :=
  DirectSum.map_of (GradedPieceHom f) i x

theorem AssociatedGradedAddMonoidHom_comp_eq_comp: Gr+[g].comp Gr+[f] = Gr+[g.comp f] := by
  apply Eq.trans (DirectSum.map_comp (GradedPieceHom f) (GradedPieceHom g)).symm
  simp only [GradedPieceHom_comp, AssociatedGradedAddMonoidHom]

end FilteredAddGroupHom

end
