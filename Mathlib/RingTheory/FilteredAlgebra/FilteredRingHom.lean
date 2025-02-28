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
@[ext]
class FilteredHom where
  /-- It is a map from `A` to `B` which maps each `FA i` pieces to corresponding `FB i` pieces, and
  maps `FA_lt i` pieces to corresponding `FB_lt i` pieces -/
  toFun : A → B
  pieces_wise {i a} : a ∈ FA i → toFun a ∈ FB i
  pieces_wise_lt {i a} : a ∈ FA_lt i → toFun a ∈ FB_lt i

instance : CoeOut (FilteredHom FA FA_lt FB FB_lt) (A → B) :=
  ⟨fun a ↦ a.toFun⟩

instance : FunLike (FilteredHom FA FA_lt FB FB_lt) A B where
  coe f := f.toFun
  coe_injective' _ _ hfg := FilteredHom.ext hfg

namespace FilteredHom

variable (g : FilteredHom FB FB_lt FC FC_lt) (f : FilteredHom FA FA_lt FB FB_lt)

variable {FA FB FC FA_lt FB_lt FC_lt} in

def piece_wise_hom (i : ι) : FA i → FB i :=
  fun a ↦ ⟨f.toFun a, f.pieces_wise a.2⟩

/-- -/
def comp : FilteredHom FA FA_lt FC FC_lt := {
  toFun := g.1.comp f.1
  pieces_wise := fun ha ↦ g.pieces_wise (f.pieces_wise ha)
  pieces_wise_lt := fun ha ↦ g.pieces_wise_lt (f.pieces_wise_lt ha) }

/-- -/
class IsStrict (f : outParam <| FilteredHom FA FA_lt FB FB_lt) : Prop where
  strict {p y} : y ∈ (FB p) → y ∈ Set.range f.toFun → y ∈ f.toFun '' (FA p)
  strict_lt {p y} : y ∈ (FB_lt p) → y ∈ Set.range f.toFun → y ∈ f.toFun '' (FA_lt p)

end FilteredHom

end

section

variable {ι A B C α β γ: Type*} [Preorder ι] [SetLike α A] [SetLike β B] [SetLike γ C]

variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

variable (FA : ι → α) (FA_lt : outParam <| ι → α) [IsFiltration FA FA_lt]
variable (FB : ι → β) (FB_lt : outParam <| ι → β) [IsFiltration FB FB_lt]
variable (FC : ι → γ) (FC_lt : outParam <| ι → γ) [IsFiltration FC FC_lt]

/-- -/
class FilteredAddMonoidHom extends FilteredHom FA FA_lt FB FB_lt, A →+ B

instance : Coe (FilteredAddMonoidHom FA FA_lt FB FB_lt) (FilteredHom FA FA_lt FB FB_lt) :=
  ⟨fun a ↦ a.toFilteredHom⟩

namespace FilteredAddMonoidHom

variable  (g : FilteredAddMonoidHom FB FB_lt FC FC_lt) (f : FilteredAddMonoidHom FA FA_lt FB FB_lt)

variable {FA FB FC FA_lt FB_lt FC_lt}

/-- -/
def comp : FilteredAddMonoidHom FA FA_lt FC FC_lt where
  __ := g.toAddMonoidHom.comp f.toAddMonoidHom
  pieces_wise := fun ha ↦ g.pieces_wise (f.pieces_wise ha)
  pieces_wise_lt := fun ha ↦ g.pieces_wise_lt (f.pieces_wise_lt ha)

variable [AddSubgroupClass α A] [AddSubgroupClass β B] [AddSubgroupClass γ C]

abbrev piece_wise_hom (i : ι) : FA i →+ FB i where
  toFun := FilteredHom.piece_wise_hom f.toFilteredHom i
  map_zero' := SetCoe.ext f.toAddMonoidHom.map_zero
  map_add' a b := SetCoe.ext (f.toAddMonoidHom.map_add a b)

/-- -/
def GradedPieceHom (i : ι) : GradedPiece FA FA_lt i →+ GradedPiece FB FB_lt i :=
  QuotientAddGroup.map _ _ (f.piece_wise_hom i)
    (fun x hx ↦ by simpa using f.pieces_wise_lt hx)

@[inherit_doc]
scoped[FilteredAddMonoidHom] notation:9000 "Gr(" i ")[" f "]" => GradedPieceHom f i

omit [Preorder ι] [IsFiltration FA FA_lt] [IsFiltration FB FB_lt] [IsFiltration FC FC_lt] in
lemma GradedPieceHom_comp_apply (x : AssociatedGraded FA FA_lt) (i : ι) :
    Gr(i)[g] (Gr(i)[f] (x i)) = Gr(i)[g.comp f] (x i) := QuotientAddGroup.induction_on (x i) <|
  fun y ↦ by
  simp only [GradedPieceHom, QuotientAddGroup.map_mk]
  rfl

/-- -/
noncomputable def AssociatedGradedAddMonoidHom :
    (AssociatedGraded FA FA_lt) →+ (AssociatedGraded FB FB_lt) :=
  DFinsupp.mapRange.addMonoidHom (GradedPieceHom f)

@[inherit_doc]
scoped[FilteredAddMonoidHom] notation:9000 "Gr[" f "]" => AssociatedGradedAddMonoidHom f

omit [Preorder ι] [IsFiltration FA FA_lt] [IsFiltration FB FB_lt] in
@[simp]
lemma AssociatedGradedAddMonoidHom_apply (x : AssociatedGraded FA FA_lt) (i : ι) :
    (Gr[f] x) i = Gr(i)[f] (x i) := rfl

omit [Preorder ι] [IsFiltration FA FA_lt] [IsFiltration FB FB_lt] in
@[simp]
lemma AssociatedGradedAddMonoidHom_apply_of [DecidableEq ι] (i : ι) (x : GradedPiece FA FA_lt i) :
    (Gr[f] (AssociatedGraded.of x)) = AssociatedGraded.of (Gr(i)[f] x) := by
  convert DFinsupp.mapRange_single
  simp

omit [Preorder ι] [IsFiltration FA FA_lt] [IsFiltration FB FB_lt] [IsFiltration FC FC_lt] in
theorem AssociatedGradedAddMonoidHom_comp: Gr[g].comp Gr[f] = Gr[g.comp f] := by
  ext x i
  simpa [AssociatedGradedAddMonoidHom, AssociatedGradedAddMonoidHom_apply]
    using GradedPieceHom_comp_apply g f _ _

end FilteredAddMonoidHom

end

section

variable {ι R S T γ σ τ : Type*} [OrderedAddCommMonoid ι]

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S]
variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T]

/-- -/
class FilteredRingHom extends FilteredAddMonoidHom FR FR_lt FS FS_lt, R →+* S

instance : Coe (FilteredRingHom FR FR_lt FS FS_lt) (FilteredAddMonoidHom FR FR_lt FS FS_lt) :=
  ⟨fun a ↦ a.toFilteredAddMonoidHom⟩

namespace FilteredRingHom

variable (g : FilteredRingHom FS FS_lt FT FT_lt) (f : FilteredRingHom FR FR_lt FS FS_lt)

variable {FR FS FT FR_lt FS_lt FT_lt}

/-- -/
def comp : FilteredRingHom FR FR_lt FT FT_lt where
  __ := g.toRingHom.comp f.toRingHom
  pieces_wise := fun ha ↦ g.pieces_wise (f.pieces_wise ha)
  pieces_wise_lt := fun ha ↦ g.pieces_wise_lt (f.pieces_wise_lt ha)

variable [AddSubgroupClass γ R] [AddSubgroupClass σ S] [AddSubgroupClass τ T]

/-- -/
abbrev piece_wise_hom (i : ι) : FR i →+ FS i :=
  FilteredAddMonoidHom.piece_wise_hom f.toFilteredAddMonoidHom i

/-- -/
abbrev GradedPieceHom (i : ι) : GradedPiece FR FR_lt i →+ GradedPiece FS FS_lt i :=
  f.1.GradedPieceHom i

@[inherit_doc]
scoped[FilteredRingHom] notation:9000 "Gr(" i ")[" f "]" => GradedPieceHom f i

omit [OrderedAddCommMonoid ι] in
lemma GradedPieceHom_comp_apply (x : AssociatedGraded FR FR_lt) (i : ι) :
    Gr(i)[g] (Gr(i)[f] (x i)) = Gr(i)[g.comp f] (x i) :=
  FilteredAddMonoidHom.GradedPieceHom_comp_apply g.1 f.1 x i

section DirectSum

open DirectSum

variable [OrderedAddCommMonoid ι] [hasGMul FR FR_lt] [hasGMul FS FS_lt] [hasGMul FT FT_lt]

/-- -/
noncomputable def AssociatedGradedRingHom [DecidableEq ι] :
    (AssociatedGraded FR FR_lt) →+* (AssociatedGraded FS FS_lt) where
  __ := f.1.AssociatedGradedAddMonoidHom
  map_one' := by
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    show (FilteredAddMonoidHom.AssociatedGradedAddMonoidHom f.1)
      (AssociatedGraded.of (1 : GradedPiece FR FR_lt 0)) =
      AssociatedGraded.of (1 : GradedPiece FS FS_lt 0)
    rw [FilteredAddMonoidHom.AssociatedGradedAddMonoidHom_apply_of]
    show AssociatedGraded.of ⟦(⟨f.toRingHom 1, _⟩ : FS 0)⟧ = AssociatedGraded.of ⟦⟨1, _⟩⟧
    simp [RingHom.map_one f.toRingHom]
  map_mul' a b := DirectSum.induction_on a (by simp)
    (DirectSum.induction_on b (by simp)
      (fun j y' i x' ↦ QuotientAddGroup.induction_on x' <| QuotientAddGroup.induction_on y' <|
          fun y x ↦ by
          simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, DirectSum.of_mul_of,
            FilteredAddMonoidHom.AssociatedGradedAddMonoidHom_apply_of]
          congr
          show Gr(i + j)[f] (GradedPiece.mk FR FR_lt ⟨x.1 * y.1, _⟩) =
            GradedPiece.mk FS FS_lt ⟨f.toRingHom x.1 * f.toRingHom y.1, _⟩
          simp only [FilteredAddMonoidHom.GradedPieceHom, GradedPiece.mk_eq,
            QuotientAddGroup.map_mk]
          congr
          exact SetCoe.ext (map_mul f.toRingHom x.1 y.1))
      (by intro x y h1 h2 i z
          simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add] at h1 h2 ⊢
          rw [mul_add, map_add, mul_add, h1 i z, h2 i z]))
    (DirectSum.induction_on b (by simp)
      (by intro i z x y h1 h2
          simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add] at h1 h2 ⊢
          rw [add_mul, map_add, add_mul, h1, h2])
      (by intro x y h1 h2 u v
          simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add]
          intro h3 h4
          rw [add_mul, map_add, add_mul, h3, h4]))

@[inherit_doc]
scoped[FilteredRingHom] notation:9000 "Gr[" f "]" => AssociatedGradedRingHom f

variable [DecidableEq ι]

set_option linter.unusedSectionVars false in
theorem AssociatedGradedRingHom_apply (x : AssociatedGraded FR FR_lt) (i : ι) :
    (Gr[f] x) i = Gr(i)[f] (x i) := rfl

set_option linter.unusedSectionVars false in
theorem AssociatedGradedRingHom_comp: Gr[g].comp Gr[f] = Gr[g.comp f] :=
  RingHom.ext <| fun x ↦ congrFun
  (congrArg DFunLike.coe (FilteredAddMonoidHom.AssociatedGradedAddMonoidHom_comp g.1 f.1)) x

end DirectSum

end FilteredRingHom

end
