/-
Copyright (c) 2025 HuanYu Zheng, Yi Yuan, Weichen Jiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HuanYu Zheng, Yi Yuan, Weichen Jiao, Nailin Guan
-/
import Mathlib.RingTheory.FilteredAlgebra.AssociatedGraded
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
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

* `FilteredRingHom` : A morphism between filtered rings that preserves both the ring and
filtered structures.

* `FilteredRingHom.AssociatedGradedRingHom` :
The induced graded ring morphism between associated graded rings,
obtained from the `AssociatedGradedAddMonoidHom` of a filtered ring morphism.

* `FilteredAlgHom` : A morphism between filtered rings that preserves both the algebra and
filtered morphism structures.

* `FilteredAlgHom.AssociatedGradedAlgHom` :
The induced graded algebra morphism between associated graded algebras,
obtained from the `AssociatedGradedRingHom` of a filtered algebra morphism.

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

section

variable {ι R S T γ σ τ : Type*}

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S]
variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T]

/-- A morphism between filtered rings that preserves both the ring and
filtered structures. -/
@[ext]
class FilteredRingHom extends FilteredAddGroupHom FR FR_lt FS FS_lt, R →+* S

/-- Reinterpret a `FilteredRingHom` as a `RingHom`. -/
add_decl_doc FilteredRingHom.toRingHom

instance : Coe (FilteredRingHom FR FR_lt FS FS_lt) (FilteredAddGroupHom FR FR_lt FS FS_lt) :=
  ⟨fun a ↦ a.toFilteredAddGroupHom⟩

instance : FunLike (FilteredRingHom FR FR_lt FS FS_lt) R S where
  coe f := f.toFun
  coe_injective' _ _ h := FilteredRingHom.ext h

instance : RingHomClass (FilteredRingHom FR FR_lt FS FS_lt) R S where
  map_mul f := f.map_mul
  map_one f := f.map_one
  map_add f := f.map_add
  map_zero f := f.map_zero

instance : FilteredHomClass  (FilteredRingHom FR FR_lt FS FS_lt) FR FR_lt FS FS_lt where
  pieces_wise f := f.pieces_wise
  pieces_wise_lt f := f.pieces_wise_lt

namespace FilteredRingHom

/-- The identity map as a `FilteredRingHom` of same filtration. -/
def id : FilteredRingHom FR FR_lt FR FR_lt where
  __ := RingHom.id R
  pieces_wise ha := ha
  pieces_wise_lt ha := ha

variable (g : FilteredRingHom FS FS_lt FT FT_lt) (f : FilteredRingHom FR FR_lt FS FS_lt)

variable {FR FS FT FR_lt FS_lt FT_lt}

/-- The composition of filtered ring morphisms,
obtained from the composition of the underlying ring homomorphisms. -/
def comp : FilteredRingHom FR FR_lt FT FT_lt where
  __ := g.toRingHom.comp f.toRingHom
  pieces_wise ha := g.pieces_wise (f.pieces_wise ha)
  pieces_wise_lt ha := g.pieces_wise_lt (f.pieces_wise_lt ha)

variable [AddSubgroupClass γ R] [AddSubgroupClass σ S] [AddSubgroupClass τ T]

/-- The `AddMonoidHom` version of `FilteredHom.piece_wise_hom`. -/
abbrev piece_wise_hom (i : ι) : FR i →+ FS i :=
  FilteredAddGroupHom.piece_wise_hom f.toFilteredAddGroupHom i

/-- The `FilteredRingHom` version of `FilteredAddGroupHom.GradedPieceHom`. -/
abbrev GradedPieceHom (i : ι) : GradedPiece FR FR_lt i →+ GradedPiece FS FS_lt i :=
  f.1.GradedPieceHom i

@[inherit_doc]
scoped[FilteredRingHom] notation:9000 "Gr+*(" i ")[" f "]" => GradedPieceHom f i

@[simp]
lemma GradedPieceHom_apply_mk_eq_mk_piece_wise_hom {i : ι} (x : FR i) :
    Gr+*(i)[f] (GradedPiece.mk FR FR_lt x) = (GradedPiece.mk FS FS_lt (f.piece_wise_hom i x)) :=
  rfl

lemma GradedPieceHom_comp_apply (i : ι) (x : GradedPiece FR FR_lt i):
    Gr+*(i)[g] (Gr+*(i)[f] x) = Gr+*(i)[g.comp f] x :=
  FilteredAddGroupHom.GradedPieceHom_comp_apply g.1 f.1 i x

lemma GradedPieceHom_comp (i : ι) : Gr+*(i)[g].comp Gr+*(i)[f] = Gr+*(i)[g.comp f] :=
  FilteredAddGroupHom.GradedPieceHom_comp g.1 f.1 i

open DirectSum

variable [AddMonoid ι] [PartialOrder ι] [hasGMul FR FR_lt] [hasGMul FS FS_lt] [hasGMul FT FT_lt]

/-- The induced graded ring morphism between associated graded rings,
obtained from the `AssociatedGradedAddMonoidHom` of a filtered ring morphism. -/
noncomputable def AssociatedGradedRingHom [DecidableEq ι] :
    (AssociatedGraded FR FR_lt) →+* (AssociatedGraded FS FS_lt) where
  __ := f.1.AssociatedGradedAddMonoidHom
  map_one' := by
    have : (FilteredAddGroupHom.AssociatedGradedAddMonoidHom f.1)
      (AssociatedGraded.of (1 : GradedPiece FR FR_lt 0)) =
      AssociatedGraded.of (1 : GradedPiece FS FS_lt 0) := by
      rw [FilteredAddGroupHom.AssociatedGradedAddMonoidHom_apply_of]
      change AssociatedGraded.of ⟦(⟨f.toRingHom 1, _⟩ : FS 0)⟧ = AssociatedGraded.of ⟦⟨1, _⟩⟧
      simp [RingHom.map_one f.toRingHom]
    simpa
  map_mul' a b := DirectSum.induction_on a (by simp)
    (DirectSum.induction_on b (by simp)
      (fun j y' i x' ↦ by
          induction x' using GradedPiece.induction_on
          induction y' using GradedPiece.induction_on
          rename_i x y
          simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, DirectSum.of_mul_of,
            FilteredAddGroupHom.AssociatedGradedAddMonoidHom_apply_of, GradedMonoid.GMul.mul,
            GradedPiece.gradedMul_def, GradedPieceHom_apply_mk_eq_mk_piece_wise_hom]
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
scoped[FilteredRingHom] notation:9000 "Gr+*[" f "]" => AssociatedGradedRingHom f

variable [DecidableEq ι]

@[simp]
theorem AssociatedGradedRingHom_apply (x : AssociatedGraded FR FR_lt) (i : ι) :
    (Gr+*[f] x) i = Gr+*(i)[f] (x i) := rfl

@[simp]
lemma AssociatedGradedRingHom_apply_of {i : ι} (x : GradedPiece FR FR_lt i) :
    (Gr+*[f] (AssociatedGraded.of x)) = AssociatedGraded.of (Gr+*(i)[f] x) :=
  f.1.AssociatedGradedAddMonoidHom_apply_of x

theorem AssociatedGradedRingHom_comp_eq_comp : Gr+*[g].comp Gr+*[f] = Gr+*[g.comp f] :=
  RingHom.ext <| fun x ↦ congrFun
  (congrArg DFunLike.coe (FilteredAddGroupHom.AssociatedGradedAddMonoidHom_comp_eq_comp g.1 f.1)) x

end FilteredRingHom

end

section

variable {ι R A B C : Type*}

variable [CommRing R] [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
variable (FA : ι → Submodule R A) (FA_lt : outParam <| ι → Submodule R A)
variable (FB : ι → Submodule R B) (FB_lt : outParam <| ι → Submodule R B)
variable (FC : ι → Submodule R C) (FC_lt : outParam <| ι → Submodule R C)

/-- A morphism between filtered rings that preserves both the algebra and
filtered morphism structures. -/
@[ext]
class FilteredAlgHom extends FilteredRingHom FA FA_lt FB FB_lt, A →ₐ[R] B

/-- Reinterpret a `FilteredAlgHom` as a `AlgHom`. -/
add_decl_doc FilteredAlgHom.toAlgHom

instance : Coe (FilteredAlgHom FA FA_lt FB FB_lt) (FilteredRingHom FA FA_lt FB FB_lt) :=
  ⟨fun a ↦ a.toFilteredRingHom⟩

instance : FunLike (FilteredAlgHom FA FA_lt FB FB_lt) A B where
  coe f := f.toFun
  coe_injective' _ _ h := FilteredAlgHom.ext h

instance : AlgHomClass (FilteredAlgHom FA FA_lt FB FB_lt) R A B where
  map_mul f := f.map_mul
  map_one f := f.map_one
  map_add f := f.map_add
  map_zero f := f.map_zero
  commutes f := f.commutes

instance : FilteredHomClass (FilteredAlgHom FA FA_lt FB FB_lt) FA FA_lt FB FB_lt where
  pieces_wise f := f.pieces_wise
  pieces_wise_lt f := f.pieces_wise_lt

namespace FilteredAlgHom

/-- The identity map as a `FilteredAlgHom` of same filtration. -/
def id : FilteredAlgHom FA FA_lt FA FA_lt where
  __ := AlgHom.id R A
  pieces_wise ha := ha
  pieces_wise_lt ha := ha

variable (g : FilteredAlgHom FB FB_lt FC FC_lt) (f : FilteredAlgHom FA FA_lt FB FB_lt)

variable {FA FB FC FA_lt FB_lt FC_lt}

/-- The composition of filtered algebra homomorphism,
obtained from the composition of the underlying `AlgHom`. -/
def comp : FilteredAlgHom FA FA_lt FC FC_lt where
  __ := g.toAlgHom.comp f.toAlgHom
  pieces_wise ha := g.pieces_wise (f.pieces_wise ha)
  pieces_wise_lt ha := g.pieces_wise_lt (f.pieces_wise_lt ha)

/-- A filtered algebra morphism restricted to its `i`-th filtration. -/
abbrev piece_wise_hom (i : ι) : FA i →ₗ[R] FB i where
  __ := f.1.piece_wise_hom i
  map_smul' r x := SetCoe.ext (f.toAlgHom.map_smul_of_tower r x)

/-- `LinearMap` version of `FilteredAddGroupHom.piece_wise_hom`. -/
abbrev GradedPieceHom (i : ι) : GradedPiece FA FA_lt i →ₗ[R] GradedPiece FB FB_lt i :=
  Submodule.mapQ ((FA_lt i).comap (FA i).subtype) ((FB_lt i).comap (FB i).subtype)
    (f.piece_wise_hom i) (fun x hx ↦ by simpa using f.pieces_wise_lt hx)

@[inherit_doc]
scoped[FilteredAlgHom] notation:9000 "Grₐ(" i ")[" f "]" => GradedPieceHom f i

lemma GradedPieceHom_comp_apply (i : ι) (x : GradedPiece FA FA_lt i):
    Grₐ(i)[g] (Grₐ(i)[f] x) = Grₐ(i)[g.comp f] x :=
  FilteredRingHom.GradedPieceHom_comp_apply g.1 f.1 i x

lemma GradedPieceHom_comp (i : ι) : Grₐ(i)[g].comp Grₐ(i)[f] = Grₐ(i)[g.comp f] := by
  ext x
  exact GradedPieceHom_comp_apply g f i x

variable [AddMonoid ι] [PartialOrder ι] [hasGMul FA FA_lt] [hasGMul FB FB_lt] [hasGMul FC FC_lt]

open FilteredAddGroupHom in
/-- The induced graded algebra morphism between associated graded algebras,
obtained from the `AssociatedGradedRingHom` of a filtered algebra morphism. -/
noncomputable def AssociatedGradedAlgHom [DecidableEq ι] :
    (AssociatedGraded FA FA_lt) →ₐ[R] (AssociatedGraded FB FB_lt) where
  __ := f.1.AssociatedGradedRingHom
  commutes' r := by
    simp only [FilteredRingHom.AssociatedGradedRingHom, ZeroHom.toFun_eq_coe, AddMonoidHom.coe_mk,
      AddMonoidHom.toZeroHom_coe, RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk,
      DirectSum.algebraMap_apply, DirectSum.GAlgebra.toFun, GradedPiece.algebraMap, ZeroHom.coe_mk,
      AssociatedGradedAddMonoidHom_apply_of, GradedPieceHom_apply_mk_eq_mk_piece_wise_hom]
    congr
    convert (f.piece_wise_hom 0).map_smul r 1
    exact SetCoe.ext f.map_one.symm

@[inherit_doc]
scoped[FilteredAlgHom] notation:9000 "Grₐ[" f "]" => AssociatedGradedAlgHom f

variable [DecidableEq ι]

@[simp]
theorem AssociatedGradedRingHom_apply (x : AssociatedGraded FA FA_lt) (i : ι) :
    (Grₐ[f] x) i = Grₐ(i)[f] (x i) := rfl

theorem AssociatedGradedRingHom_comp: Grₐ[g].comp Grₐ[f] = Grₐ[g.comp f] :=
  AlgHom.ext <| fun x ↦ congrFun
    (congrArg DFunLike.coe (FilteredRingHom.AssociatedGradedRingHom_comp_eq_comp g.1 f.1)) x

end FilteredAlgHom

end
