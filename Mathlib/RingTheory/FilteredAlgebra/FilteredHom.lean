/-
Copyright (c) 2025 HuanYu Zheng, Yi Yuan, Weichen Jiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HuanYu Zheng, Yi Yuan, Weichen Jiao, Nailin Guan
-/
import Mathlib.RingTheory.FilteredAlgebra.AssociatedGraded
import Mathlib.Algebra.Ring.Hom.Defs
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

section

variable (σ₁₂ : FilteredRingHom FR FR_lt FS FS_lt)
variable (σ₂₃ : FilteredRingHom FS FS_lt FT FT_lt)
variable (σ₁₃ : FilteredRingHom FR FR_lt FT FT_lt)

lemma AssociatedGradedRingHom_comp_eq_comp'
    [RingHomCompTriple σ₁₂.toRingHom σ₂₃.toRingHom σ₁₃.toRingHom] :
    RingHomCompTriple Gr+*[σ₁₂] Gr+*[σ₂₃] Gr+*[σ₁₃] where
  comp_eq := by
    rw [AssociatedGradedRingHom_comp_eq_comp]
    congr
    ext x
    exact RingHomCompTriple.comp_apply (σ₁₂ := σ₁₂.toRingHom) (σ₂₃ := σ₂₃.toRingHom)

end

end FilteredRingHom

end

section

variable {ι ιM R S T M N L σR σS σT σM σN σL : Type*}
--[AddAction ι ιM]
variable [Ring R] [SetLike σR R] (FR : ι → σR) (FR_lt : outParam <| ι → σR)
variable [Ring S] [SetLike σS S] (FS : ι → σS) (FS_lt : outParam <| ι → σS)
variable [Ring T] [SetLike σT T] (FT : ι → σT) (FT_lt : outParam <| ι → σT)
variable [AddCommGroup M] [Module R M] [SetLike σM M] (FM : ιM → σM) (FM_lt : outParam <| ιM → σM)
variable [AddCommGroup N] [Module S N] [SetLike σN N] (FN : ιM → σN) (FN_lt : outParam <| ιM → σN)
variable [AddCommGroup L] [Module T L] [SetLike σL L] (FL : ιM → σL) (FL_lt : outParam <| ιM → σL)

variable (σ₂₃ : outParam <| FilteredRingHom FS FS_lt FT FT_lt)
variable (σ₁₂ : outParam <| FilteredRingHom FR FR_lt FS FS_lt)
variable (σ₁₃ : outParam <| FilteredRingHom FR FR_lt FT FT_lt)


/-- A morphism between filtered modules that preserves both the module and
filtered structures. -/
@[ext]
class FilteredModuleHom extends FilteredAddGroupHom FM FM_lt FN FN_lt, M →ₛₗ[σ₁₂.toRingHom] N

/-- Reinterpret a `FilteredModuleHom` as a `LinearMap`. -/
add_decl_doc FilteredModuleHom.toLinearMap

instance : CoeOut (FilteredModuleHom FR FR_lt FS FS_lt FM FM_lt FN FN_lt σ₁₂)
    (FilteredAddGroupHom FM FM_lt FN FN_lt) :=
  ⟨fun a ↦ a.toFilteredAddGroupHom⟩

instance : FunLike (FilteredModuleHom FR FR_lt FS FS_lt FM FM_lt FN FN_lt σ₁₂) M N where
  coe f := f.toFun
  coe_injective' _ _ h := FilteredModuleHom.ext h

instance : SemilinearMapClass (FilteredModuleHom FR FR_lt FS FS_lt FM FM_lt FN FN_lt σ₁₂)
    σ₁₂.toRingHom M N where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul'

instance : FilteredHomClass (FilteredModuleHom FR FR_lt FS FS_lt FM FM_lt FN FN_lt σ₁₂)
    FM FM_lt FN FN_lt where
  pieces_wise f := f.pieces_wise
  pieces_wise_lt f := f.pieces_wise_lt

namespace FilteredModuleHom

variable (g : FilteredModuleHom FS FS_lt FT FT_lt FN FN_lt FL FL_lt σ₂₃)
  (f : FilteredModuleHom FR FR_lt FS FS_lt FM FM_lt FN FN_lt σ₁₂)

variable {FR FS FT FM FN FL FR_lt FS_lt FT_lt FM_lt FN_lt FL_lt σ₁₂ σ₂₃ σ₁₃}
variable [RingHomCompTriple σ₁₂.toRingHom σ₂₃.toRingHom σ₁₃.toRingHom]

/-- The composition of filtered ring morphisms,
obtained from the composition of the underlying ring homomorphisms. -/
def comp : FilteredModuleHom FR FR_lt FT FT_lt FM FM_lt FL FL_lt σ₁₃  where
  __ := g.toLinearMap.comp f.toLinearMap
  map_zero' := (g.toLinearMap.comp f.toLinearMap).map_zero
  pieces_wise ha := g.pieces_wise (f.pieces_wise ha)
  pieces_wise_lt ha := g.pieces_wise_lt (f.pieces_wise_lt ha)

variable [AddSubgroupClass σM M] [AddSubgroupClass σN N] [AddSubgroupClass σL L]

/-- The `AddMonoidHom` version of `FilteredHom.piece_wise_hom`. -/
abbrev piece_wise_hom (i : ιM) : FM i →+ FN i :=
  FilteredAddGroupHom.piece_wise_hom f.toFilteredAddGroupHom i

/-- The `FilteredModuleHom` version of `FilteredAddGroupHom.GradedPieceHom`. -/
abbrev GradedPieceHom (i : ιM) : GradedPiece FM FM_lt i →+ GradedPiece FN FN_lt i :=
  f.1.GradedPieceHom i

@[inherit_doc]
scoped[FilteredModuleHom] notation:9000 "Grₛₗ(" i ")[" f "]" => GradedPieceHom f i

@[simp]
lemma GradedPieceHom_apply_mk_eq_mk_piece_wise_hom {i : ιM} (x : FM i) :
    Grₛₗ(i)[f] (GradedPiece.mk FM FM_lt x) = (GradedPiece.mk FN FN_lt (f.piece_wise_hom i x)) :=
  rfl

lemma GradedPieceHom_comp_apply (i : ιM) (x : GradedPiece FM FM_lt i):
    Grₛₗ(i)[g] (Grₛₗ(i)[f] x) = Grₛₗ(i)[g.comp f] x :=
  FilteredAddGroupHom.GradedPieceHom_comp_apply g.1 f.1 i x

lemma GradedPieceHom_comp (i : ιM) : Grₛₗ(i)[g].comp Grₛₗ(i)[f] = Grₛₗ(i)[g.comp f] :=
  FilteredAddGroupHom.GradedPieceHom_comp g.1 f.1 i

variable [AddSubgroupClass σR R] [AddSubgroupClass σS S] [AddSubgroupClass σT T]
variable [AddMonoid ι] [PartialOrder ι] [hasGMul FR FR_lt] [hasGMul FS FS_lt] [hasGMul FT FT_lt]
variable [PartialOrder ιM] [AddAction ι ιM]
variable [hasGSMul FR FR_lt FM FM_lt] [hasGSMul FS FS_lt FN FN_lt] [hasGSMul FT FT_lt FL FL_lt]

open DirectSum FilteredRingHom in
/-- The induced graded module morphism between associated graded modules,
obtained from the `AssociatedGradedAddMonoidHom` of a filtered module morphism. -/
noncomputable def AssociatedGradedModuleHom [DecidableEq ι] [DecidableEq ιM] :
    (AssociatedGraded FM FM_lt) →ₛₗ[Gr+*[σ₁₂]] (AssociatedGraded FN FN_lt) where
  __ := f.1.AssociatedGradedAddMonoidHom
  map_smul' r' m' := DirectSum.induction_on r' (by simp)
    (DirectSum.induction_on m' (by simp)
      (fun j m' i r' ↦ by
        induction r' using GradedPiece.induction_on
        induction m' using GradedPiece.induction_on
        rename_i r m
        simp only [Gmodule.smul_def, Gmodule.smulAddMonoidHom_apply_of_of, GradedMonoid.GSMul.smul,
          gradedSMul_def, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
          FilteredAddGroupHom.AssociatedGradedAddMonoidHom_apply_of,
          FilteredAddGroupHom.GradedPieceHom_apply_mk_eq_mk_piece_wise_hom, AddMonoidHom.coe_mk,
          ZeroHom.coe_mk, AssociatedGradedRingHom_apply_of]
        congr
        exact SetCoe.ext (f.toLinearMap.map_smul' r.1 m.1))
      (by intro m1 m2 h1 h2 i x
          simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, smul_add, map_add] at h1 h2 ⊢
          rw [h1 i x, h2 i x]))
    (DirectSum.induction_on m' (by simp)
      (by intro i x m1 m2 h1 h2
          simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, add_smul, map_add] at h1 h2 ⊢
          rw [h1, h2])
      (by intro m1 m2 h1 h2 r1 r2
          simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add]
          intro h3 h4
          rw [add_smul, map_add, h3, h4, add_smul]))

variable [DecidableEq ι] [DecidableEq ιM]

@[inherit_doc]
scoped[FilteredModuleHom] notation:9000 "Grₛₗ[" f "]" => AssociatedGradedModuleHom f


@[simp]
theorem AssociatedGradedRingHom_apply (x : AssociatedGraded FM FM_lt) (i : ιM) :
    (Grₛₗ[f] x) i = Grₛₗ(i)[f] (x i) := rfl

@[simp]
lemma AssociatedGradedRingHom_apply_of {i : ιM} (x : GradedPiece FM FM_lt i) :
    (Grₛₗ[f] (AssociatedGraded.of x)) = AssociatedGraded.of (Grₛₗ(i)[f] x) :=
  f.1.AssociatedGradedAddMonoidHom_apply_of x

theorem AssociatedGradedRingHom_comp_eq_comp :
    letI := FilteredRingHom.AssociatedGradedRingHom_comp_eq_comp' σ₁₂ σ₂₃ σ₁₃
    Grₛₗ[g].comp Grₛₗ[f] = Grₛₗ[g.comp f] :=
  LinearMap.ext <| fun x ↦ congrFun
  (congrArg DFunLike.coe (FilteredAddGroupHom.AssociatedGradedAddMonoidHom_comp_eq_comp g.1 f.1)) x

end FilteredModuleHom

end
