/-
Copyright (c) 2025 HuanYu Zheng, Yi Yuan, Weichen Jiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HuanYu Zheng, Yi Yuan, Weichen Jiao
-/
import Mathlib.RingTheory.FilteredAlgebra.AssociatedGraded
import Mathlib.Algebra.Ring.Hom.Defs
/-!
# The filtered ring morphsims on ring

In this file, we defined the filtered ring morphsim on ring, and proof some basic property of it.

# Main definitions

* `FilteredHom` : defines a morphism between general filtration (filtration of set) that preserves
both the main and auxiliary filtered structures.

* `FilteredRingHom` : `FilteredRingHom` defines a morphism between filtered rings that preserves
both the ring and filtration structures.

* `FilteredRingHom.IsStrict` :

* `FilteredRingHom.comp` :

* `Gf` :

* `Gf_comp` :

* `G` :

-/
section FilteredHom

variable {ι A B C α β σ: Type*} [Preorder ι] [SetLike α A] [SetLike β B] [SetLike σ C]

variable (FA : ι → α) (FA_lt : outParam <| ι → α) [IsFiltration FA FA_lt]
variable (FB : ι → β) (FB_lt : outParam <| ι → β) [IsFiltration FB FB_lt]
variable (FC : ι → σ) (FC_lt : outParam <| ι → σ) [IsFiltration FC FC_lt]

/-- This class describes a structure-preserving map between two filtered rings
`IsFiltration FA FA_lt` and `IsFiltration FB FB_lt` (types `A` and `B`). -/
class FilteredHom where
  toFun : A → B
  pieces_wise : ∀ i : ι, ∀ a ∈ FA i, toFun a ∈ FB i
  pieces_wise_lt : ∀ i : ι, ∀ a ∈ FA_lt i, toFun a ∈ FB_lt i

variable (f : FilteredHom FA FA_lt FB FB_lt) (g : FilteredHom FB FB_lt FC FC_lt)

variable {FA FB FC FA_lt FB_lt FC_lt} in
/-- This function composes two filtered morphisms `f : FilteredHom FA FA_lt FB FB_lt` and
`g : FilteredHom FB FB_lt FC FC_lt`, resulting in a new morphism
`f ∘ g : FilteredHom FA FA_lt FC FC_lt`. -/
def FilteredHom.comp : FilteredHom FA FA_lt FC FC_lt := {
  toFun := g.1.comp f.1
  pieces_wise := fun i a ha ↦ g.pieces_wise i (f.1 a) (f.pieces_wise i a ha)
  pieces_wise_lt := fun i a ha ↦ g.pieces_wise_lt i (f.1 a) (f.pieces_wise_lt i a ha)
}

infixl:100 " ∘ " => FilteredHom.comp

end FilteredHom



section FilteredRingHom

variable {ι R S T γ σ τ : Type*} [OrderedAddCommMonoid ι]

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R] [IsRingFiltration FR FR_lt]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S] [IsRingFiltration FS FS_lt]
variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T] [IsRingFiltration FT FT_lt]

/-- This class combines the properties of a ring homomorphism and a filtered homomorphism, ensuring
that the structure of both the ring and its filtration are maintained under the morphism.-/
class FilteredRingHom extends FilteredHom FR FR_lt FS FS_lt, R →+* S

variable {FR FS FR_lt FS_lt} in
class FilteredRingHom.IsStrict (f : outParam <| FilteredRingHom FR FR_lt FS FS_lt) : Prop where
  strict : ∀ p : ι, ∀ y : S, y ∈ f.toRingHom '' (FR p) ↔ (y ∈ (FS p) ∧ y ∈ f.range)
  strict_lt : ∀ p : ι, ∀ y : S, y ∈ f.toRingHom '' (FR_lt p) ↔ (y ∈ (FS_lt p) ∧ y ∈ f.range)

variable (g : FilteredRingHom FS FS_lt FT FT_lt) (f : FilteredRingHom FR FR_lt FS FS_lt)

variable {FR FS FT FR_lt FS_lt FT_lt} in
def FilteredRingHom.comp : FilteredRingHom FR FR_lt FT FT_lt := {
    g.toRingHom.comp f.toRingHom with
  pieces_wise := fun i a ha ↦ g.pieces_wise i (f.toFun a) (f.pieces_wise i a ha)
  pieces_wise_lt := fun i a ha ↦ g.pieces_wise_lt i (f.toFun a) (f.pieces_wise_lt i a ha)
}

infixl:100 " ∘ " => FilteredRingHom.comp

end FilteredRingHom





section DirectSum

open DirectSum

variable {ι R S T σR σS σT : Type*} [DecidableEq ι]

variable [Ring R] {FR : ι → σR} {FR_lt : outParam <| ι → σR} [SetLike σR R] [AddSubgroupClass σR R]
variable [Ring S] {FS : ι → σS} {FS_lt : outParam <| ι → σS} [SetLike σS S] [AddSubgroupClass σS S]
variable [Ring T] (FT : ι → σT) (FT_lt : outParam <| ι → σT) [SetLike σT T] [AddSubgroupClass σT T]

variable (f : FilteredRingHom FR FR_lt FS FS_lt)

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
    exact RingHom.map_add f.toRingHom ↑a ↑b

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
/- The `docBlame` linter reports:
DEFINITIONS ARE MISSING DOCUMENTATION STRINGS: -/
#check @FilteredHom.toFun /- definition missing documentation string -/
#check «term_∘__1» /- definition missing documentation string -/
#check @FilteredRingHom /- inductive missing documentation string -/
#check @FilteredRingHom.toRingHom /- definition missing documentation string -/
#check @FilteredRingHom.IsStrict /- inductive missing documentation string -/
#check @FilteredRingHom.comp /- definition missing documentation string -/
#check «term_∘__2» /- definition missing documentation string -/
#check @Gf /- definition missing documentation string -/
#check @G /- definition missing documentation string -/
