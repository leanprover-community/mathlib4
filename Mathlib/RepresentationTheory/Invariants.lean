/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.SuppressCompilation

/-!
# Subspace of invariants a group representation

This file introduces the subspace of invariants of a group representation
and proves basic results about it.
The main tool used is the average of all elements of the group, seen as an element of `k[G]`.
The action of this special element gives a projection onto the subspace of invariants.
In order for the definition of the average element to make sense, we need to assume for most of the
results that the order of `G` is invertible in `k` (e. g. `k` has characteristic `0`).
-/

@[expose] public section

suppress_compilation

universe w u v

open MonoidAlgebra

open Representation

namespace GroupAlgebra

variable (k G : Type*) [CommSemiring k] [Group G]
variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The average of all elements of the group `G`, considered as an element of `k[G]`. -/
noncomputable def average : k[G] := ⅟(Fintype.card G : k) • ∑ g : G, of k G g

/-- `average k G` is invariant under left multiplication by elements of `G`. -/
@[simp]
theorem mul_average_left (g : G) : ↑(Finsupp.single g 1) * average k G = average k G := by
  simp only [mul_one, Finset.mul_sum, Algebra.mul_smul_comm, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G → k[G] := fun x => Finsupp.single x 1
  change ⅟(Fintype.card G : k) • ∑ x : G, f (g * x) = ⅟(Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) _]

/-- `average k G` is invariant under right multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_right (g : G) : average k G * ↑(Finsupp.single g 1) = average k G := by
  simp only [mul_one, Finset.sum_mul, Algebra.smul_mul_assoc, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G → k[G] := fun x => Finsupp.single x 1
  change ⅟(Fintype.card G : k) • ∑ x : G, f (x * g) = ⅟(Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) _]

end GroupAlgebra

namespace Representation

section Invariants

open GroupAlgebra

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]
variable (ρ : Representation k G V) (σ : Representation k G W)

/-- The subspace of invariants, consisting of the vectors fixed by all elements of `G`.
-/
def invariants : Submodule k V where
  carrier := setOf fun v => ∀ g : G, ρ g v = v
  zero_mem' g := by simp only [map_zero]
  add_mem' hv hw g := by simp only [hv g, hw g, map_add]
  smul_mem' r v hv g := by simp only [hv g, map_smulₛₗ, RingHom.id_apply]

@[simp]
theorem mem_invariants (v : V) : v ∈ invariants ρ ↔ ∀ g : G, ρ g v = v := by rfl

theorem invariants_eq_inter : (invariants ρ).carrier = ⋂ g : G, Function.fixedPoints (ρ g) := by
  ext; simp [Function.IsFixedPt]

theorem invariants_eq_top [ρ.IsTrivial] :
    invariants ρ = ⊤ :=
eq_top_iff.2 (fun x _ g => ρ.isTrivial_apply g x)

lemma mem_invariants_iff_of_forall_mem_zpowers
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (x : V) :
    x ∈ ρ.invariants ↔ ρ g x = x :=
  ⟨fun h => h g, fun hx γ => by
    rcases hg γ with ⟨i, rfl⟩
    induction i with | zero => simp | succ i _ => simp_all [zpow_add_one] | pred i h => _
    simpa [neg_sub_comm _ (1 : ℤ), zpow_sub] using congr(ρ g⁻¹ $(h.trans hx.symm))⟩

variable {ρ σ} in
@[simp] lemma mem_linHom_invariants_iff_isIntertwining (f : V →ₗ[k] W) :
    (∀ (g : G), σ g ∘ₗ f ∘ₗ ρ g⁻¹ = f) ↔ ρ.IsIntertwiningMap σ f := by
  refine ⟨fun hf ↦ ⟨fun γ v ↦ ?_⟩, fun hf γ ↦ ?_⟩
  · specialize hf γ
    nth_rewrite 1 [← hf]
    simp
  · ext v
    simp [hf.isIntertwining]

/-- The invariants of the representation `linHom ρ σ` correspond to intertwining maps
 from `ρ` to `σ`. -/
def invariantsEquivIntertwiningMap : (linHom ρ σ).invariants ≃ₗ[k] IntertwiningMap ρ σ where
  toFun f := f.val.intertwiningMap_of_isIntertwiningMap ρ σ
    ((mem_linHom_invariants_iff_isIntertwining f.val).mp f.property).isIntertwining
  map_add' _ _ := IntertwiningMap.ext_iff.mpr rfl
  map_smul' _ _ := IntertwiningMap.ext_iff.mpr rfl
  invFun g :=
    { val := g.toLinearMap
      property := (mem_linHom_invariants_iff_isIntertwining g.toLinearMap).mpr
        { isIntertwining := g.isIntertwining } }

section

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The action of `average k G` gives a projection map onto the subspace of invariants.
-/
@[simp]
noncomputable def averageMap : V →ₗ[k] V :=
  asAlgebraHom ρ (average k G)

/-- The `averageMap` sends elements of `V` to the subspace of invariants.
-/
theorem averageMap_invariant (v : V) : averageMap ρ v ∈ invariants ρ := fun g => by
  rw [averageMap, ← asAlgebraHom_single_one, ← Module.End.mul_apply, ← map_mul (asAlgebraHom ρ),
    mul_average_left]

/-- The `averageMap` acts as the identity on the subspace of invariants.
-/
theorem averageMap_id (v : V) (hv : v ∈ invariants ρ) : averageMap ρ v = v := by
  rw [mem_invariants] at hv
  simp [average, map_sum, hv, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k _ v, smul_smul]

theorem isProj_averageMap : LinearMap.IsProj ρ.invariants ρ.averageMap :=
  ⟨ρ.averageMap_invariant, ρ.averageMap_id⟩

end
section Subgroup

variable {V : Type*} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (S : Subgroup G) [S.Normal]

lemma le_comap_invariants (g : G) :
    (invariants <| ρ.comp S.subtype) ≤
      (invariants <| ρ.comp S.subtype).comap (ρ g) :=
  fun x hx ⟨s, hs⟩ => by
    simpa using congr(ρ g $(hx ⟨(g⁻¹ * s * g), Subgroup.Normal.conj_mem' ‹_› s hs g⟩))

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the invariants of `ρ|_S`. -/
abbrev toInvariants :
    Representation k G (invariants (ρ.comp S.subtype)) :=
  subrepresentation ρ _ <| le_comap_invariants ρ S

instance : IsTrivial ((toInvariants ρ S).comp S.subtype) where
  out g := LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext <| by simpa using (hx g)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
abbrev quotientToInvariants :
    Representation k (G ⧸ S) (invariants (ρ.comp S.subtype)) :=
  ofQuotient (toInvariants ρ S) S

/-- The intertwining map between the `G ⧸ S`-representation on the invariants of `ρ|_S` and `ρ`. -/
abbrev quotientToInvariants_lift :
    Representation.IntertwiningMap (MonoidHom.comp (quotientToInvariants ρ S)
      (QuotientGroup.mk' _)) ρ := ⟨Submodule.subtype _, fun _ ↦ rfl⟩

end Subgroup
end Invariants

namespace linHom

open CategoryTheory Action

section Rep

variable {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep.{w} k G}

theorem mem_invariants_iff_comm (f : X.V →ₗ[k] Y.V) (g : G) :
    (linHom X.ρ Y.ρ) g f = f ↔ f.comp (X.ρ g) = (Y.ρ g).comp f := by
  dsimp
  constructor
  · intro h
    nth_rw 1 [← h]
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← Rep.ρ_mul, inv_mul_cancel, map_one,
      Module.End.one_eq_id, LinearMap.comp_id]
  · intro h
    rw [← LinearMap.comp_assoc, ← h, LinearMap.comp_assoc, ← Rep.ρ_mul, mul_inv_cancel, map_one,
      Module.End.one_eq_id, LinearMap.comp_id]

variable (X Y) in
/-- The invariants of the representation `linHom X.ρ Y.ρ` correspond to the representation
homomorphisms from `X` to `Y`. -/
@[simps]
def invariantsEquivRepHom : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y where
  toFun f := Rep.ofHom ⟨f.val, fun g ↦ (mem_invariants_iff_comm _ g).1 <| f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f.hom, fun g => (mem_invariants_iff_comm _ g).2 <| f.hom.2 g⟩

end Rep

section FDRep

variable {k : Type u} [Field k] {G : Type u} [Group G]

/-- The invariants of the representation `linHom X.ρ Y.ρ` correspond to the representation
homomorphisms from `X` to `Y`. -/
def invariantsEquivFDRepHom (X Y : FDRep k G) : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y := by
  rw [← FDRep.forget₂_ρ, ← FDRep.forget₂_ρ]
  -- Porting note: The original version used `linHom.invariantsEquivRepHom _ _ ≪≫ₗ`
  exact linHom.invariantsEquivRepHom
    ((forget₂ (FDRep k G) (Rep k G)).obj X) ((forget₂ (FDRep k G) (Rep k G)).obj Y) ≪≫ₗ
    FDRep.forget₂HomLinearEquiv X Y

end FDRep

end linHom

end Representation

namespace Rep

open CategoryTheory

variable {k : Type u} {G : Type v} [CommRing k] [Group G] (A : Rep.{w} k G)
  (S : Subgroup G) [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the invariants of `ρ|_S`. -/
abbrev toInvariants : Rep k G := Rep.of <| A.ρ.toInvariants S

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
abbrev quotientToInvariants : Rep k (G ⧸ S) := Rep.of (A.ρ.quotientToInvariants S)

variable (k G)

/-- The functor sending a representation to its submodule of invariants. -/
@[simps! obj_carrier map_hom]
noncomputable def invariantsFunctor : Rep.{w} k G ⥤ ModuleCat k where
  obj A := ModuleCat.of k A.ρ.invariants
  map {A B} f := ModuleCat.ofHom <| (f.hom ∘ₗ A.ρ.invariants.subtype).codRestrict
    B.ρ.invariants fun ⟨c, hc⟩ g => by
      have := (hom_comm_apply f g c).symm
      simp_all [hc g]

instance : (invariantsFunctor k G).PreservesZeroMorphisms where
instance : (invariantsFunctor k G).Additive where
instance : (invariantsFunctor k G).Linear k where

set_option backward.isDefEq.respectTransparency false in
variable {G} in
/-- Given a normal subgroup S ≤ G, this is the functor sending a `G`-representation `A` to the
`G ⧸ S`-representation it induces on `A^S`. -/
noncomputable def quotientToInvariantsFunctor (S : Subgroup G) [S.Normal] :
    Rep.{w} k G ⥤ Rep k (G ⧸ S) where
  obj X := X.quotientToInvariants S
  map {X Y} f := Rep.ofHom ⟨((invariantsFunctor k S).map ((Rep.resFunctor S.subtype).map f)).hom,
    fun g ↦ QuotientGroup.induction_on g fun g ↦ by ext x; simp [hom_comm_apply]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction between the functor equipping a module with the trivial representation, and
the functor sending a representation to its submodule of invariants. -/
@[simps]
noncomputable def invariantsAdjunction : trivialFunctor k G ⊣ invariantsFunctor k G where
  unit := { app _ := ModuleCat.ofHom <| LinearMap.id.codRestrict _ <| by simp [trivialFunctor] }
  counit := { app X := Rep.ofHom ⟨Submodule.subtype _, fun g ↦ by ext x; exact (x.2 g).symm⟩ }

@[simp]
lemma invariantsAdjunction_homEquiv_apply_hom
    {X : ModuleCat k} {Y : Rep k G} (f : (trivialFunctor k G).obj X ⟶ Y) :
    ((invariantsAdjunction k G).homEquiv _ _ f).hom =
      f.hom.codRestrict _ (by intro _ _; exact (hom_comm_apply f _ _).symm) := rfl

@[simp]
lemma invariantsAdjunction_homEquiv_symm_apply_hom
    {X : ModuleCat k} {Y : Rep k G} (f : X ⟶ (invariantsFunctor k G).obj Y) :
    (((invariantsAdjunction k G).homEquiv _ _).symm f).hom.toLinearMap =
      Submodule.subtype _ ∘ₗ f.hom := rfl

noncomputable instance : (invariantsFunctor k G).IsRightAdjoint :=
  (invariantsAdjunction k G).isRightAdjoint

end Rep
