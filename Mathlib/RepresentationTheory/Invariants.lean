/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.FDRep

/-!
# Subspace of invariants a group representation

This file introduces the subspace of invariants of a group representation
and proves basic results about it.
The main tool used is the average of all elements of the group, seen as an element of
`MonoidAlgebra k G`. The action of this special element gives a projection onto the
subspace of invariants.
In order for the definition of the average element to make sense, we need to assume for most of the
results that the order of `G` is invertible in `k` (e. g. `k` has characteristic `0`).
-/

suppress_compilation

universe u

open Representation

namespace GroupAlgebra

open MonoidAlgebra

variable (k G : Type*) [CommSemiring k] [Group G]
variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The average of all elements of the group `G`, considered as an element of `MonoidAlgebra k G`.
-/
noncomputable def average : MonoidAlgebra k G :=
  ⅟ (Fintype.card G : k) • ∑ g : G, of k G g

/-- `average k G` is invariant under left multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_left (g : G) : ↑(Finsupp.single g 1) * average k G = average k G := by
  simp only [mul_one, Finset.mul_sum, Algebra.mul_smul_comm, average, MonoidAlgebra.of_apply,
    Finset.sum_congr, MonoidAlgebra.single_mul_single]
  set f : G → MonoidAlgebra k G := fun x => Finsupp.single x 1
  show ⅟ (Fintype.card G : k) • ∑ x : G, f (g * x) = ⅟ (Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) _]

/-- `average k G` is invariant under right multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_right (g : G) : average k G * ↑(Finsupp.single g 1) = average k G := by
  simp only [mul_one, Finset.sum_mul, Algebra.smul_mul_assoc, average, MonoidAlgebra.of_apply,
    Finset.sum_congr, MonoidAlgebra.single_mul_single]
  set f : G → MonoidAlgebra k G := fun x => Finsupp.single x 1
  show ⅟ (Fintype.card G : k) • ∑ x : G, f (x * g) = ⅟ (Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) _]

end GroupAlgebra

namespace Representation

section Invariants

open GroupAlgebra

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

/-- The subspace of invariants, consisting of the vectors fixed by all elements of `G`.
-/
def invariants : Submodule k V where
  carrier := setOf fun v => ∀ g : G, ρ g v = v
  zero_mem' g := by simp only [map_zero]
  add_mem' hv hw g := by simp only [hv g, hw g, map_add]
  smul_mem' r v hv g := by simp only [hv g, LinearMap.map_smulₛₗ, RingHom.id_apply]

@[simp]
theorem mem_invariants (v : V) : v ∈ invariants ρ ↔ ∀ g : G, ρ g v = v := by rfl

theorem invariants_eq_inter : (invariants ρ).carrier = ⋂ g : G, Function.fixedPoints (ρ g) := by
  ext; simp [Function.IsFixedPt]

theorem invariants_eq_top [ρ.IsTrivial] :
    invariants ρ = ⊤ :=
eq_top_iff.2 (fun x _ g => ρ.isTrivial_apply g x)

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The action of `average k G` gives a projection map onto the subspace of invariants.
-/
@[simp]
noncomputable def averageMap : V →ₗ[k] V :=
  asAlgebraHom ρ (average k G)

/-- The `averageMap` sends elements of `V` to the subspace of invariants.
-/
theorem averageMap_invariant (v : V) : averageMap ρ v ∈ invariants ρ := fun g => by
  rw [averageMap, ← asAlgebraHom_single_one, ← LinearMap.mul_apply, ← map_mul (asAlgebraHom ρ),
    mul_average_left]

/-- The `averageMap` acts as the identity on the subspace of invariants.
-/
theorem averageMap_id (v : V) (hv : v ∈ invariants ρ) : averageMap ρ v = v := by
  rw [mem_invariants] at hv
  simp [average, map_sum, hv, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k _ v, smul_smul]

theorem isProj_averageMap : LinearMap.IsProj ρ.invariants ρ.averageMap :=
  ⟨ρ.averageMap_invariant, ρ.averageMap_id⟩

end Invariants

namespace linHom

open CategoryTheory Action

section Rep

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

theorem mem_invariants_iff_comm {X Y : Rep k G} (f : X.V →ₗ[k] Y.V) (g : G) :
    (linHom X.ρ Y.ρ) g f = f ↔ f.comp (X.ρ g) = (Y.ρ g).comp f := by
  dsimp
  rw [← LinearMap.comp_assoc, ← ModuleCat.hom_ofHom (Y.ρ g), ← ModuleCat.hom_ofHom f,
      ← ModuleCat.hom_comp, ← ModuleCat.hom_ofHom (X.ρ g⁻¹), ← ModuleCat.hom_comp,
      Rep.ofHom_ρ, ← ρAut_apply_inv X g, Rep.ofHom_ρ, ← ρAut_apply_hom Y g, ← ModuleCat.hom_ext_iff,
      Iso.inv_comp_eq, ρAut_apply_hom, ← ModuleCat.hom_ofHom (X.ρ g),
      ← ModuleCat.hom_comp, ← ModuleCat.hom_ext_iff]
  exact comm

/-- The invariants of the representation `linHom X.ρ Y.ρ` correspond to the representation
homomorphisms from `X` to `Y`. -/
@[simps]
def invariantsEquivRepHom (X Y : Rep k G) : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y where
  toFun f := ⟨ModuleCat.ofHom f.val, fun g =>
    ModuleCat.hom_ext ((mem_invariants_iff_comm _ g).1 (f.property g))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f.hom.hom, fun g =>
    (mem_invariants_iff_comm _ g).2 (ModuleCat.hom_ext_iff.mp (f.comm g))⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

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

section Coinvariants

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (S : Subgroup G)

/-- The submodule generated by elements of the form `ρ g x - x`. -/
abbrev augmentationSubmodule : Submodule k V :=
  Submodule.span k (Set.range <| fun (x : G × V) => ρ x.1 x.2 - x.2)

variable {ρ}

lemma mem_augmentationSubmodule_of_eq (g : G) (x : V) (a : V) (h : ρ g x - x = a) :
    a ∈ augmentationSubmodule ρ :=
  Submodule.subset_span ⟨(g, x), h⟩

variable (ρ)

/-- The coinvariants of a representation, `V ⧸ ⟨{ρ g x - x | g ∈ G, x ∈ V}⟩`. -/
abbrev coinvariants := V ⧸ augmentationSubmodule ρ

/-- The quotient map from a representation to its coinvariants as a linear map. -/
abbrev coinvariantsMkQ := Submodule.mkQ (augmentationSubmodule ρ)

/-- A `G`-invariant linear map induces a linear map out of the coinvariants of a
`G`-representation. -/
def coinvariantsLift (f : V →ₗ[k] W) (h : ∀ (x : G), f ∘ₗ ρ x = f) :
    ρ.coinvariants →ₗ[k] W :=
  Submodule.liftQ _ f <| Submodule.span_le.2 fun x ⟨⟨g, y⟩, hy⟩ => by
    simpa only [← hy, SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, LinearMap.coe_comp,
      Function.comp_apply] using LinearMap.ext_iff.1 (h g) y

@[simp]
theorem coinvariantsLift_comp_mkQ (f : V →ₗ[k] W) (h : ∀ (x : G), f ∘ₗ ρ x = f) :
  coinvariantsLift ρ f h ∘ₗ (augmentationSubmodule ρ).mkQ = f := rfl

@[simp]
theorem coinvariantsLift_mk (f : V →ₗ[k] W) (h : ∀ (x : G), f ∘ₗ ρ x = f) (x : V) :
  coinvariantsLift ρ f h (Submodule.Quotient.mk x) = f x := rfl

end Coinvariants
end Representation

namespace Rep

open CategoryTheory

variable (k G : Type u) [CommRing k] [Group G] (A : Rep k G)

section Invariants

/-- The functor sending a representation to its submodule of invariants. -/
@[simps]
noncomputable def invariantsFunctor : Rep k G ⥤ ModuleCat k where
  obj A := ModuleCat.of k A.ρ.invariants
  map {A B} f := ModuleCat.ofHom <| (f.hom.hom ∘ₗ A.ρ.invariants.subtype).codRestrict
    B.ρ.invariants fun ⟨c, hc⟩ g => by
      have := (hom_comm_apply f g c).symm
      simp_all [hc g]

instance : (invariantsFunctor k G).PreservesZeroMorphisms where

instance : (invariantsFunctor k G).Additive where

/-- The adjunction between the functor equipping a module with the trivial representation, and
the functor sending a representation to its submodule of invariants. -/
noncomputable abbrev invariantsAdjunction : trivialFunctor ⊣ invariantsFunctor k G :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun _ _ => {
      toFun := fun f => ModuleCat.ofHom <|
        LinearMap.codRestrict _ f.hom.hom fun x g => (hom_comm_apply f _ _).symm
      invFun := fun f => {
        hom := ModuleCat.ofHom (Submodule.subtype _ ∘ₗ f.hom)
        comm := fun g => by ext x; exact ((f x).2 g).symm }
      left_inv := by intro; rfl
      right_inv := by intro; rfl }
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; rfl }

noncomputable instance : Limits.PreservesLimits (invariantsFunctor k G) :=
  (invariantsAdjunction k G).rightAdjoint_preservesLimits

end Invariants
section Coinvariants

variable {k G A} {B C : Rep k G} {n : ℕ} {V : Type u} [AddCommGroup V] [Module k V]

open Representation

/-- The linear map underlying a `G`-representation morphism `A ⟶ V`, where `V` has the trivial
representation, factors through `A_G`. -/
abbrev coinvariantsLift (f : A ⟶ Rep.trivial k G V) :
    coinvariants A.ρ →ₗ[k] V :=
  Representation.coinvariantsLift _ f.hom.hom fun _ => congr(ModuleCat.Hom.hom $(f.comm _))

/-- A `G`-representation morphism `A ⟶ B` induces a linear map `A_G →ₗ[k] B_G`. -/
abbrev coinvariantsMap (f : A ⟶ B) :
    coinvariants A.ρ →ₗ[k] coinvariants B.ρ :=
  Representation.coinvariantsLift _ (Submodule.mkQ _ ∘ₗ f.hom.hom) fun g => LinearMap.ext fun x =>
    (Submodule.Quotient.eq _).2 <| mem_augmentationSubmodule_of_eq g (f.hom x) _ <| by
      simpa using (hom_comm_apply f g x).symm

@[simp]
theorem coinvariantsMap_comp_mkQ (f : A ⟶ B) :
    coinvariantsMap f ∘ₗ coinvariantsMkQ A.ρ = coinvariantsMkQ B.ρ ∘ₗ f.hom.hom := rfl

@[simp]
theorem coinvariantsMap_mk (f : A ⟶ B) (x : A) :
    coinvariantsMap f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f.hom x) := rfl

@[simp]
theorem coinvariantsMap_id (A : Rep k G) :
    coinvariantsMap (𝟙 A) = LinearMap.id := by
  ext; rfl

@[simp]
theorem coinvariantsMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    coinvariantsMap (f ≫ g) = coinvariantsMap g ∘ₗ coinvariantsMap f := by
  ext; rfl

variable (k G)

/-- The functor sending a representation to its coinvariants. -/
@[simps]
def coinvariantsFunctor : Rep k G ⥤ ModuleCat k where
  obj A := ModuleCat.of k (A.ρ.coinvariants)
  map f := ModuleCat.ofHom (coinvariantsMap f)

instance : (coinvariantsFunctor k G).Additive where
  map_add := ModuleCat.hom_ext <| LinearMap.ext fun x => Quotient.inductionOn' x (fun _ => rfl)

/-- The adjunction between the functor sending a representation to its coinvariants and the functor
equipping a module with the trivial representation. -/
noncomputable def coinvariantsAdjunction : coinvariantsFunctor k G ⊣ trivialFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => {
        hom := ModuleCat.ofHom (f.hom ∘ₗ X.ρ.augmentationSubmodule.mkQ)
        comm := fun g => by
          ext x
          exact congr(f.hom $((Submodule.Quotient.eq <| X.ρ.augmentationSubmodule).2
            (X.ρ.mem_augmentationSubmodule_of_eq g x _ rfl))) }
      invFun := fun f => ModuleCat.ofHom (coinvariantsLift f)
      left_inv := fun _ => ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl
      right_inv := fun _ => Action.Hom.ext <| rfl }
    homEquiv_naturality_left_symm := fun _ _ => ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl
    homEquiv_naturality_right := by intros; rfl }

instance : (coinvariantsFunctor k G).PreservesZeroMorphisms where
  map_zero _ _ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl

instance : Limits.PreservesColimits (coinvariantsFunctor k G) :=
  (coinvariantsAdjunction k G).leftAdjoint_preservesColimits

end Coinvariants
end Rep
