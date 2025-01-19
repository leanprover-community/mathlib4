/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
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

universe v u

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
eq_top_iff.2 (fun x _ g => by simp)

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

variable {k : Type u} [CommRing k] {G : Grp.{u}}

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

variable {k : Type u} [Field k] {G : Grp.{u}}

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

section QuotientGroup

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V) (S : Subgroup G) [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the invariants of `ρ|_S`. -/
@[simps]
noncomputable def toInvariantsOfNormal :
    Representation k G (invariants (ρ.comp S.subtype)) where
  toFun g := ((ρ g).comp (Submodule.subtype _)).codRestrict _ (fun ⟨x, hx⟩ ⟨s, hs⟩ => by
    simpa using congr(ρ g $(hx ⟨(g⁻¹ * s * g), Subgroup.Normal.conj_mem' ‹_› s hs g⟩)))
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

instance : IsTrivial ((toInvariantsOfNormal ρ S).comp S.subtype) where
  out g := LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext <| by
    simpa using (hx g)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
noncomputable abbrev quotientGroupToInvariants :
    Representation k (G ⧸ S) (invariants (ρ.comp S.subtype)) :=
  ofQuotientGroup (toInvariantsOfNormal ρ S) S

end QuotientGroup
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

section Finsupp
open Finsupp

variable (α : Type*)

/-- Given a `G`-representation `(V, ρ)` and a type `α`, this is the map `(α →₀ V)_G →ₗ (α →₀ V_G)`
sending `⟦single a v⟧ ↦ single a ⟦v⟧`. -/
def coinvariantsToFinsupp :
    coinvariants (ρ.finsupp α) →ₗ[k] α →₀ coinvariants ρ :=
  coinvariantsLift _ (mapRange.linearMap (Submodule.mkQ _)) <| fun g => lhom_ext fun _ x => by
    simp [mapRange.linearMap, ← (Submodule.Quotient.eq _).2
      (mem_augmentationSubmodule_of_eq g x _ rfl), finsupp]

@[simp]
lemma coinvariantsToFinsupp_mk_single (x : α) (a : V) :
    coinvariantsToFinsupp ρ α (Submodule.Quotient.mk (single x a)) =
      single x (Submodule.Quotient.mk a) := by simp [coinvariantsToFinsupp]

/-- Given a `G`-representation `(V, ρ)` and a type `α`, this is the map `(α →₀ V_G) →ₗ (α →₀ V)_G`
sending `single a ⟦v⟧ ↦ ⟦single a v⟧`. -/
def finsuppToCoinvariants :
    (α →₀ coinvariants ρ) →ₗ[k] coinvariants (ρ.finsupp α) :=
  lsum (R := k) k fun a => coinvariantsLift _ (Submodule.mkQ _ ∘ₗ lsingle a) fun g =>
    LinearMap.ext fun x => (Submodule.Quotient.eq _).2 <|
    mem_augmentationSubmodule_of_eq g (single a x) _ <| by simp

@[simp]
lemma finsuppToCoinvariants_single_mk (a : α) (x : V) :
    finsuppToCoinvariants ρ α (single a <| Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (single a x) := by simp [finsuppToCoinvariants]

/-- Given a `G`-representation `(V, ρ)` and a type `α`, this is the linear equivalence
`(α →₀ V)_G ≃ₗ (α →₀ V_G)` sending `⟦single a v⟧ ↦ single a ⟦v⟧`. -/
abbrev coinvariantsFinsuppLEquiv :
    coinvariants (ρ.finsupp α) ≃ₗ[k] α →₀ coinvariants ρ :=
  LinearEquiv.ofLinear (coinvariantsToFinsupp ρ α) (finsuppToCoinvariants ρ α)
    (lhom_ext fun _ x => Quotient.inductionOn' x fun _ => by
      simp [coinvariantsToFinsupp, finsuppToCoinvariants, Submodule.Quotient.mk''_eq_mk])
    (Submodule.linearMap_qext _ <| lhom_ext fun _ _ => by
      simp [finsuppToCoinvariants, coinvariantsToFinsupp])

end Finsupp

section TensorProduct
open TensorProduct

@[simp]
lemma coinvariants_mk_ρ_inv_tmul (τ : Representation k G W) (x : V) (y : W) (g : G) :
    Submodule.Quotient.mk (p := (ρ.tprod τ).augmentationSubmodule) (ρ g⁻¹ x ⊗ₜ[k] y) =
      Submodule.Quotient.mk (p := (ρ.tprod τ).augmentationSubmodule) (x ⊗ₜ[k] τ g y) :=
  (Submodule.Quotient.eq _).2 <| mem_augmentationSubmodule_of_eq g⁻¹ (x ⊗ₜ[k] τ g y) _ <| by simp

@[simp]
lemma coinvariants_mk_tmul_ρ_inv (τ : Representation k G W) (x : V) (y : W) (g : G) :
    Submodule.Quotient.mk (p := (ρ.tprod τ).augmentationSubmodule) (x ⊗ₜ[k] τ g⁻¹ y) =
      Submodule.Quotient.mk (p := (ρ.tprod τ).augmentationSubmodule) (ρ g x ⊗ₜ[k] y) :=
  (Submodule.Quotient.eq _).2 <| mem_augmentationSubmodule_of_eq g⁻¹ (ρ g x ⊗ₜ[k] y) _ <| by simp

/-- Given a `k`-linear `G`-representation `V, ρ`, this is the map `(V ⊗ k[G])_G →ₗ[k] V` sending
`⟦v ⊗ single g r⟧ ↦ r • ρ(g⁻¹)(v)`. -/
def ofCoinvariantsTprodLeftRegular :
    coinvariants (V := V ⊗[k] (G →₀ k)) (ρ.tprod (leftRegular k G)) →ₗ[k] V :=
  coinvariantsLift _ (TensorProduct.lift (Finsupp.linearCombination _
    fun g => ρ g⁻¹) ∘ₗ (TensorProduct.comm _ _ _).toLinearMap) fun _ => TensorProduct.ext <|
      LinearMap.ext fun _ => Finsupp.lhom_ext fun _ _ => by simp

@[simp]
lemma ofCoinvariantsTprodLeftRegular_mk_tmul_single (x : V) (g : G) (r : k) :
    ofCoinvariantsTprodLeftRegular ρ (Submodule.Quotient.mk (x ⊗ₜ Finsupp.single g r)) =
      r • ρ g⁻¹ x :=
  congr($(Finsupp.linearCombination_single k (v := fun g => ρ g⁻¹) r g) x)

/-- Given a `k`-linear `G`-representation `V, ρ`, this is the linear equivalence
`(V ⊗ k[G])_G ≃ₗ[k] V` sending `⟦v ⊗ single g r⟧ ↦ r • ρ(g⁻¹)(v)`. -/
abbrev coinvariantsTprodLeftRegularLEquiv :
    coinvariants (V := V ⊗[k] (G →₀ k)) (ρ.tprod (leftRegular k G)) ≃ₗ[k] V :=
  LinearEquiv.ofLinear (ofCoinvariantsTprodLeftRegular ρ)
    (Submodule.mkQ _ ∘ₗ (mk k V (G →₀ k)).flip (Finsupp.single 1 1)) (by ext; simp) <|
    Submodule.linearMap_qext _ <| TensorProduct.ext <| LinearMap.ext fun a =>
      Finsupp.lhom_ext fun g r => (Submodule.Quotient.eq _).2 <| by
        apply mem_augmentationSubmodule_of_eq g⁻¹ (a ⊗ₜ Finsupp.single g r)
        simp_all [TensorProduct.smul_tmul', TensorProduct.smul_tmul]

end TensorProduct
end Coinvariants
section QuotientGroup

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (S : Subgroup G)

lemma augmentationSubmodule_le_comap_ρ_of_normal [S.Normal] (g : G) :
    augmentationSubmodule (ρ.comp S.subtype) ≤
      (augmentationSubmodule <| ρ.comp S.subtype).comap (ρ g) :=
  Submodule.span_le.2 fun y ⟨⟨s, x⟩, hs⟩ => by
    simpa [← hs] using mem_augmentationSubmodule_of_eq
      ⟨g * s * g⁻¹, Subgroup.Normal.conj_mem ‹_› s.1 s.2 g⟩ (ρ g x) _ <| by simp

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the augmentation submodule of `ρ|_S`. -/
@[simps]
noncomputable def toAugmentationSubmoduleOfNormal [S.Normal] :
    Representation k G (augmentationSubmodule <| ρ.comp S.subtype) where
  toFun g := LinearMap.restrict (ρ g) <| augmentationSubmodule_le_comap_ρ_of_normal ρ S g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G`-representation on the
coinvariants of `ρ|_S`. -/
@[simps]
noncomputable def toCoinvariantsOfNormal [S.Normal] :
    Representation k G (coinvariants (ρ.comp S.subtype)) where
  toFun g := coinvariantsLift (ρ.comp S.subtype) ((augmentationSubmodule _).mkQ ∘ₗ ρ g)
    fun ⟨s, hs⟩ => by
      ext x
      simpa [Submodule.Quotient.eq] using mem_augmentationSubmodule_of_eq
        (ρ := ρ.comp S.subtype) ⟨g * s * g⁻¹, Subgroup.Normal.conj_mem ‹_› s hs g⟩ (ρ g x)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

instance [S.Normal] : IsTrivial ((toCoinvariantsOfNormal ρ S).comp S.subtype) where
  out g := Submodule.linearMap_qext _ <| by
    ext x
    simpa [Submodule.Quotient.eq] using mem_augmentationSubmodule_of_eq g x _ rfl

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the coinvariants of `ρ|_S`. -/
noncomputable abbrev quotientGroupToCoinvariants [S.Normal] :
    Representation k (G ⧸ S) (coinvariants (ρ.comp S.subtype)) :=
  ofQuotientGroup (toCoinvariantsOfNormal ρ S) S

end QuotientGroup
end Representation

namespace Rep

open CategoryTheory

variable (k G : Type u) [CommRing k] [Group G] (A : Rep k G)

section Invariants

/-- The functor sending a representation to its submodule of invariants. -/
@[simps]
noncomputable def invariantsFunctor : Rep k G ⥤ ModuleCat.{u} k where
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

variable {k G}

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
abbrev quotientGroupToInvariants (S : Subgroup G) [S.Normal] :=
  Rep.of (A.ρ.quotientGroupToInvariants S)

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

variable (A B)

/-- For a representation `A` of a finite group `G`, the norm map `A ⟶ A` induces a linear map
`A_G →ₗ[k] Aᴳ`. -/
noncomputable def liftRestrictNorm [Fintype G] :
    A.ρ.coinvariants →ₗ[k] A.ρ.invariants :=
  A.ρ.coinvariantsLift ((norm A).hom.hom.codRestrict _ fun a g =>
      congr($(ρ_comp_norm_hom_hom A g) a))
    fun g => LinearMap.ext fun x => Subtype.ext <| congr($(norm_hom_hom_comp_ρ A g) x)

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

variable {k G} (S : Subgroup G) [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the augmentation submodule of `ρ|_S`. -/
abbrev toAugmentationSubmoduleOfNormal :=
  Rep.of (A.ρ.toAugmentationSubmoduleOfNormal S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G`-representation on the
coinvariants of `ρ|_S`. -/
abbrev toCoinvariantsOfNormal :=
  Rep.of (A.ρ.toCoinvariantsOfNormal S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `A` induces a short exact sequence of
`G`-representations `0 ⟶ (I_S)A ⟶ A ⟶ A_S ⟶ 0` where `(I_S)A` is the submodule of `A`
generated by elements of the form `ρ(s)(x) - x` for `s ∈ S, x ∈ A`. -/
@[simps]
def coinvariantsShortComplex : ShortComplex (Rep k G) where
  X₁ := toAugmentationSubmoduleOfNormal A S
  X₂ := A
  X₃ := toCoinvariantsOfNormal A S
  f := ⟨ModuleCat.ofHom (Submodule.subtype _), fun _ => rfl⟩
  g := ⟨ModuleCat.ofHom (Submodule.mkQ _), fun _ => rfl⟩
  zero := by ext x; exact (Submodule.Quotient.mk_eq_zero _).2 x.2

lemma coinvariantsShortComplex_shortExact : (coinvariantsShortComplex A S).ShortExact where
  exact := (forget₂ _ (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2
      fun x hx => ⟨(⟨x, (Submodule.Quotient.mk_eq_zero _).1 hx⟩ :
      augmentationSubmodule <| A.ρ.comp S.subtype), rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
  epi_g := (Rep.epi_iff_surjective _).2 <| Submodule.mkQ_surjective _

instance [S.Normal] : IsTrivial ((A.toCoinvariantsOfNormal S).ρ.comp S.subtype) where
  out g := Submodule.linearMap_qext _ <| by ext; simp

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the coinvariants of `ρ|_S`. -/
abbrev quotientGroupToCoinvariants :=
  Rep.of (A.ρ.quotientGroupToCoinvariants S)

variable (α : Type u) [DecidableEq α]

open MonoidalCategory Finsupp

/-- Given a `k`-linear `G`-representation `(A, ρ)` and a type `α`, this is the map
`(A ⊗ (α →₀ k[G]))_G →ₗ[k] (α →₀ A)` sending
`⟦a ⊗ single x (single g r)⟧ ↦ single x (r • ρ(g⁻¹)(a)).` -/
def coinvariantsTensorFreeToFinsupp :
    (A ⊗ free k G α).ρ.coinvariants →ₗ[k] (α →₀ A) :=
  (coinvariantsFinsuppLEquiv _ α ≪≫ₗ lcongr (Equiv.refl α)
    (coinvariantsTprodLeftRegularLEquiv A.ρ)).toLinearMap ∘ₗ coinvariantsMap (finsuppTensorRight A
      (leftRegular k G) α).hom

variable {A α}

@[simp]
lemma coinvariantsTensorFreeToFinsupp_mk_tmul_single (x : A) (i : α) (g : G) (r : k) :
    coinvariantsTensorFreeToFinsupp A α (Submodule.Quotient.mk (x ⊗ₜ single i (single g r))) =
      single i (r • A.ρ g⁻¹ x) := by
  simp [coinvariantsTensorFreeToFinsupp, coinvariantsMap,
    finsuppTensorRight, TensorProduct.finsuppRight]

variable (A α)

/-- Given a `k`-linear `G`-representation `(A, ρ)` and a type `α`, this is the map
`(α →₀ A) →ₗ[k] (A ⊗ (α →₀ k[G]))_G` sending `single x a ↦ ⟦a ⊗ₜ single x 1⟧.` -/
def finsuppToCoinvariantsTensorFree :
    (α →₀ A) →ₗ[k] coinvariants (A ⊗ (free k G α)).ρ :=
  coinvariantsMap ((finsuppTensorRight A (leftRegular k G) α)).inv ∘ₗ
    (coinvariantsFinsuppLEquiv _ α ≪≫ₗ
    lcongr (Equiv.refl α) (coinvariantsTprodLeftRegularLEquiv A.ρ)).symm.toLinearMap

variable {A α}

lemma finsuppToCoinvariantsTensorFree_single (i : α) (x : A) :
    finsuppToCoinvariantsTensorFree A α (single i x) =
      Submodule.Quotient.mk (x ⊗ₜ single i (single (1 : G) (1 : k))) := by
  have := finsuppTensorRight_inv_hom (A := A) (B := leftRegular k G)
  simp_all [finsuppToCoinvariantsTensorFree, coinvariantsMap,
    ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj]

variable (A α)

/-- Given a `k`-linear `G`-representation `(A, ρ)` and a type `α`, this is the linear equivalence
`(A ⊗ (α →₀ k[G]))_G ≃ₗ[k] (α →₀ A)` sending
`⟦a ⊗ single x (single g r)⟧ ↦ single x (r • ρ(g⁻¹)(a)).` -/
abbrev coinvariantsTensorFreeLEquiv :
    coinvariants (A ⊗ free k G α).ρ ≃ₗ[k] (α →₀ A) :=
  LinearEquiv.ofLinear (coinvariantsTensorFreeToFinsupp A α) (finsuppToCoinvariantsTensorFree A α)
    (lhom_ext fun _ _ => by
      rw [LinearMap.comp_apply, finsuppToCoinvariantsTensorFree_single,
        coinvariantsTensorFreeToFinsupp_mk_tmul_single]
      simp) <|
    Submodule.linearMap_qext _ <| TensorProduct.ext <| LinearMap.ext fun a => lhom_ext' fun i =>
      lhom_ext fun g r => by
        have := coinvariantsTensorFreeToFinsupp_mk_tmul_single a i g r
        have := finsuppToCoinvariantsTensorFree_single (A := A) i
        simp_all [Submodule.Quotient.eq, TensorProduct.smul_tmul]

variable (k G) in
/-- The functor sending `A, B` to `(A ⊗[k] B)_G`. This is naturally isomorphic to the functor
sending `A, B` to `A ⊗[k[G]] B`, where we give `A` the `k[G]ᵐᵒᵖ`-module structure defined by
`g • a := A.ρ g⁻¹ a`. -/
@[simps]
def coinvariantsTensor : Rep k G ⥤ Rep k G ⥤ ModuleCat k where
  obj A := MonoidalCategory.tensorLeft A ⋙ coinvariantsFunctor k G
  map f := {
    app := fun A => ModuleCat.ofHom (coinvariantsMap (f ⊗ 𝟙 A))
    naturality := fun _ _ _ => ModuleCat.hom_ext <| Submodule.linearMap_qext _ <|
      TensorProduct.ext' fun _ _ => by rfl }
  map_id _ := NatTrans.ext <| funext fun _ => by
    simpa only [tensorHom_id, id_whiskerRight] using (coinvariantsFunctor k G).map_id _
  map_comp _ _ := NatTrans.ext <| funext fun _ => by
    simpa only [tensorHom_id, comp_whiskerRight] using (coinvariantsFunctor k G).map_comp _ _

instance (A : Rep k G) : ((coinvariantsTensor k G).obj A).Additive := by
  unfold coinvariantsTensor
  infer_instance

end Coinvariants

/-- Given a finite group `G`, this is the natural transformation sending a `G`-representation `A`
to the map `A_G →ₗ[k] Aᴳ` induced by the norm map on `A`. -/
@[simps]
noncomputable def liftRestrictNormNatTrans [Fintype G] :
    coinvariantsFunctor k G ⟶ invariantsFunctor k G where
  app A := ModuleCat.ofHom <| liftRestrictNorm A
  naturality _ _ f := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <|
    LinearMap.ext fun _ => Subtype.ext <| by
      have := hom_comm_apply f
      simp_all [norm, liftRestrictNorm]

end Rep
