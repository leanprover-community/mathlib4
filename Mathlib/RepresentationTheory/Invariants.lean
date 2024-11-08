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
eq_top_iff.2 (fun x _ g => ρ.apply_eq_self g x)

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
  erw [← ρAut_apply_inv]
  rw [← LinearMap.comp_assoc, ← ModuleCat.comp_def, ← ModuleCat.comp_def, Iso.inv_comp_eq,
    ρAut_apply_hom]
  exact comm

/-- The invariants of the representation `linHom X.ρ Y.ρ` correspond to the representation
homomorphisms from `X` to `Y`. -/
@[simps]
def invariantsEquivRepHom (X Y : Rep k G) : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y where
  toFun f := ⟨f.val, fun g => (mem_invariants_iff_comm _ g).1 (f.property g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f.hom, fun g => (mem_invariants_iff_comm _ g).2 (f.comm g)⟩
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

section Inf

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V) (S : Subgroup G)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the invariants of `ρ|_S`. -/
@[simps]
noncomputable def invariantsOfNormal [S.Normal] :
    Representation k G (invariants (ρ.comp S.subtype)) where
  toFun g := ((ρ g).comp (Submodule.subtype _)).codRestrict _ (fun ⟨x, hx⟩ ⟨s, hs⟩ => by
    simpa using congr(ρ g $(hx ⟨(g⁻¹ * s * g), Subgroup.Normal.conj_mem' ‹_› s hs g⟩)))
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
noncomputable def inf [S.Normal] : Representation k (G ⧸ S) (invariants (ρ.comp S.subtype)) :=
  (QuotientGroup.con S).lift (invariantsOfNormal ρ S)
    fun x y ⟨⟨z, hz⟩, h⟩ => LinearMap.ext fun ⟨w, hw⟩ => Subtype.ext <| by
    simpa [← h] using congr(ρ y $(hw ⟨z.unop, hz⟩))

variable {ρ S} in
@[simp]
lemma inf_apply [S.Normal] (g : G) (x : invariants (ρ.comp S.subtype)) :
    (inf ρ S (g : G ⧸ S) x).1 = ρ g x :=
  rfl

end Inf
section Coinvariants

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (S : Subgroup G)

/-- The submodule generated by elements of the form `ρ g x - x`. -/
abbrev coinvariantsKer : Submodule k V :=
  Submodule.span k (Set.range <| fun (x : G × V) => ρ x.1 x.2 - x.2)

variable {ρ}

lemma mem_coinvariantsKer_of_eq (g : G) (x : V) (a : V) (h : ρ g x - x = a) :
    a ∈ coinvariantsKer ρ :=
  Submodule.subset_span ⟨(g, x), h⟩

variable (ρ)

/-- The coinvariants of a representation, `V ⧸ ⟨{ρ g x - x | g ∈ G, x ∈ V}⟩`. -/
abbrev coinvariants := V ⧸ coinvariantsKer ρ

abbrev coinvariantsMkQ := Submodule.mkQ (coinvariantsKer ρ)

/-- A `G`-invariant linear map induces a linear map out of the coinvariants of a
`G`-representation. -/
def coinvariantsLift (f : V →ₗ[k] W) (h : ∀ (x : G), f ∘ₗ ρ x = f) :
    ρ.coinvariants →ₗ[k] W :=
  Submodule.liftQ _ f <| Submodule.span_le.2 fun x ⟨⟨g, y⟩, hy⟩ => by
    simpa only [← hy, SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, LinearMap.coe_comp,
      Function.comp_apply] using LinearMap.ext_iff.1 (h g) y

@[simp]
theorem coinvariantsLift_mkQ (f : V →ₗ[k] W) (h : ∀ (x : G), f ∘ₗ ρ x = f) :
  coinvariantsLift ρ f h ∘ₗ (coinvariantsKer ρ).mkQ = f := rfl

@[simp]
theorem coinvariantsLift_apply (f : V →ₗ[k] W) (h : ∀ (x : G), f ∘ₗ ρ x = f) (x : V) :
  coinvariantsLift ρ f h (Submodule.Quotient.mk x) = f x := rfl

section Finsupp
open Finsupp

variable (α : Type*)

/-- Given a `G`-representation `(V, ρ)` and a type `α`, this is the map `(α →₀ V)_G →ₗ (α →₀ V_G)`
sending `⟦single a v⟧ ↦ single a ⟦v⟧`. -/
def coinvariantsToFinsupp :
    coinvariants (ρ.finsupp α) →ₗ[k] α →₀ coinvariants ρ :=
  (coinvariantsLift _ (mapRange.linearMap (Submodule.mkQ _)) <| fun g => lhom_ext fun i x => by
    simp [mapRange.linearMap, ← (Submodule.Quotient.eq _).2
      (mem_coinvariantsKer_of_eq g x _ rfl), finsupp])

@[simp]
lemma coinvariantsToFinsupp_mk_single (x : α) (a : V) :
    coinvariantsToFinsupp ρ α (Submodule.Quotient.mk (Finsupp.single x a)) =
      Finsupp.single x (Submodule.Quotient.mk a) := by simp [coinvariantsToFinsupp]

/-- Given a `G`-representation `(V, ρ)` and a type `α`, this is the map `(α →₀ V_G) →ₗ (α →₀ V)_G`
sending `single a ⟦v⟧ ↦ ⟦single a v⟧`. -/
def finsuppToCoinvariants :
    (α →₀ coinvariants ρ) →ₗ[k] coinvariants (ρ.finsupp α) :=
  lsum (R := k) k fun a => coinvariantsLift _ (Submodule.mkQ _ ∘ₗ lsingle a) fun g =>
    LinearMap.ext fun x => (Submodule.Quotient.eq _).2 <|
    mem_coinvariantsKer_of_eq g (single a x) _ <| by simp

@[simp]
lemma finsuppToCoinvariants_single (a : α) (x : V) :
    finsuppToCoinvariants ρ α (single a <| Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (single a x) := by simp [finsuppToCoinvariants]

/-- Given a `G`-representation `(V, ρ)` and a type `α`, this is the linear equivalence
`(α →₀ V)_G ≃ₗ (α →₀ V_G)` sending `⟦single a v⟧ ↦ single a ⟦v⟧`. -/
abbrev coinvariantsFinsuppLEquiv :
    coinvariants (ρ.finsupp α) ≃ₗ[k] α →₀ coinvariants ρ :=
  LinearEquiv.ofLinear (coinvariantsToFinsupp ρ α) (finsuppToCoinvariants ρ α)
    (Finsupp.lhom_ext fun a x => Quotient.inductionOn' x fun y => by
      simp [coinvariantsToFinsupp, finsuppToCoinvariants, Submodule.Quotient.mk''_eq_mk])
    (Submodule.linearMap_qext _ <| Finsupp.lhom_ext fun a x => by
      simp [finsuppToCoinvariants, coinvariantsToFinsupp])

end Finsupp

section TensorProduct
open TensorProduct

@[simp]
lemma coinvariantsMk_ρ_inv_tmul (τ : Representation k G W) (x : V) (y : W) (g : G) :
    Submodule.Quotient.mk (p := (ρ.tprod τ).coinvariantsKer) (ρ g⁻¹ x ⊗ₜ[k] y) =
      Submodule.Quotient.mk (p := (ρ.tprod τ).coinvariantsKer) (x ⊗ₜ[k] τ g y) :=
  (Submodule.Quotient.eq _).2 <| mem_coinvariantsKer_of_eq g⁻¹ (x ⊗ₜ[k] τ g y) _ <| by simp

@[simp]
lemma coinvariantsMk_tmul_ρ_inv (τ : Representation k G W) (x : V) (y : W) (g : G) :
    Submodule.Quotient.mk (p := (ρ.tprod τ).coinvariantsKer) (x ⊗ₜ[k] τ g⁻¹ y) =
      Submodule.Quotient.mk (p := (ρ.tprod τ).coinvariantsKer) (ρ g x ⊗ₜ[k] y) :=
  (Submodule.Quotient.eq _).2 <| mem_coinvariantsKer_of_eq g⁻¹ (ρ g x ⊗ₜ[k] y) _ <| by simp

/-- Given a `k`-linear `G`-representation `V, ρ`, this is the map `(V ⊗ k[G])_G →ₗ[k] V` sending
`⟦v ⊗ single g r⟧ ↦ r • ρ(g⁻¹)(v)`. -/
def ofCoinvariantsTprodLeftRegular :
    coinvariants (V := V ⊗[k] (G →₀ k)) (ρ.tprod (leftRegular k G)) →ₗ[k] V :=
  coinvariantsLift _ (TensorProduct.lift (Finsupp.linearCombination _
    fun g => ρ g⁻¹) ∘ₗ (TensorProduct.comm _ _ _).toLinearMap) fun g => TensorProduct.ext <|
      LinearMap.ext fun (x : V) => Finsupp.lhom_ext fun a y => by simp

@[simp] lemma ofCoinvariantsTprodLeftRegular_mk_tmul_single (x : V) (g : G) (r : k) :
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
        apply mem_coinvariantsKer_of_eq g⁻¹ (a ⊗ₜ Finsupp.single g r)
        simp_all [TensorProduct.smul_tmul', TensorProduct.smul_tmul]

end TensorProduct
end Coinvariants
section Coinf

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (S : Subgroup G)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G`-representation on the
coinvariants of `ρ|_S`. -/
@[simps]
noncomputable def coinvariantsOfNormal [S.Normal] :
    Representation k G (coinvariants (ρ.comp S.subtype)) where
  toFun g := coinvariantsLift (ρ.comp S.subtype) ((coinvariantsKer _).mkQ ∘ₗ ρ g) fun ⟨s, hs⟩ => by
    ext x
    simpa [Submodule.Quotient.eq] using mem_coinvariantsKer_of_eq
      (ρ := ρ.comp S.subtype) ⟨g * s * g⁻¹, Subgroup.Normal.conj_mem ‹_› s hs g⟩ (ρ g x)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the coinvariants of `ρ|_S`. -/
noncomputable def coinf [h1 : S.Normal] :
    Representation k (G ⧸ S) (coinvariants (ρ.comp S.subtype)) :=
  (QuotientGroup.con S).lift (coinvariantsOfNormal ρ S)
    fun x y ⟨⟨z, hz⟩, h⟩ => Submodule.linearMap_qext _ <| by
      ext w
      simpa [← h, Submodule.Quotient.eq] using mem_coinvariantsKer_of_eq
        ⟨y * z.unop * y ⁻¹, h1.conj_mem z.unop hz y⟩ (ρ y w) _ (by simp)

variable {ρ S} in
@[simp]
lemma coinf_apply [S.Normal] (g : G) (x : V) :
    coinf ρ S (g : G ⧸ S) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) :=
  rfl

end Coinf
end Representation
namespace Rep

open CategoryTheory

variable (k G : Type u) [CommRing k] [Group G] (A : Rep k G)

section Invariants

/-- The functor sending a representation to its submodule of invariants. -/
@[simps]
noncomputable def invariantsFunctor : Rep k G ⥤ ModuleCat.{u} k where
  obj A := ModuleCat.of k A.ρ.invariants
  map {A B} f := (f.hom ∘ₗ A.ρ.invariants.subtype).codRestrict
    B.ρ.invariants fun ⟨c, hc⟩ g => by
      have := (hom_comm_apply f g c).symm
      simp_all [moduleCat_simps, hc g]

instance : (invariantsFunctor k G).PreservesZeroMorphisms where

instance : (invariantsFunctor k G).Additive where

/-- The adjunction between the functor equipping a module with the trivial representation, and
the functor sending a representation to its submodule of invariants. -/
noncomputable abbrev invariantsAdjunction : trivialFunctor ⊣ invariantsFunctor k G :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => LinearMap.codRestrict _ f.hom fun x g => (hom_comm_apply f _ _).symm
      invFun := fun f => {
        hom := Submodule.subtype _ ∘ₗ f
        comm := fun g => by ext x; exact ((f x).2 g).symm }
      left_inv := by intros f; rfl
      right_inv := by intros f; rfl }
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; rfl }

noncomputable instance : Limits.PreservesLimits (invariantsFunctor k G) :=
  (invariantsAdjunction k G).rightAdjointPreservesLimits

end Invariants
section Inf

variable {k G} (S : Subgroup G) [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
abbrev inf := Rep.of (A.ρ.inf S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation morphism `f : A ⟶ B` induces a
`G ⧸ S`-representation morphism `invariants ρ_A|_S ⟶ invariants ρ_B|_S`. -/
@[simps]
noncomputable def infMap {A B : Rep k G} (φ : A ⟶ B) :
    inf A S ⟶ inf B S where
  hom := (invariantsFunctor k S).map ((Action.res _ S.subtype).map φ)
  comm g := QuotientGroup.induction_on g fun g => LinearMap.ext
    fun x => Subtype.ext (hom_comm_apply φ g x.1)

/-- Given a normal subgroup `S ≤ G`, this functor sends a `G`-representation `ρ` to the
`G ⧸ S`-representation induced on the invariants of `ρ|_S`. -/
@[simps]
noncomputable def infFunctor : Rep k G ⥤ Rep k (G ⧸ S) where
  obj A := inf A S
  map f := infMap S f

end Inf

section Coinvariants

variable {k G A} {B C : Rep k G} {n : ℕ} {V : Type u} [AddCommGroup V] [Module k V]

open Representation

/-- A `G`-representation morphism `A ⟶ trivial(V)` induces a linear map `A_G →ₗ[k] V`. -/
def coinvariantsLift (f : A ⟶ Rep.trivial k G V) :
    coinvariants A.ρ →ₗ[k] V :=
  Representation.coinvariantsLift _ f.hom f.comm

/-- A `G`-representation morphism `A ⟶ B` induces a linear map `A_G →ₗ[k] B_G`. -/
abbrev coinvariantsMap (f : A ⟶ B) :
    coinvariants A.ρ →ₗ[k] coinvariants B.ρ :=
  Representation.coinvariantsLift _ (Submodule.mkQ _ ∘ₗ f.hom) fun g => LinearMap.ext fun x =>
    (Submodule.Quotient.eq _).2 <| mem_coinvariantsKer_of_eq g (f.hom x) _ <| by
      simpa using (hom_comm_apply f g x).symm

@[simp]
theorem coinvariantsMap_mkQ (f : A ⟶ B) :
    coinvariantsMap f ∘ₗ (coinvariantsKer A.ρ).mkQ = (coinvariantsKer B.ρ).mkQ ∘ₗ f.hom := rfl

@[simp]
theorem coinvariantsMap_apply (f : A ⟶ B) (x : A) :
    coinvariantsMap f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f.hom x) := rfl

lemma ugh (A : ModuleCat k) : 𝟙 A = LinearMap.id := rfl

attribute [moduleCat_simps] ugh

@[simp]
theorem coinvariantsMap_id (A : Rep k G) :
    coinvariantsMap (𝟙 A) = LinearMap.id := by
  ext; simp [moduleCat_simps]

@[simp]
theorem coinvariantsMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    coinvariantsMap (f ≫ g) = coinvariantsMap g ∘ₗ coinvariantsMap f := by
  ext; simp [moduleCat_simps]

variable (A B)

/-- For a representation `A` of a finite group `G`, the norm map `A ⟶ A` induces a linear map
`A_G →ₗ[k] Aᴳ`. -/
noncomputable def liftRestrictNorm [Fintype G] :
    A.ρ.coinvariants →ₗ[k] A.ρ.invariants :=
  A.ρ.coinvariantsLift ((norm A).hom.codRestrict _
    fun a g => congr($(ρ_comp_norm A g) a)) fun g => by ext x; exact congr($(norm_comp_ρ A g) x)

variable (k G)

/-- The functor sending a representation to its coinvariants. -/
@[simps]
def coinvariantsFunctor : Rep k G ⥤ ModuleCat k where
  obj A := ModuleCat.of k (A.ρ.coinvariants)
  map f := coinvariantsMap f

instance : (coinvariantsFunctor k G).Additive where
  map_add := LinearMap.ext fun x => Quotient.inductionOn' x (fun _ => rfl)

/-- The adjunction between the functor sending a representation to its coinvariants and the functor
equipping a module with the trivial representation. -/
noncomputable def coinvariantsAdjunction : coinvariantsFunctor k G ⊣ trivialFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => {
        hom := f ∘ₗ X.ρ.coinvariantsKer.mkQ
        comm := fun g => by
          ext x
          exact congr(f $((Submodule.Quotient.eq <| X.ρ.coinvariantsKer).2
            (X.ρ.mem_coinvariantsKer_of_eq g x _ rfl))) }
      invFun := fun f => coinvariantsLift f
      left_inv := fun x => Submodule.linearMap_qext _ rfl
      right_inv := fun x => Action.Hom.ext rfl }
    homEquiv_naturality_left_symm := by intros; apply Submodule.linearMap_qext; rfl
    homEquiv_naturality_right := by intros; rfl }

instance : (coinvariantsFunctor k G).PreservesZeroMorphisms where
  map_zero _ _ := Submodule.linearMap_qext _ rfl

noncomputable instance : Limits.PreservesColimits (coinvariantsFunctor k G) :=
  (coinvariantsAdjunction k G).leftAdjointPreservesColimits

variable {k G} (α : Type u) [DecidableEq α]

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

@[simp]
lemma finsuppToCoinvariantsTensorFree_single (i : α) (x : A) :
    finsuppToCoinvariantsTensorFree A α (single i x) =
      Submodule.Quotient.mk (x ⊗ₜ single i (single (1 : G) (1 : k))) := by
  have := finsuppTensorRight_inv_apply_single (A := A) (B := leftRegular k G)
  simp_all [finsuppToCoinvariantsTensorFree, coinvariantsMap, moduleCat_simps,
    ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj]

variable (A α)

/-- Given a `k`-linear `G`-representation `(A, ρ)` and a type `α`, this is the linear equivalence
`(A ⊗ (α →₀ k[G]))_G ≃ₗ[k] (α →₀ A)` sending
`⟦a ⊗ single x (single g r)⟧ ↦ single x (r • ρ(g⁻¹)(a)).` -/
abbrev coinvariantsTensorFreeLEquiv :
    coinvariants (A ⊗ free k G α).ρ ≃ₗ[k] (α →₀ A) :=
  LinearEquiv.ofLinear (coinvariantsTensorFreeToFinsupp A α) (finsuppToCoinvariantsTensorFree A α)
    (lhom_ext fun i a => by
      simp [-coe_tensor, -tensor_ρ, coinvariantsTensorFreeToFinsupp_mk_tmul_single a]) <|
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
    app := fun A => coinvariantsMap (f ⊗ 𝟙 A)
    naturality := fun _ _ _ => Submodule.linearMap_qext _ <| TensorProduct.ext' fun _ _ => by rfl }
  map_id _ := NatTrans.ext <| funext fun _ => by
    simpa only [tensorHom_id, id_whiskerRight] using (coinvariantsFunctor k G).map_id _
  map_comp _ _ := NatTrans.ext <| funext fun _ => by
    simpa only [tensorHom_id, comp_whiskerRight] using (coinvariantsFunctor k G).map_comp _ _

instance (A : Rep k G) : ((coinvariantsTensor k G).obj A).Additive := by
  unfold coinvariantsTensor
  infer_instance

/-
abbrev coinvariantsFinsuppIso (A : Rep k G) (α : Type u) :
    (coinvariantsFunctor k G).obj (A.finsupp α)
      ≅ ModuleCat.of k (α →₀ (coinvariantsFunctor k G).obj A) :=
  (coinvariantsFinsuppLEquiv A.ρ α).toModuleIso

abbrev coinvariantsTensorLeftRegular (A : Rep k G) :
    (coinvariantsFunctor k G).obj (A ⊗ Rep.leftRegular k G) ≅ A.V :=
  A.ρ.coinvariantsTprodLeftRegularLEquiv.toModuleIso

open MonoidalCategory

abbrev coinvariantsTensorFreeIso (A : Rep k G) (α : Type u) [DecidableEq α] :
    (coinvariantsFunctor k G).obj (A ⊗ Rep.free k G α) ≅ ModuleCat.of k (α →₀ A) :=
  (A.coinvariantsTensorFreeLEquiv α).toModuleIso-/
end Coinvariants

/-- Given a finite group `G`, this is the natural transformation sending a `G`-representation `A`
to the map `A_G →ₗ[k] Aᴳ` induced by the norm map on `A`. -/
@[simps]
noncomputable def liftRestrictNormNatTrans [Fintype G] :
    coinvariantsFunctor k G ⟶ invariantsFunctor k G where
  app A := liftRestrictNorm A
  naturality _ _ f := Submodule.linearMap_qext _ <| LinearMap.ext fun x => Subtype.ext <| by
    have := hom_comm_apply f
    simp_all [norm, moduleCat_simps, liftRestrictNorm]

section Coinf

variable {k G} (S : Subgroup G) [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the coinvariants of `ρ|_S`. -/
abbrev coinf := Rep.of (A.ρ.coinf S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation morphism `f : A ⟶ B` induces a
`G ⧸ S`-representation morphism `coinvariants ρ_A|_S ⟶ coinvariants ρ_B|_S`. -/
noncomputable abbrev coinfMap {A B : Rep k G} (φ : A ⟶ B) :
    coinf A S ⟶ coinf B S :=
  mkHom ((coinvariantsFunctor k S).map ((Action.res _ S.subtype).map φ))
    fun g => QuotientGroup.induction_on g fun g => Submodule.linearMap_qext _ <|
    LinearMap.ext fun _ => (Submodule.Quotient.eq _).2 <| by
      have := hom_comm_apply φ
      simp_all [moduleCat_simps]

/-- Given a normal subgroup `S ≤ G`, this functor sends a `G`-representation `ρ` to the
`G ⧸ S`-representation induced on the coinvariants of `ρ|_S`. -/
@[simps]
noncomputable def coinfFunctor : Rep k G ⥤ Rep k (G ⧸ S) where
  obj A := coinf A S
  map f := coinfMap S f
  map_id _ := Action.Hom.ext <| coinvariantsMap_id _
  map_comp _ _ := Action.Hom.ext <| by simp [moduleCat_simps]

end Coinf
end Rep
