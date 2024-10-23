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

open MonoidAlgebra

open Representation

namespace GroupAlgebra

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

lemma mem_coinvariantsKer_of_eq (g : G) (x : V) (a : V) (h : ρ g x - x = a) :
    a ∈ coinvariantsKer ρ :=
  Submodule.subset_span ⟨(g, x), h⟩

/-- The coinvariants of a representation, `V ⧸ ⟨{ρ g x - x | g ∈ G, x ∈ V}⟩`. -/
abbrev coinvariants := V ⧸ coinvariantsKer ρ

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
      (ρ.comp S.subtype) ⟨g * s * g⁻¹, Subgroup.Normal.conj_mem ‹_› s hs g⟩ (ρ g x)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the coinvariants of `ρ|_S`. -/
noncomputable def coinf [h1 : S.Normal] :
    Representation k (G ⧸ S) (coinvariants (ρ.comp S.subtype)) :=
  (QuotientGroup.con S).lift (coinvariantsOfNormal ρ S)
    fun x y ⟨⟨z, hz⟩, h⟩ => Submodule.linearMap_qext _ <| by
      ext w
      simpa [← h, Submodule.Quotient.eq] using mem_coinvariantsKer_of_eq _
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
  map {A B} f := (hom f ∘ₗ A.ρ.invariants.subtype).codRestrict
    B.ρ.invariants fun ⟨c, hc⟩ g => by simp [← hom_comm_apply'', hc g]

instance : (invariantsFunctor k G).PreservesZeroMorphisms where

instance : (invariantsFunctor k G).Additive where

/-- The adjunction between the functor equipping a module with the trivial representation, and
the functor sending a representation to its submodule of invariants. -/
noncomputable abbrev invariantsAdjunction : trivialFunctor ⊣ invariantsFunctor k G :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => LinearMap.codRestrict _ f.hom fun x g =>
        (hom_comm_apply'' f _ _).symm
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
  comm g := QuotientGroup.induction_on g (fun g => LinearMap.ext
    fun x => Subtype.ext (Rep.hom_comm_apply'' φ g x.1))

/-- Given a normal subgroup `S ≤ G`, this functor sends a `G`-representation `ρ` to the
`G ⧸ S`-representation induced on the invariants of `ρ|_S`. -/
@[simps]
noncomputable def infFunctor : Rep k G ⥤ Rep k (G ⧸ S) where
  obj A := inf A S
  map f := infMap S f

end Inf

section Coinvariants

variable {k G} {A B C : Rep k G} {n : ℕ} {V : Type u} [AddCommGroup V] [Module k V]

open Representation

/-- A `G`-representation morphism `A ⟶ trivial(V)` induces a linear map `A_G →ₗ[k] V`. -/
def coinvariantsLift (f : A ⟶ Rep.trivial k G V) :
    coinvariants A.ρ →ₗ[k] V :=
  Representation.coinvariantsLift _ (hom f) f.comm

/-- A `G`-representation morphism `A ⟶ B` induces a linear map `A_G →ₗ[k] B_G`. -/
def coinvariantsMap (f : A ⟶ B) :
    coinvariants A.ρ →ₗ[k] coinvariants B.ρ :=
  Representation.coinvariantsLift _ (Submodule.mkQ _ ∘ₗ hom f) fun g => LinearMap.ext fun x => by
    simpa [hom_comm_apply'', Submodule.Quotient.eq]
    using mem_coinvariantsKer_of_eq B.ρ g (hom f x) _ rfl

@[simp]
theorem coinvariantsMap_mkQ (f : A ⟶ B) :
    coinvariantsMap f ∘ₗ (coinvariantsKer A.ρ).mkQ = (coinvariantsKer B.ρ).mkQ ∘ₗ hom f := rfl

@[simp]
theorem coinvariantsMap_apply (f : A ⟶ B) (x : A) :
    coinvariantsMap f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (hom f x) := rfl

@[simp]
theorem coinvariantsMap_id (A : Rep k G) :
    coinvariantsMap (𝟙 A) = LinearMap.id := by
  ext; simp

@[simp]
theorem coinvariantsMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    coinvariantsMap (f ≫ g) = coinvariantsMap g ∘ₗ coinvariantsMap f := by
  ext; simp

variable (A B)

/-- For a representation `A` of a finite group `G`, the norm map `A ⟶ A` induces a linear map
`A_G →ₗ[k] Aᴳ`. -/
noncomputable def liftRestrictNorm [Fintype G] :
    A.ρ.coinvariants →ₗ[k] A.ρ.invariants :=
  A.ρ.coinvariantsLift ((hom <| norm A).codRestrict _
    fun a g => congr($(ρ_comp_norm A g) a)) fun g => by ext x; exact congr($(norm_comp_ρ A g) x)

variable (k G)

/-- The functor sending a representation to its coinvariants. -/
@[simps]
def coinvariantsFunctor : Rep k G ⥤ ModuleCat k where
  obj A := ModuleCat.of k (A.ρ.coinvariants)
  map f := coinvariantsMap f

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

end Coinvariants

/-- Given a finite group `G`, this is the natural transformation sending a `G`-representation `A`
to the map `A_G →ₗ[k] Aᴳ` induced by the norm map on `A`. -/
@[simps]
noncomputable def liftRestrictNormNatTrans [Fintype G] :
    coinvariantsFunctor k G ⟶ invariantsFunctor k G where
  app A := liftRestrictNorm A
  naturality _ _ _ := Submodule.linearMap_qext _ <| LinearMap.ext fun x => Subtype.ext <| by
    simp [norm, ModuleCat.comp_def, ModuleCat.hom_def, ModuleCat.coe_of, liftRestrictNorm,
      hom_comm_apply'']

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
    fun g => QuotientGroup.induction_on g fun g =>
    Submodule.linearMap_qext _ <| by
      ext x
      refine (Submodule.Quotient.eq _).2 ?_
      simp [coe_res_obj, ← hom_comm_apply'']

/-- Given a normal subgroup `S ≤ G`, this functor sends a `G`-representation `ρ` to the
`G ⧸ S`-representation induced on the coinvariants of `ρ|_S`. -/
@[simps]
noncomputable def coinfFunctor : Rep k G ⥤ Rep k (G ⧸ S) where
  obj A := coinf A S
  map f := coinfMap S f
  map_id _ := Rep.ext <| coinvariantsMap_id _
  map_comp _ _ := Rep.ext <| by simp

end Coinf
end Rep
