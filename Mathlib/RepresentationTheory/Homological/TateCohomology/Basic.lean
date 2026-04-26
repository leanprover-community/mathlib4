module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality


/-!
## Tate Cohomology

This file defines Tate cohomology of finite groups by taking homology of Tate complex. We
define Tate complex by connecting the inhomogeneous chain complex and cochain complex using
norm map.

## Key definitions

* `Rep.tateNorm`: the map induced by the norm map from the zeroth term of the inhomogeneous chain
  complex to the zeroth term of the inhomogeneous cochain complex.

* `tateComplex`: the Tate complex defined by connecting the inhomogeneous chain complex and
  cochain complex using the Tate norm.

* `tateComplexFunctor`: the functor taking a representation of `G` to its Tate complex.

* `tateCohomologyFunctor`: the functor taking a representation of `G` to its `n`-th Tate
  cohomology group.

## Tags

Tate cohomology, homological algebra
-/

@[expose] public noncomputable section

universe u v

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

open CategoryTheory groupCohomology groupHomology

/-- This is the map from the coinvariants of `M : Rep R G` to the invariants, induced by the map
`m ↦ ∑ g : G, M.ρ g m`. -/
def Rep.tateNorm (M : Rep R G) : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0 :=
  (chainsIso₀ M).hom ≫ M.norm.toModuleCatHom ≫ (cochainsIso₀ M).inv

lemma tateNorm_hom_apply (M : Rep R G) (x : (Fin 0 → G) →₀ ↑M.V) (y : Fin 0 → G) :
    M.tateNorm.hom x y = (cochainsIso₀ M).inv.hom (M.ρ.norm <| (chainsIso₀ M).hom.hom x) y := rfl

set_option backward.isDefEq.respectTransparency false in
lemma Rep.tateNorm_eq (M : Rep R G) :
    M.tateNorm = ModuleCat.ofHom (Finsupp.lsum R fun _ ↦ LinearMap.pi fun _ ↦ M.ρ.norm) := by
  ext
  simp only [CochainComplex.of_X, Rep.tateNorm, ChainComplex.of_X, chainsIso₀,
    LinearEquiv.toModuleIso_hom, Rep.norm, cochainsIso₀, LinearEquiv.toModuleIso_inv,
    ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearEquiv.funUnique_symm_apply, Function.comp_apply, Finsupp.lsingle_apply,
    Finsupp.LinearEquiv.finsuppUnique_apply, AddEquiv.funUnique_symm_apply,
    Finsupp.lsum_comp_lsingle, LinearMap.pi_apply]
  congr
  simp only [Finsupp.single_apply, ite_eq_left_iff]
  exact fun h ↦ False.elim <| h <| Unique.eq_default _

@[reassoc (attr := simp), elementwise]
lemma Rep.norm_comp_d_eq_zero (M : Rep R G) : M.norm.toModuleCatHom ≫ d₀₁ M = 0 := by
  ext; simp [Pi.zero_apply _]

set_option backward.isDefEq.respectTransparency false in
lemma Rep.tateNorm_comp_d (M : Rep R G) : tateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0 := by
  simp [tateNorm]

@[simp]
lemma Rep.comp_eq_zero (M : Rep R G) : d₁₀ M ≫ M.norm.toModuleCatHom = 0 := by
  ext
  simp [d₁₀_single M, Rep.norm, ← LinearMap.comp_apply]

set_option backward.isDefEq.respectTransparency false in
lemma Rep.d_comp_tateNorm (M : Rep R G) : (inhomogeneousChains M).d 1 0 ≫ M.tateNorm = 0 := by
  simp only [ChainComplex.of_X, CochainComplex.of_X, tateNorm, ← Category.assoc]
  simp [← comp_d₁₀_eq]

/-- The Tate norm connecting complexes of inhomogeneous chains and cochains. -/
@[simps]
def tateComplexConnectData (M : Rep R G) :
    CochainComplex.ConnectData (inhomogeneousChains M) (inhomogeneousCochains M) where
  d₀ := M.tateNorm
  comp_d₀ := Rep.d_comp_tateNorm _
  d₀_comp := Rep.tateNorm_comp_d _

/-- The Tate complex defined by connecting inhomogeneous chains and cochains with the Tate norm. -/
abbrev tateComplex (M : Rep R G) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.ConnectData.cochainComplex (tateComplexConnectData M)

lemma tateComplex_d_neg_one (M : Rep R G) : (tateComplex M).d (-1) 0 = M.tateNorm := by rfl

lemma tateComplex_d_ofNat (M : Rep R G) (n : ℕ) :
    (tateComplex M).d n (n + 1) = (inhomogeneousCochains M).d n (n + 1) := rfl

lemma tateComplex_d_neg (M : Rep R G) (n : ℕ) :
    (tateComplex M).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ)) = (inhomogeneousChains M).d (n + 1) n := rfl

@[reassoc]
lemma tateComplex.norm_comm {A B : Rep R G} (φ : A ⟶ B) : φ ≫ B.norm = A.norm ≫ φ := by
  ext
  simp [Rep.norm_comm]

@[reassoc]
lemma tateComplex.norm_hom_comm {A B : Rep R G} (φ : A ⟶ B) :
    φ.toModuleCatHom ≫ B.norm.toModuleCatHom = A.norm.toModuleCatHom ≫ φ.toModuleCatHom := by
  rw [← ModuleCat.ofHom_comp, ← Representation.IntertwiningMap.comp_toLinearMap,
    ← Rep.hom_comp, A.norm_comm φ]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The chain map on the Tate complex induced by a morphism of representations. -/
@[reducible]
def tateComplex.map {X Y : Rep R G} (φ : X ⟶ Y) : tateComplex X ⟶ tateComplex Y := by
  refine CochainComplex.ConnectData.map _ _ (chainsMap (.id G) φ) (cochainsMap (.id G) φ) ?_
  ext
  simp [Rep.tateNorm_eq, Representation.norm, Rep.hom_comm_apply]

@[simp]
lemma tateComplex.map_zero {X Y : Rep R G} : tateComplex.map (X := X) (Y := Y) 0 = 0 := by aesop_cat

/-- The functor taking a representation of `G` to its Tate complex. -/
@[simps]
def tateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := tateComplex M
  map := tateComplex.map
  map_comp f g := by
    unfold tateComplex.map
    rw [CochainComplex.ConnectData.map_comp_map]
    congr 1
    rw [← chainsMap_comp]
    congr 1

/-- The functor taking a representation of `G` to its `n`-th Tate cohomology group. -/
def tateCohomologyFunctor (n : ℤ) : Rep R G ⥤ ModuleCat R :=
  tateComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- The shortcut path of taking Tate cohomology which aligns with
`groupCohomology` and `groupHomology`. -/
abbrev tateCohomology (M : Rep R G) (n : ℤ) : ModuleCat R := (tateCohomologyFunctor n).obj M
