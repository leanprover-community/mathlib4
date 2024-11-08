import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.ProjectiveResolution
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
universe v u
variable (n : ℕ)

open CategoryTheory

lemma Fin.comp_contractNth {G H : Type*} [MulOneClass G] [MulOneClass H] (f : G →* H)
    (j : Fin (n + 1)) (g : Fin (n + 1) → G) :
    f ∘ Fin.contractNth j (· * ·) g = Fin.contractNth j (· * ·) (f ∘ g) := by
  ext x
  rcases lt_trichotomy (x : ℕ) j with (h|h|h)
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_eq, h, f.map_mul]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_gt, h]

namespace LinearMap

lemma ker_compLeft
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (I : Type*) :
    LinearMap.ker (f.compLeft I) = Submodule.pi (Set.univ : Set I) (fun _ => LinearMap.ker f) :=
  Submodule.ext fun _ => ⟨fun (hx : _ = _) i _ => congr_fun hx i,
    fun hx => funext fun i => hx i trivial⟩

lemma range_compLeft
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (I : Type*) :
    LinearMap.range (f.compLeft I) = Submodule.pi (Set.univ : Set I) (fun _ => LinearMap.range f) :=
  Submodule.ext fun _ => ⟨fun ⟨y, hy⟩ i _ => ⟨y i, congr_fun hy i⟩, fun hx => by
    choose y hy using hx
    exact ⟨fun i => y i trivial, funext fun i => hy i trivial⟩⟩

end LinearMap
namespace ModuleCat

variable (R : Type u) [Ring R]

lemma asHom_comp {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    asHom (g ∘ₗ f) = asHom f ≫ asHom g := rfl

end ModuleCat

namespace groupCohomology
open Rep

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : (Action.res _ f).obj A ⟶ B) (n : ℕ)

open Representation
variable (S : Subgroup G)

noncomputable def infHom [S.Normal] : (Action.res _ (QuotientGroup.mk' S)).obj (Rep.inf B S) ⟶ B :=
  mkHom (invariants (B.ρ.comp S.subtype)).subtype <| by intros; rfl

@[simps (config := .lemmasOnly)]
noncomputable def cochainsMap :
    inhomogeneousCochains A ⟶ inhomogeneousCochains B where
  f i := ModuleCat.asHom (φ.hom.compLeft (Fin i → G)
    ∘ₗ LinearMap.funLeft k A (fun x : Fin i → G => (f ∘ x)))
  comm' i j (hij : _ = _) := by
    subst hij
    ext x
    funext g
    simp only [CochainComplex.of_x, inhomogeneousCochains.d_def, ModuleCat.coe_comp,
      Function.comp_apply]
    simpa [ModuleCat.asHom, ModuleCat.coe_of, ModuleCat.hom_def, Fin.comp_contractNth]
      using (hom_comm_apply φ _ _).symm

@[simp]
lemma cochainsMap_f_apply (n : ℕ) (x : (inhomogeneousCochains A).X n) (g : Fin n → G) :
    (cochainsMap f φ).f n x g = φ.hom (x (f ∘ g)) :=
  rfl

@[simp]
lemma cochainsMap_id :
    cochainsMap (MonoidHom.id _) (𝟙 A) = 𝟙 (inhomogeneousCochains A) := by
  rfl

@[simp]
lemma cochainsMap_eq_compLeft {A B : Rep k G} (f : A ⟶ B) (i : ℕ) :
    (cochainsMap (MonoidHom.id G) f).f i = f.hom.compLeft _ := by
  ext
  rfl

@[simp]
lemma cochainsMap_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    cochainsMap (f.comp g) ((Action.res _ g).map φ ≫ ψ) =
      cochainsMap f φ ≫ cochainsMap g ψ := by
  rfl

@[simp]
lemma cochainsMap_zero : cochainsMap (A := A) (B := B) f 0 = 0 := by rfl

instance cochainsMap_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : ℕ) :
    Mono ((cochainsMap (MonoidHom.id G) φ).f i) :=
  (ModuleCat.mono_iff_injective _).2 <| Function.Injective.comp_left <|
    (Rep.mono_iff_injective φ).1 inferInstance

instance cochainsMap_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : ℕ) :
    Epi ((cochainsMap (MonoidHom.id G) φ).f i) :=
  (ModuleCat.epi_iff_surjective _).2 <| Function.Surjective.comp_left <|
    (Rep.epi_iff_surjective φ).1 inferInstance

noncomputable abbrev cocyclesMap (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology.cocycles B n :=
  HomologicalComplex.cyclesMap (cochainsMap f φ) n

theorem cocyclesMap_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) (n : ℕ) :
    cocyclesMap (f.comp g) ((Action.res _ g).map φ ≫ ψ) n =
      cocyclesMap f φ n ≫ cocyclesMap g ψ n := by
  simp [cocyclesMap, HomologicalComplex.cyclesMap_comp]

noncomputable abbrev cohomologyMap (n : ℕ) :
  groupCohomology A n ⟶ groupCohomology B n :=
HomologicalComplex.homologyMap (cochainsMap f φ) n

theorem cohomologyMap_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) (n : ℕ) :
    cohomologyMap (f.comp g) ((Action.res _ g).map φ ≫ ψ) n
      = cohomologyMap f φ n ≫ cohomologyMap g ψ n := by
  rw [cohomologyMap, cochainsMap_comp, HomologicalComplex.homologyMap_comp]

abbrev fOne := φ.hom.compLeft G ∘ₗ LinearMap.funLeft k A f
abbrev fTwo := φ.hom.compLeft (G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f f)
abbrev fThree := φ.hom.compLeft (G × G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f (Prod.map f f))

@[reassoc (attr := simp)]
lemma cochainsMap_f_0_comp_zeroCochainsLEquiv :
    (cochainsMap f φ).f 0 ≫ (zeroCochainsLEquiv B : (inhomogeneousCochains B).X 0 →ₗ[k] B)
      = (zeroCochainsLEquiv A : (inhomogeneousCochains A).X 0 →ₗ[k] A) ≫ φ.hom := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_1_comp_oneCochainsLEquiv :
    (cochainsMap f φ).f 1 ≫ (oneCochainsLEquiv B : (inhomogeneousCochains B).X 1 →ₗ[k] G → B)
      = (oneCochainsLEquiv A).toModuleIso.hom ≫ ModuleCat.asHom (fOne f φ) := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_2_comp_twoCochainsLEquiv :
    (cochainsMap f φ).f 2
      ≫ (twoCochainsLEquiv B : (inhomogeneousCochains B).X 2 →ₗ[k] G × G → B)
      = (twoCochainsLEquiv A).toModuleIso.hom ≫ ModuleCat.asHom (fTwo f φ) := by
  ext x
  funext g
  show φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_3_comp_threeCochainsLEquiv :
    (cochainsMap f φ).f 3
      ≫ (threeCochainsLEquiv B : (inhomogeneousCochains B).X 3 →ₗ[k] G × G × G → B)
      = (threeCochainsLEquiv A).toModuleIso.hom ≫ ModuleCat.asHom (fThree f φ) := by
  ext x
  funext g
  show φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

open ShortComplex

def mapH0 : ModuleCat.of k (H0 A) ⟶ ModuleCat.of k (H0 B) :=
  LinearMap.codRestrict _ (φ.hom ∘ₗ A.ρ.invariants.subtype) fun ⟨c, hc⟩ g => by
    have := (hom_comm_apply φ g c).symm
    simp_all [moduleCat_simps, hc (f g)]

@[simp]
theorem mapH0_id : mapH0 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

theorem mapH0_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    mapH0 (f.comp g) ((Action.res _ g).map φ ≫ ψ) = mapH0 f φ ≫ mapH0 g ψ := rfl

theorem mapH0_eq_invariantsFunctor_map {A B : Rep k G} (f : A ⟶ B) :
    mapH0 (MonoidHom.id G) f = (invariantsFunctor k G).map f := by
  rfl

instance mono_mapH0_of_mono {A B : Rep k G} (f : A ⟶ B) [Mono f] :
    Mono (mapH0 (MonoidHom.id G) f) :=
  (inferInstanceAs (Mono <| (invariantsFunctor k G).map f))

@[reassoc (attr := simp)]
theorem cocyclesMap_comp_isoZeroCocycles_hom :
    cocyclesMap f φ 0 ≫ (isoZeroCocycles B).hom
      = (isoZeroCocycles A).hom ≫ mapH0 f φ := by
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq,
    ← cancel_mono (HomologicalComplex.iCycles _ _)]
  simp only [CochainComplex.of_x, cocyclesMap, Category.assoc, HomologicalComplex.cyclesMap_i,
    isoZeroCocycles_inv_comp_iCocycles_assoc, ModuleCat.of_coe, LinearEquiv.toModuleIso_inv,
    isoZeroCocycles_inv_comp_iCocycles]
  rfl

@[reassoc (attr := simp)]
theorem cohomologyMap_comp_isoH0_hom :
    cohomologyMap f φ 0 ≫ (isoH0 B).hom = (isoH0 A).hom ≫ mapH0 f φ := by
  simp [← cancel_epi (groupCohomologyπ _ _)]

@[simps]
def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := φ.hom
  τ₂ := ModuleCat.asHom (fOne f φ)
  τ₃ := ModuleCat.asHom (fTwo f φ)
  comm₁₂ := by
    ext x
    funext g
    dsimp [shortComplexH1, dZero]
    simpa [ModuleCat.coe_of, ModuleCat.hom_def, fOne] using (hom_comm_apply φ g x).symm
  comm₂₃ := by
    ext x
    funext g
    dsimp [shortComplexH1, dOne]
    simpa [ModuleCat.coe_of, ModuleCat.hom_def, fOne, fTwo] using (hom_comm_apply φ _ _).symm

@[simp]
theorem mapShortComplexH1_id :
    mapShortComplexH1 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

theorem mapShortComplexH1_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    mapShortComplexH1 (f.comp g) ((Action.res _ g).map φ ≫ ψ)
      = mapShortComplexH1 f φ ≫ mapShortComplexH1 g ψ := rfl

noncomputable abbrev mapOneCocycles :
    ModuleCat.of k (oneCocycles A) ⟶ ModuleCat.of k (oneCocycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

noncomputable abbrev mapH1 : ModuleCat.of k (H1 A) ⟶ ModuleCat.of k (H1 B) :=
  ShortComplex.leftHomologyMap' (mapShortComplexH1 f φ)
    (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

@[simp]
theorem mapH1_id : mapH1 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  simp only [mapH1, shortComplexH1, mapShortComplexH1_id, leftHomologyMap'_id]
  rfl

theorem mapH1_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    mapH1 (f.comp g) ((Action.res _ g).map φ ≫ ψ) = mapH1 f φ ≫ mapH1 g ψ := by
  simpa [mapH1, shortComplexH1, mapShortComplexH1_comp] using leftHomologyMap'_comp _ _ _ _ _

@[simp]
lemma subtype_comp_mapOneCocycles :
    (oneCocycles B).subtype ∘ₗ mapOneCocycles f φ
      = fOne f φ ∘ₗ (oneCocycles A).subtype :=
  ShortComplex.cyclesMap'_i (mapShortComplexH1 f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[simp]
lemma H1π_comp_mapH1 :
    mapH1 f φ ∘ₗ H1π A = H1π B ∘ₗ mapOneCocycles f φ :=
  leftHomologyπ_naturality' (mapShortComplexH1 f φ) _ _

@[reassoc (attr := simp)]
lemma cocyclesMap_comp_isoOneCocycles_hom :
    cocyclesMap f φ 1 ≫ (isoOneCocycles B).hom
      = (isoOneCocycles A).hom ≫ mapOneCocycles f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapOneCocycles,
      Category.assoc, cyclesMap'_i, isoOneCocycles, ← Category.assoc]
  simp

@[reassoc (attr := simp)]
lemma cohomologyMap_comp_isoH1_hom :
    cohomologyMap f φ 1 ≫ (isoH1 B).hom = (isoH1 A).hom ≫ mapH1 f φ := by
  simpa [← cancel_epi (groupCohomologyπ _ _), mapH1, Category.assoc]
    using (leftHomologyπ_naturality' (mapShortComplexH1 f φ)
    (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm

@[simps]
def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := ModuleCat.asHom (fOne f φ)
  τ₂ := ModuleCat.asHom (fTwo f φ)
  τ₃ := ModuleCat.asHom (fThree f φ)
  comm₁₂ := by
    ext x
    funext g
    dsimp [shortComplexH2, dOne]
    simpa [moduleCat_simps, fOne, fTwo] using (hom_comm_apply φ _ _).symm
  comm₂₃ := by
    ext x
    funext g
    dsimp [shortComplexH2, dTwo]
    simpa [moduleCat_simps, fTwo, fThree] using (hom_comm_apply φ _ _).symm

@[simp]
theorem mapShortComplexH2_id :
    mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

theorem mapShortComplexH2_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    mapShortComplexH2 (f.comp g) ((Action.res _ g).map φ ≫ ψ)
      = mapShortComplexH2 f φ ≫ mapShortComplexH2 g ψ := rfl

noncomputable abbrev mapTwoCocycles :
    ModuleCat.of k (twoCocycles A) ⟶ ModuleCat.of k (twoCocycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

noncomputable abbrev mapH2 : ModuleCat.of k (H2 A) ⟶ ModuleCat.of k (H2 B) :=
  ShortComplex.leftHomologyMap' (mapShortComplexH2 f φ)
    (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

@[simp]
theorem mapH2_id : mapH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  simp only [mapH2, shortComplexH2, mapShortComplexH2_id, leftHomologyMap'_id]
  rfl

theorem mapH2_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    mapH2 (f.comp g) ((Action.res _ g).map φ ≫ ψ) = mapH2 f φ ≫ mapH2 g ψ := by
  simpa [mapH2, shortComplexH2, mapShortComplexH2_comp] using leftHomologyMap'_comp _ _ _ _ _

@[simp]
lemma subtype_comp_mapTwoCocycles :
    (twoCocycles B).subtype ∘ₗ mapTwoCocycles f φ
      = fTwo f φ ∘ₗ (twoCocycles A).subtype :=
  ShortComplex.cyclesMap'_i (mapShortComplexH2 f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[simp]
lemma H2π_comp_mapH2 :
    mapH2 f φ ∘ₗ H2π A = H2π B ∘ₗ mapTwoCocycles f φ :=
  leftHomologyπ_naturality' (mapShortComplexH2 f φ) _ _

@[reassoc (attr := simp)]
lemma cocyclesMap_comp_isoTwoCocycles_hom :
    cocyclesMap f φ 2 ≫ (isoTwoCocycles B).hom
      = (isoTwoCocycles A).hom ≫ mapTwoCocycles f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapTwoCocycles,
      Category.assoc, cyclesMap'_i, isoTwoCocycles, ← Category.assoc]
  simp

@[reassoc (attr := simp)]
lemma cohomologyMap_comp_isoH2_hom :
    cohomologyMap f φ 2 ≫ (isoH2 B).hom = (isoH2 A).hom ≫ mapH2 f φ := by
  simpa [← cancel_epi (groupCohomologyπ _ _), mapH2, Category.assoc]
    using (leftHomologyπ_naturality' (mapShortComplexH2 f φ)
    (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm

variable (k G) in
@[simps]
noncomputable def cochainsFunctor : Rep k G ⥤ CochainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousCochains A
  map f := cochainsMap (MonoidHom.id _) f
  map_id _ := cochainsMap_id
  map_comp φ ψ := cochainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

instance : (cochainsFunctor k G).PreservesZeroMorphisms where
instance : (cochainsFunctor k G).Additive where

variable (k G) in
@[simps]
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupCohomology A n
  map φ := cohomologyMap (MonoidHom.id _) φ n
  map_id _ := HomologicalComplex.homologyMap_id _ _
  map_comp _ _ := by
    simp only [← HomologicalComplex.homologyMap_comp]
    rfl

instance (n : ℕ) : (functor k G n).PreservesZeroMorphisms where
  map_zero _ _ := by simp [cohomologyMap]

open ShortComplex

variable {X : ShortComplex (Rep k G)} (C D : ChainComplex (Rep k G) ℕ) (f : C ⟶ D) [Epi f]

def mapShortExact (H : ShortExact X) :
    ShortExact (X.map (cochainsFunctor k G)) :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      have : LinearMap.range X.f.hom = LinearMap.ker X.g.hom :=
        (H.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      show LinearMap.range (LinearMap.compLeft X.f.hom (Fin i → G))
        = LinearMap.ker (LinearMap.compLeft X.g.hom (Fin i → G))
      rw [LinearMap.range_compLeft, LinearMap.ker_compLeft, this]
    mono_f := letI := H.2; cochainsMap_f_map_mono X.f i
    epi_g := letI := H.3; cochainsMap_f_map_epi X.g i }

/-- The short complex  `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)`-/
noncomputable abbrev cohomologyShortComplex₁
    (H : ShortExact X) {i j : ℕ} (hij : i + 1 = j) :=
  ShortComplex.mk _ _ ((mapShortExact H).δ_comp i j hij)

/-- The short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)`. -/
noncomputable abbrev cohomologyShortComplex₂ (H : ShortExact X) (i : ℕ) :=
  ShortComplex.mk (cohomologyMap (MonoidHom.id G) X.f i)
    (cohomologyMap (MonoidHom.id G) X.g i) <| by
      have : ((Action.res _ (MonoidHom.id G)).map X.f) ≫ X.g = 0 := X.zero
      simp [← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp, this]

/-- The short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
noncomputable abbrev cohomologyShortComplex₃ (H : ShortExact X) {i j : ℕ} (hij : i + 1 = j) :=
  ShortComplex.mk _ _ ((mapShortExact H).comp_δ i j hij)

/-- Exactness of `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)`. -/
lemma cohomology_exact₁ (H : ShortExact X) {i j : ℕ} (hij : i + 1 = j) :
    (cohomologyShortComplex₁ H hij).Exact :=
  (mapShortExact H).homology_exact₁ i j hij

/-- Exactness of `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)`. -/
lemma cohomology_exact₂ (H : ShortExact X) (i : ℕ) :
    (cohomologyShortComplex₂ H i).Exact :=
  (mapShortExact H).homology_exact₂ i

/--  Exactness of `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
lemma cohomology_exact₃ (H : ShortExact X) {i j : ℕ} (hij : i + 1 = j) :
    (cohomologyShortComplex₃ H hij).Exact :=
  (mapShortExact H).homology_exact₃ i j hij

theorem δ_apply_aux (H : ShortExact X) (n : ℕ) (y : (Fin n → G) → X.X₂)
    (x : (Fin (n + 1) → G) → X.X₁) (hx : X.f.hom ∘ x = inhomogeneousCochains.d X.X₂ n y) :
    inhomogeneousCochains.d X.X₁ (n + 1) x = 0 := by
  letI := H.2
  change (cochainsMap (MonoidHom.id G) _).f _ _ = _ at hx
  have := congr($((cochainsMap (MonoidHom.id G) X.f).comm (n + 1) (n + 2)) x)
  simp only [CochainComplex.of_x, inhomogeneousCochains.d_def, ModuleCat.coe_comp,
    Function.comp_apply] at this hx
  rw [hx] at this
  apply (ModuleCat.mono_iff_injective ((cochainsMap (MonoidHom.id G) X.f).f (n + 2))).1
  · infer_instance
  · simp only [CochainComplex.of_x, map_zero]
    exact this ▸ congr($(inhomogeneousCochains.d_comp_d X.X₂ n) y)

theorem δ_apply (H : ShortExact X) (n : ℕ)
    (z : (Fin n → G) → X.X₃) (hz : inhomogeneousCochains.d X.X₃ n z = 0)
    (y : (Fin n → G) → X.X₂) (hy : (cochainsMap (MonoidHom.id G) X.g).f n y = z)
    (x : (Fin (n + 1) → G) → X.X₁)
    (hx : X.f.hom ∘ x = inhomogeneousCochains.d X.X₂ n y) :
    (mapShortExact H).δ n (n + 1) rfl (groupCohomologyπ X.X₃ n <|
      (cocyclesIso X.X₃ n).inv ⟨z, hz⟩) = groupCohomologyπ X.X₁ (n + 1)
      ((cocyclesIso X.X₁ (n + 1)).inv ⟨x, δ_apply_aux H n y x hx⟩) := by
  simp_rw [cocyclesIso_inv_eq]
  exact ShortExact.δ_apply (mapShortExact H) n _ rfl z (by simpa using hz) y hy x
    (by simpa using hx) (n + 2) (by simp)

noncomputable def δ₀ (H : ShortExact X) :
    ModuleCat.of k (H0 X.X₃) ⟶ ModuleCat.of k (H1 X.X₁) :=
  (isoH0 X.X₃).inv ≫ (mapShortExact H).δ 0 1 rfl ≫ (isoH1 X.X₁).hom

theorem δ₀_apply_aux (H : ShortExact X) (y : X.X₂) (x : G → X.X₁)
    (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    dOne X.X₁ x = 0 := by
  have h0 := δ_apply_aux H 0 ((zeroCochainsLEquiv X.X₂).symm y) ((oneCochainsLEquiv X.X₁).symm x)
  have hy := congr($((CommSq.horiz_inv ⟨(shortComplexH1Iso X.X₂).hom.comm₁₂⟩).w) y)
  have h := congr($((Iso.eq_inv_comp _).2 (shortComplexH1Iso X.X₁).hom.comm₂₃) x)
  simp only [ModuleCat.coe_comp, Function.comp_apply] at h0 hy
  exact h.trans <| (twoCochainsLEquiv X.X₁).map_eq_zero_iff.2 <| h0 (hy.trans <| hx ▸ rfl).symm

theorem δ₀_apply (H : ShortExact X)
    (z : X.X₃) (hz : z ∈ X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : G → X.X₁) (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    δ₀ H ⟨z, hz⟩ = H1π X.X₁ ⟨x, δ₀_apply_aux H y x hx⟩ := by
  have h0z : (inhomogeneousCochains.d X.X₃ 0) ((zeroCochainsLEquiv X.X₃).symm z) = 0 := by
    have := congr($((LinearEquiv.symm_comp_eq_comp_symm_iff _ _).2 (dZero_comp_eq X.X₃)) z)
    simp_all [← dZero_ker_eq_invariants, ModuleCat.coe_of]
  have hxy : X.f.hom ∘ (oneCochainsLEquiv X.X₁).symm x = inhomogeneousCochains.d X.X₂ 0
      ((zeroCochainsLEquiv X.X₂).symm y) := by
    have := (congr($((LinearEquiv.symm_comp_eq_comp_symm_iff _ _).2 (dZero_comp_eq X.X₂)) y)).symm
    ext i
    simp_all only [CochainComplex.of_x, ModuleCat.coe_of,
      inhomogeneousCochains.d_def, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    simp [← hx, oneCochainsLEquiv]
  have := congr((isoH1 X.X₁).hom $(δ_apply H 0 ((zeroCochainsLEquiv X.X₃).symm z) h0z
    ((zeroCochainsLEquiv X.X₂).symm y) (hy ▸ rfl) ((oneCochainsLEquiv X.X₁).symm x) hxy))
  convert this
  · exact cocyclesIso_0_eq X.X₃ ▸ rfl
  · have := LinearMap.ext_iff.1 ((Iso.inv_comp_eq _).2 (groupCohomologyπ_comp_isoH1_hom X.X₁))
    simp_all only [cocyclesIso_1_eq X.X₁, Iso.trans_inv, ModuleCat.hom_def,
      ModuleCat.coe_of, LinearEquiv.toModuleIso_inv, ModuleCat.comp_def, LinearMap.coe_comp,
      Function.comp_apply]
    rfl

open Limits

theorem epi_δ₀ (X : ShortComplex (Rep k G)) (H : ShortExact X)
    (h1 : IsZero (ModuleCat.of k <| H1 X.X₂)) : Epi (δ₀ H) := by
  letI : Epi ((mapShortExact H).δ 0 1 rfl) := (mapShortExact H).epi_δ _ _ rfl
    (h1.of_iso (isoH1 X.X₂))
  exact epi_comp _ _

noncomputable def δ₁ {X : ShortComplex (Rep k G)} (H : ShortExact X) :
    ModuleCat.of k (H1 X.X₃) ⟶ ModuleCat.of k (H2 X.X₁) :=
  (isoH1 X.X₃).inv ≫ (mapShortExact H).δ 1 2 rfl ≫ (isoH2 X.X₁).hom

theorem δ₁_apply_aux {X : ShortComplex (Rep k G)} (H : ShortExact X) (y : G → X.X₂)
    (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    dTwo X.X₁ x = 0 := by
  have h1 := δ_apply_aux H 1 ((oneCochainsLEquiv X.X₂).symm y) ((twoCochainsLEquiv X.X₁).symm x)
  have hy := congr($((CommSq.horiz_inv ⟨(shortComplexH2Iso X.X₂).hom.comm₁₂⟩).w) y)
  have h := congr($((Iso.eq_inv_comp _).2 (shortComplexH2Iso X.X₁).hom.comm₂₃) x)
  simp only [ModuleCat.coe_comp, Function.comp_apply] at h1 hy
  exact h.trans <| (threeCochainsLEquiv X.X₁).map_eq_zero_iff.2 <| h1 (hy.trans <| hx ▸ rfl).symm

theorem δ₁_apply (X : ShortComplex (Rep k G)) (H : ShortExact X)
    (z : G → X.X₃) (hz : z ∈ oneCocycles X.X₃) (y : G → X.X₂) (hy : X.g.hom ∘ y = z)
    (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    δ₁ H (H1π X.X₃ ⟨z, hz⟩) = H2π X.X₁ ⟨x, δ₁_apply_aux H y x hx⟩ := by
  have h1z : (inhomogeneousCochains.d X.X₃ 1) ((oneCochainsLEquiv X.X₃).symm z) = 0 := by
    have := congr($((LinearEquiv.symm_comp_eq_comp_symm_iff _ _).2 (dOne_comp_eq X.X₃)) z)
    simp_all [ModuleCat.coe_of, oneCocycles]
  have hxy : X.f.hom ∘ (twoCochainsLEquiv X.X₁).symm x
      = inhomogeneousCochains.d X.X₂ 1 ((oneCochainsLEquiv X.X₂).symm y) := by
    have := (congr($((LinearEquiv.symm_comp_eq_comp_symm_iff _ _).2 (dOne_comp_eq X.X₂)) y)).symm
    ext i
    simp_all only [CochainComplex.of_x, ModuleCat.coe_of,
      inhomogeneousCochains.d_def, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    simp [← hx, twoCochainsLEquiv]
  have := congr((isoH2 X.X₁).hom $(δ_apply H 1 ((oneCochainsLEquiv X.X₃).symm z) h1z
    ((oneCochainsLEquiv X.X₂).symm y) (hy ▸ rfl) ((twoCochainsLEquiv X.X₁).symm x) hxy))
  convert this
  · have := congr($((CommSq.vert_inv ⟨groupCohomologyπ_comp_isoH1_hom X.X₃⟩).w) ⟨z, hz⟩)
    rw [cocyclesIso_1_eq]
    exact this ▸ rfl
  · have := LinearMap.ext_iff.1 ((Iso.inv_comp_eq _).2 (groupCohomologyπ_comp_isoH2_hom X.X₁))
    simp_all only [cocyclesIso_2_eq X.X₁, Iso.trans_inv, ModuleCat.hom_def,
      ModuleCat.coe_of, LinearEquiv.toModuleIso_inv, ModuleCat.comp_def, LinearMap.coe_comp,
      Function.comp_apply]
    rfl

theorem epi_δ₁ (X : ShortComplex (Rep k G)) (H : ShortExact X)
    (h2 : IsZero (ModuleCat.of k <| H2 X.X₂)) : Epi (δ₁ H) := by
  letI : Epi ((mapShortExact H).δ 1 2 rfl) := (mapShortExact H).epi_δ _ _ rfl
    (h2.of_iso (isoH2 X.X₂))
  exact epi_comp _ _

/-- The short complex `X₁ᴳ ⟶ X₂ᴳ ⟶ X₃ᴳ`. -/
noncomputable abbrev H0ShortComplex₂ (H : ShortExact X) :=
  ShortComplex.mk (mapH0 (MonoidHom.id G) X.f) (mapH0 (MonoidHom.id G) X.g) <| by
    ext x; apply Subtype.ext; exact congr(Action.Hom.hom $(X.zero) x.1)

noncomputable def isoH0ShortComplex₂ (H : ShortExact X) :
    cohomologyShortComplex₂ H 0 ≅ H0ShortComplex₂ H :=
  isoMk (isoH0 _) (isoH0 _) (isoH0 _) (cohomologyMap_comp_isoH0_hom (MonoidHom.id G) _).symm
    (cohomologyMap_comp_isoH0_hom (MonoidHom.id G) _).symm

theorem H0ShortComplex₂_exact (H : ShortExact X) :
    (H0ShortComplex₂ H).Exact :=
  exact_of_iso (isoH0ShortComplex₂ H) (cohomology_exact₂ _ _)

/-- The short complex `X₂ᴳ ⟶ X₃ᴳ ⟶ H¹(G, X₁)`. -/
noncomputable abbrev H0ShortComplex₃ (H : ShortExact X) :=
  ShortComplex.mk (mapH0 (MonoidHom.id G) X.g) (δ₀ H) <| by
    rw [δ₀, ← Category.assoc, (CommSq.vert_inv ⟨cohomologyMap_comp_isoH0_hom
      (MonoidHom.id G) X.g⟩).w]
    simpa using (mapShortExact H).comp_δ_assoc 0 1 rfl _

noncomputable def isoH0ShortComplex₃ (H : ShortExact X) :
    cohomologyShortComplex₃ H (j := 1) rfl ≅ H0ShortComplex₃ H :=
  isoMk (isoH0 _) (isoH0 _) (isoH1 _)
    (cohomologyMap_comp_isoH0_hom (MonoidHom.id G) _).symm (by simp [δ₀])

theorem H0ShortComplex₃_exact (H : ShortExact X) :
    (H0ShortComplex₃ H).Exact :=
  exact_of_iso (isoH0ShortComplex₃ H) (cohomology_exact₃ _ _)

/-- The short complex  `X₃ᴳ ⟶ H¹(G, X₁) ⟶ H¹(G, X₂)`-/
noncomputable abbrev H1ShortComplex₁ (H : ShortExact X) :=
  ShortComplex.mk (δ₀ H) (mapH1 (MonoidHom.id G) X.f) <| by
    simpa [δ₀, ModuleCat.asHom, ← cohomologyMap_comp_isoH1_hom]
      using (mapShortExact H).δ_comp_assoc 0 1 rfl _

noncomputable def isoH1ShortComplex₁ (H : ShortExact X) :
    cohomologyShortComplex₁ H (i := 0) rfl ≅ H1ShortComplex₁ H :=
  isoMk (isoH0 _) (isoH1 _) (isoH1 _) (by simp [δ₀])
    (cohomologyMap_comp_isoH1_hom (MonoidHom.id G) _).symm

theorem H1ShortComplex₁_exact (H : ShortExact X) :
    (H1ShortComplex₁ H).Exact :=
  exact_of_iso (isoH1ShortComplex₁ H) (cohomology_exact₁ _ _)

/-- The short complex `H¹(G, X₁) ⟶ H¹(G, X₂) ⟶ H¹(G, X₃)`. -/
noncomputable abbrev H1ShortComplex₂ (H : ShortExact X) :=
  ShortComplex.mk (mapH1 (MonoidHom.id G) X.f)
    (mapH1 (MonoidHom.id G) X.g) <| by
      suffices mapH1 (MonoidHom.id G) (X.f ≫ X.g) = 0 by
        rw [← mapH1_comp]
        exact this
      rw [X.zero]
      exact leftHomologyMap'_zero _ _

noncomputable def isoH1ShortComplex₂ (H : ShortExact X) :
    cohomologyShortComplex₂ H 1 ≅ H1ShortComplex₂ H :=
  isoMk (isoH1 _) (isoH1 _) (isoH1 _) (cohomologyMap_comp_isoH1_hom (MonoidHom.id G) _).symm
    (cohomologyMap_comp_isoH1_hom (MonoidHom.id G) _).symm

theorem H1ShortComplex₂_exact (H : ShortExact X) :
    (H1ShortComplex₂ H).Exact :=
  exact_of_iso (isoH1ShortComplex₂ H) (cohomology_exact₂ _ _)

/-- The short complex `H¹(G, X₂) ⟶ H¹(G, X₃) ⟶ H²(G, X₁)`. -/
noncomputable abbrev H1ShortComplex₃ (H : ShortExact X) :=
  ShortComplex.mk (mapH1 (MonoidHom.id G) X.g) (δ₁ H) <| by
    rw [δ₁, ← Category.assoc, (CommSq.vert_inv ⟨cohomologyMap_comp_isoH1_hom
      (MonoidHom.id G) X.g⟩).w]
    simpa using (mapShortExact H).comp_δ_assoc 1 2 rfl _

noncomputable def isoH1ShortComplex₃ (H : ShortExact X) :
    cohomologyShortComplex₃ H (i := 1) rfl ≅ H1ShortComplex₃ H :=
  isoMk (isoH1 _) (isoH1 _) (isoH2 _)
    (cohomologyMap_comp_isoH1_hom (MonoidHom.id G) _).symm (by simp [δ₁])

theorem H1ShortComplex₃_exact (H : ShortExact X) :
    (H1ShortComplex₃ H).Exact :=
  exact_of_iso (isoH1ShortComplex₃ H) (cohomology_exact₃ _ _)

/-- The short complex  `H¹(G, X₃) ⟶ H²(G, X₁) ⟶ H²(G, X₂)`-/
noncomputable abbrev H2ShortComplex₁ (H : ShortExact X) :=
  ShortComplex.mk (δ₁ H) (mapH2 (MonoidHom.id G) X.f) <| by
    simpa [δ₁, ModuleCat.asHom, ← cohomologyMap_comp_isoH2_hom]
      using (mapShortExact H).δ_comp_assoc 1 2 rfl _

noncomputable def isoH2ShortComplex₁ (H : ShortExact X) :
    cohomologyShortComplex₁ H (i := 1) rfl ≅ H2ShortComplex₁ H :=
  isoMk (isoH1 _) (isoH2 _) (isoH2 _) (by simp [δ₁])
    (cohomologyMap_comp_isoH2_hom (MonoidHom.id G) _).symm

theorem H2ShortComplex₁_exact (H : ShortExact X) :
    (H2ShortComplex₁ H).Exact :=
  exact_of_iso (isoH2ShortComplex₁ H) (cohomology_exact₁ _ _)

end groupCohomology
