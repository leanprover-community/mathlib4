import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
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

lemma ofHom_comp {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    ofHom (g ∘ₗ f) = ofHom f ≫ ofHom g := rfl

end ModuleCat

namespace groupCohomology
open Rep

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  (A : Rep k H) (B : Rep k G) (f : G →* H) (φ : A →ₗ[k] B) (n : ℕ)

class IsPairMap : Prop where
  compatible : ∀ (g : G), φ ∘ₗ A.ρ (f g) = B.ρ g ∘ₗ φ

namespace IsPairMap
open Representation

variable {A B f φ} (S : Subgroup G)

lemma compatible_apply [IsPairMap A B f φ] (g : G) (x : A) :
    φ (A.ρ (f g) x) = B.ρ g (φ x) :=
  congr($(compatible g) x)

instance comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    (A : Rep k K) (B : Rep k H) (C : Rep k G) (f : H →* K) (g : G →* H) (φ : A →ₗ[k] B)
    (ψ : B →ₗ[k] C) [IsPairMap A B f φ] [IsPairMap B C g ψ] :
    IsPairMap A C (f.comp g) (ψ.comp φ) where
  compatible x := by
    ext y
    have := congr($(compatible (A := A) (B := B) (f := f) (φ := φ) (g x)) y)
    have := congr($(compatible (A := B) (B := C) (f := g) (φ := ψ) x) (φ y))
    simp_all

instance instInf [S.Normal] : IsPairMap (Rep.inf B S) B (QuotientGroup.mk' S)
    (invariants (B.ρ.comp S.subtype)).subtype where
  compatible := by intros; rfl

instance instRes : IsPairMap A ((Action.res _ f).obj A) f LinearMap.id where
  compatible := by intros; rfl

instance instHom {A B : Rep k G} (f : A ⟶ B) : IsPairMap A B (MonoidHom.id G) f.hom where
  compatible := f.comm

variable [IsPairMap A B f φ]

variable (A B f φ) in
@[simps (config := .lemmasOnly)]
noncomputable def cochainsMap :
    inhomogeneousCochains A ⟶ inhomogeneousCochains B where
  f i := ModuleCat.ofHom (φ.compLeft (Fin i → G)
    ∘ₗ LinearMap.funLeft k A (fun x : Fin i → G => (f ∘ x)))
  comm' i j (hij : _ = _) := by
    subst hij
    ext x
    funext g
    simp only [CochainComplex.of_x, inhomogeneousCochains.d_def, ModuleCat.coe_comp,
      Function.comp_apply]
    simpa [ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, Fin.comp_contractNth]
      using (compatible_apply _ _).symm

@[simp]
lemma cochainsMap_f_apply (n : ℕ) (x : (inhomogeneousCochains A).X n) (g : Fin n → G) :
    (cochainsMap A B f φ).f n x g = φ (x (f ∘ g)) :=
  rfl

@[simp]
lemma cochainsMap_id :
    cochainsMap A A (MonoidHom.id _) (Action.Hom.hom <| 𝟙 A) = 𝟙 (inhomogeneousCochains A) := by
  rfl

lemma cochainsMap_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    (A : Rep k K) (B : Rep k H) (C : Rep k G) (f : H →* K) (g : G →* H) (φ : A →ₗ[k] B)
    (ψ : B →ₗ[k] C) [IsPairMap A B f φ] [IsPairMap B C g ψ] :
    cochainsMap A C (f.comp g) (ψ ∘ₗ φ) = (cochainsMap A B f φ) ≫ (cochainsMap B C g ψ) := by
  rfl

instance cochainsMap_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : ℕ) :
    Mono ((cochainsMap A B (MonoidHom.id G) φ.hom).f i) :=
  (ModuleCat.mono_iff_injective _).2 <| Function.Injective.comp_left <|
    (ModuleCat.mono_iff_injective φ.hom).1 <| (forget₂ (Rep k G) (ModuleCat k)).map_mono φ

instance cochainsMap_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : ℕ) :
    Epi ((cochainsMap A B (MonoidHom.id G) φ.hom).f i) :=
  (ModuleCat.epi_iff_surjective _).2 <| Function.Surjective.comp_left <|
    (ModuleCat.epi_iff_surjective φ.hom).1 <| (forget₂ (Rep k G) (ModuleCat k)).map_epi φ

variable (A B f φ)
noncomputable abbrev cocyclesMap (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology.cocycles B n :=
  HomologicalComplex.cyclesMap (cochainsMap A B f φ) n

noncomputable abbrev cohomologyMap (n : ℕ) :
  groupCohomology A n ⟶ groupCohomology B n :=
HomologicalComplex.homologyMap (cochainsMap A B f φ) n

abbrev fOne := φ.compLeft G ∘ₗ LinearMap.funLeft k A f
abbrev fTwo := φ.compLeft (G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f f)
abbrev fThree := φ.compLeft (G × G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f (Prod.map f f))

@[reassoc (attr := simp)]
lemma cochainsMap_f_0_comp_zeroCochainsLEquiv :
    (cochainsMap A B f φ).f 0 ≫ (zeroCochainsLEquiv B : (inhomogeneousCochains B).X 0 →ₗ[k] B)
      = (zeroCochainsLEquiv A : (inhomogeneousCochains A).X 0 →ₗ[k] A) ≫ ModuleCat.ofHom φ := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_1_comp_oneCochainsLEquiv :
    (cochainsMap A B f φ).f 1 ≫ (oneCochainsLEquiv B : (inhomogeneousCochains B).X 1 →ₗ[k] G → B)
      = (oneCochainsLEquiv A).toModuleIso.hom
      ≫ ModuleCat.ofHom (fOne A B f φ) := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_2_comp_twoCochainsLEquiv :
    (cochainsMap A B f φ).f 2
      ≫ (twoCochainsLEquiv B : (inhomogeneousCochains B).X 2 →ₗ[k] G × G → B)
      = (twoCochainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fTwo A B f φ) := by
  ext x
  funext g
  show φ (x _) = φ (x _)
  rcongr x
  fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_3_comp_threeCochainsLEquiv :
    (cochainsMap A B f φ).f 3
      ≫ (threeCochainsLEquiv B : (inhomogeneousCochains B).X 3 →ₗ[k] G × G × G → B)
      = (threeCochainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fThree A B f φ) := by
  ext x
  funext g
  show φ (x _) = φ (x _)
  rcongr x
  fin_cases x <;> rfl

open ShortComplex

def mapH0 : H0 A →ₗ[k] H0 B :=
  LinearMap.codRestrict _ (φ ∘ₗ A.ρ.invariants.subtype) fun ⟨c, hc⟩ g => by
    simp [← compatible_apply (f := f) g c, hc (f g)]

@[simps]
def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := ModuleCat.ofHom φ
  τ₂ := ModuleCat.ofHom (fOne A B f φ)
  τ₃ := ModuleCat.ofHom (fTwo A B f φ)
  comm₁₂ := by
    ext x
    funext g
    dsimp [shortComplexH1, dZero]
    simp [ModuleCat.coe_of, ModuleCat.hom_def, compatible_apply]
  comm₂₃ := by
    ext x
    funext g
    dsimp [shortComplexH1, dOne]
    simp [ModuleCat.coe_of, ModuleCat.hom_def, compatible_apply]

noncomputable abbrev mapOneCocycles :
    oneCocycles A →ₗ[k] oneCocycles B :=
  ShortComplex.cyclesMap' (mapShortComplexH1 A B f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

noncomputable abbrev mapH1 : H1 A →ₗ[k] H1 B :=
  ShortComplex.leftHomologyMap' (mapShortComplexH1 A B f φ)
    (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

@[simp]
lemma subtype_comp_mapOneCocycles :
    (oneCocycles B).subtype ∘ₗ mapOneCocycles A B f φ
      = fOne A B f φ ∘ₗ (oneCocycles A).subtype :=
  ShortComplex.cyclesMap'_i (mapShortComplexH1 A B f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[simp]
lemma H1π_comp_mapH1 :
    mapH1 A B f φ ∘ₗ H1π A = H1π B ∘ₗ mapOneCocycles A B f φ :=
  leftHomologyπ_naturality' (mapShortComplexH1 A B f φ) _ _

@[reassoc (attr := simp)]
lemma cocyclesMap_comp_isoOneCocycles_hom :
    cocyclesMap A B f φ 1 ≫ (isoOneCocycles B).hom
      = (isoOneCocycles A).hom ≫ mapOneCocycles A B f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapOneCocycles,
      Category.assoc, cyclesMap'_i, isoOneCocycles, ← Category.assoc]
  simp

@[reassoc (attr := simp)]
lemma cohomologyMap_comp_isoH1_hom :
    cohomologyMap A B f φ 1 ≫ (isoH1 B).hom = (isoH1 A).hom ≫ mapH1 A B f φ := by
  simpa [← cancel_epi (groupCohomologyπ _ _), mapH1, Category.assoc]
    using (leftHomologyπ_naturality' (mapShortComplexH1 A B f φ)
    (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm

@[simps]
def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := ModuleCat.ofHom (fOne A B f φ)
  τ₂ := ModuleCat.ofHom (fTwo A B f φ)
  τ₃ := ModuleCat.ofHom (fThree A B f φ)
  comm₁₂ := by
    ext x
    funext g
    dsimp [shortComplexH2, dOne]
    simp [ModuleCat.coe_of, ModuleCat.hom_def, compatible_apply]
  comm₂₃ := by
    ext x
    funext g
    dsimp [shortComplexH2, dTwo]
    simp [ModuleCat.coe_of, ModuleCat.hom_def, compatible_apply]

noncomputable abbrev mapTwoCocycles :
    twoCocycles A →ₗ[k] twoCocycles B :=
  ShortComplex.cyclesMap' (mapShortComplexH2 A B f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

noncomputable abbrev mapH2 : H2 A →ₗ[k] H2 B :=
  ShortComplex.leftHomologyMap' (mapShortComplexH2 A B f φ)
    (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

@[simp]
lemma subtype_comp_mapTwoCocycles :
    (twoCocycles B).subtype ∘ₗ mapTwoCocycles A B f φ
      = fTwo A B f φ ∘ₗ (twoCocycles A).subtype :=
  ShortComplex.cyclesMap'_i (mapShortComplexH2 A B f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[simp]
lemma H2π_comp_mapH2 :
    mapH2 A B f φ ∘ₗ H2π A = H2π B ∘ₗ mapTwoCocycles A B f φ :=
  leftHomologyπ_naturality' (mapShortComplexH2 A B f φ) _ _

@[reassoc (attr := simp)]
lemma cocyclesMap_comp_isoTwoCocycles_hom :
    cocyclesMap A B f φ 2 ≫ (isoTwoCocycles B).hom
      = (isoTwoCocycles A).hom ≫ mapTwoCocycles A B f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapTwoCocycles,
      Category.assoc, cyclesMap'_i, isoTwoCocycles, ← Category.assoc]
  simp

@[reassoc (attr := simp)]
lemma cohomologyMap_comp_isoH2_hom :
    cohomologyMap A B f φ 2 ≫ (isoH2 B).hom = (isoH2 A).hom ≫ mapH2 A B f φ := by
  simpa [← cancel_epi (groupCohomologyπ _ _), mapH2, Category.assoc]
    using (leftHomologyπ_naturality' (mapShortComplexH2 A B f φ)
    (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm

end IsPairMap

open IsPairMap

variable (k G) in
@[simps]
noncomputable def cochainsFunctor : Rep k G ⥤ CochainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousCochains A
  map f := cochainsMap _ _ (MonoidHom.id _) f.hom
  map_id _ := cochainsMap_id
  map_comp {X Y Z} φ ψ := cochainsMap_comp X Y Z (MonoidHom.id G) (MonoidHom.id G) φ.hom ψ.hom

instance : (cochainsFunctor k G).PreservesZeroMorphisms where
instance : (cochainsFunctor k G).Additive where

variable (k G) in
@[simps]
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupCohomology A n
  map {A B} φ :=
    letI : IsPairMap A B (MonoidHom.id _) φ.hom := instHom φ
    cohomologyMap A B (MonoidHom.id _) φ.hom n
  map_id A := HomologicalComplex.homologyMap_id _ _
  map_comp f g := by
    simp only [← HomologicalComplex.homologyMap_comp]
    rfl

open ShortComplex

def mapShortExact (X : ShortComplex (Rep k G)) (H : ShortExact X) :
    ShortExact ((cochainsFunctor k G).mapShortComplex.obj X) :=
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

theorem lol_aux {X : ShortComplex (Rep k G)} (H : ShortExact X) (n : ℕ)
    (y : (Fin n → G) → X.X₂) (x : (Fin (n + 1) → G) → X.X₁)
    (hx : X.f.hom ∘ x = inhomogeneousCochains.d X.X₂ n y) :
    inhomogeneousCochains.d X.X₁ (n + 1) x = 0 := by
  letI := H.2
  change (cochainsMap X.X₁ X.X₂ (MonoidHom.id G) _).f _ _ = _ at hx
  have := congr($((cochainsMap X.X₁ X.X₂ (MonoidHom.id G) X.f.hom).comm (n + 1) (n + 2)) x)
  simp only [CochainComplex.of_x, inhomogeneousCochains.d_def, ModuleCat.coe_comp,
    Function.comp_apply] at this hx
  rw [hx] at this
  apply (ModuleCat.mono_iff_injective ((cochainsMap X.X₁ X.X₂
    (MonoidHom.id G) X.f.hom).f (n + 2))).1
  · infer_instance
  · simp only [CochainComplex.of_x, map_zero]
    exact this ▸ congr($(inhomogeneousCochains.d_comp_d X.X₂ n) y)

theorem lol (X : ShortComplex (Rep k G)) (H : ShortExact X) (n : ℕ)
    (z : (Fin n → G) → X.X₃) (hz : inhomogeneousCochains.d X.X₃ n z = 0)
    (y : (Fin n → G) → X.X₂) (hy : (cochainsMap X.X₂ X.X₃ (MonoidHom.id G) X.g.hom).f n y = z)
    (x : (Fin (n + 1) → G) → X.X₁) (hx : X.f.hom ∘ x = inhomogeneousCochains.d X.X₂ n y) :
    (mapShortExact X H).δ n (n + 1) rfl (groupCohomologyπ X.X₃ n <|
      (cocyclesIso X.X₃ n).inv ⟨z, hz⟩) = groupCohomologyπ X.X₁ (n + 1)
      ((cocyclesIso X.X₁ (n + 1)).inv ⟨x, lol_aux H n y x hx⟩) := by
  have lol' := ShortExact.δ_apply (C := ModuleCat k)
    (mapShortExact X H) n (n + 1) rfl z ?_ y hy x ?_ (n + 2) (by simp)
  convert lol'
  all_goals sorry

end groupCohomology
