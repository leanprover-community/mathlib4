import Mathlib.CategoryTheory.Grothendieck
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

namespace ModuleCat

variable (R : Type u) [Ring R]

lemma ofHom_comp {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    ofHom (g ∘ₗ f) = ofHom f ≫ ofHom g := rfl

end ModuleCat

namespace groupCohomology
open Rep

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  (A : Rep k G) (B : Rep k H) (f : G →* H) (φ : B →ₗ[k] A) (n : ℕ)

class IsPairMap : Prop where
  compatible : ∀ (g : G), φ ∘ₗ B.ρ (f g) = A.ρ g ∘ₗ φ

namespace IsPairMap
open Representation

variable {A B f φ} (S : Subgroup G)

lemma compatible_apply [IsPairMap A B f φ] (g : G) (x : B) :
    φ (B.ρ (f g) x) = A.ρ g (φ x) :=
  congr($(compatible g) x)

instance comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    (A : Rep k G) (B : Rep k H) (C : Rep k K) (f : G →* H) (g : H →* K) (φ : B →ₗ[k] A)
    (ψ : C →ₗ[k] B) [IsPairMap A B f φ] [IsPairMap B C g ψ] :
    IsPairMap A C (g.comp f) (φ.comp ψ) where
  compatible x := by
    ext y
    have := congr($(compatible (A := A) (B := B) (f := f) (φ := φ) x) (ψ y))
    have := congr($(compatible (A := B) (B := C) (f := g) (φ := ψ) (f x)) y)
    simp_all

instance instInf [S.Normal] : IsPairMap A (inf A S) (QuotientGroup.mk' S)
    (invariants (A.ρ.comp S.subtype)).subtype where
  compatible := by intros; rfl

instance instRes : IsPairMap ((Action.res _ f).obj B) B f LinearMap.id where
  compatible := by intros; rfl

instance instHom {A B : Rep k G} (f : A ⟶ B) : IsPairMap B A (MonoidHom.id G) f.hom where
  compatible := f.comm

variable [IsPairMap A B f φ]

variable (A B f φ) in
@[simps (config := .lemmasOnly)]
noncomputable def cochainsMap :
    inhomogeneousCochains B ⟶ inhomogeneousCochains A where
  f i := ModuleCat.ofHom (φ.compLeft (Fin i → G)
    ∘ₗ LinearMap.funLeft k B (fun x : Fin i → G => (f ∘ x)))
  comm' i j (hij : _ = _) := by
    subst hij
    ext x
    funext g
    simp only [CochainComplex.of_x, inhomogeneousCochains.d_def, ModuleCat.coe_comp,
      Function.comp_apply]
    simpa [ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, Fin.comp_contractNth]
      using (compatible_apply _ _).symm

@[simp]
lemma cochainsMap_f_apply (n : ℕ) (x : (inhomogeneousCochains B).X n) (g : Fin n → G) :
    (cochainsMap A B f φ).f n x g = φ (x (f ∘ g)) :=
  rfl

lemma cochainsMap_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    (A : Rep k G) (B : Rep k H) (C : Rep k K) (f : G →* H) (g : H →* K) (φ : B →ₗ[k] A)
    (ψ : C →ₗ[k] B) [IsPairMap A B f φ] [IsPairMap B C g ψ] :
    cochainsMap A C (g.comp f) (φ.comp ψ) = (cochainsMap B C g ψ) ≫ (cochainsMap A B f φ) := by
  rfl

variable (A B f φ)
noncomputable abbrev cocyclesMap (n : ℕ) :
    groupCohomology.cocycles B n ⟶ groupCohomology.cocycles A n :=
  HomologicalComplex.cyclesMap (cochainsMap A B f φ) n

noncomputable abbrev cohomologyMap (n : ℕ) :
  groupCohomology B n ⟶ groupCohomology A n :=
HomologicalComplex.homologyMap (cochainsMap A B f φ) n

@[simps]
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupCohomology A n
  map {A B} φ :=
    letI : IsPairMap B A (MonoidHom.id _) φ.hom := instHom φ
    cohomologyMap B A (MonoidHom.id _) φ.hom n
  map_id A := HomologicalComplex.homologyMap_id _ _
  map_comp f g := by
    simp only [← HomologicalComplex.homologyMap_comp]
    rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_0_comp_zeroCochainsLequiv :
    (cochainsMap A B f φ).f 0 ≫ (zeroCochainsLequiv A : (inhomogeneousCochains A).X 0 →ₗ[k] A)
      = (zeroCochainsLequiv B : (inhomogeneousCochains B).X 0 →ₗ[k] B) ≫ ModuleCat.ofHom φ := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_1_comp_oneCochainsLequiv :
    (cochainsMap A B f φ).f 1 ≫ (oneCochainsLequiv A : (inhomogeneousCochains A).X 1 →ₗ[k] G → A)
      = (oneCochainsLequiv B).toModuleIso.hom
      ≫ ModuleCat.ofHom (φ.compLeft G ∘ₗ LinearMap.funLeft k B f) := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_2_comp_twoCochainsLequiv :
    (cochainsMap A B f φ).f 2
      ≫ (twoCochainsLequiv A : (inhomogeneousCochains A).X 2 →ₗ[k] G × G → A)
      = (twoCochainsLequiv B).toModuleIso.hom
      ≫ ModuleCat.ofHom (φ.compLeft (G × G) ∘ₗ LinearMap.funLeft k B (Prod.map f f)) := by
  ext x
  funext g
  show φ (x _) = φ (x _)
  rcongr x
  fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_3_comp_threeCochainsLequiv :
    (cochainsMap A B f φ).f 3
      ≫ (threeCochainsLequiv A : (inhomogeneousCochains A).X 3 →ₗ[k] G × G × G → A)
      = (threeCochainsLequiv B).toModuleIso.hom
      ≫ ModuleCat.ofHom (φ.compLeft (G × G × G)
        ∘ₗ LinearMap.funLeft k B (Prod.map f (Prod.map f f))) := by
  ext x
  funext g
  show φ (x _) = φ (x _)
  rcongr x
  fin_cases x <;> rfl

open ShortComplex

def mapH0 : H0 B →ₗ[k] H0 A :=
  LinearMap.codRestrict _ (φ ∘ₗ B.ρ.invariants.subtype) fun ⟨c, hc⟩ g => by
    simp [← compatible_apply (f := f) g c, hc (f g)]

@[simps]
def mapShortComplexH1 :
    shortComplexH1 B ⟶ shortComplexH1 A where
  τ₁ := ModuleCat.ofHom φ
  τ₂ := ModuleCat.ofHom (φ.compLeft G ∘ₗ LinearMap.funLeft k B f)
  τ₃ := ModuleCat.ofHom (φ.compLeft (G × G) ∘ₗ LinearMap.funLeft k B (Prod.map f f))
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
    oneCocycles B →ₗ[k] oneCocycles A :=
  ShortComplex.cyclesMap' (mapShortComplexH1 A B f φ) (shortComplexH1 B).moduleCatLeftHomologyData
    (shortComplexH1 A).moduleCatLeftHomologyData

noncomputable abbrev mapH1 : H1 B →ₗ[k] H1 A :=
  ShortComplex.leftHomologyMap' (mapShortComplexH1 A B f φ)
    (shortComplexH1 B).moduleCatLeftHomologyData
    (shortComplexH1 A).moduleCatLeftHomologyData

@[simp]
lemma H1π_comp_mapH1 :
    mapH1 A B f φ ∘ₗ H1π B = H1π A ∘ₗ mapOneCocycles A B f φ :=
  leftHomologyπ_naturality' (mapShortComplexH1 A B f φ) _ _

@[reassoc (attr := simp)]
lemma cocyclesMap_comp_isoOneCocycles_hom :
    cocyclesMap A B f φ 1 ≫ (isoOneCocycles A).hom
      = (isoOneCocycles B).hom ≫ mapOneCocycles A B f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 A)).i, mapOneCocycles,
      Category.assoc, cyclesMap'_i, isoOneCocycles, ← Category.assoc]
  simp

@[reassoc (attr := simp)]
lemma cohomologyMap_comp_isoH1_hom :
    cohomologyMap A B f φ 1 ≫ (isoH1 A).hom = (isoH1 B).hom ≫ mapH1 A B f φ := by
  simpa [← cancel_epi (groupCohomologyπ _ _), mapH1, Category.assoc]
    using (leftHomologyπ_naturality' (mapShortComplexH1 A B f φ)
    (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm

@[simps]
def mapShortComplexH2 :
    shortComplexH2 B ⟶ shortComplexH2 A where
  τ₁ := ModuleCat.ofHom (φ.compLeft G ∘ₗ LinearMap.funLeft k B f)
  τ₂ := ModuleCat.ofHom (φ.compLeft (G × G) ∘ₗ LinearMap.funLeft k B (Prod.map f f))
  τ₃ := ModuleCat.ofHom (φ.compLeft (G × G × G)
    ∘ₗ LinearMap.funLeft k B (Prod.map f (Prod.map f f)))
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
    twoCocycles B →ₗ[k] twoCocycles A :=
  ShortComplex.cyclesMap' (mapShortComplexH2 A B f φ) (shortComplexH2 B).moduleCatLeftHomologyData
    (shortComplexH2 A).moduleCatLeftHomologyData

noncomputable abbrev mapH2 : H2 B →ₗ[k] H2 A :=
  ShortComplex.leftHomologyMap' (mapShortComplexH2 A B f φ)
    (shortComplexH2 B).moduleCatLeftHomologyData
    (shortComplexH2 A).moduleCatLeftHomologyData

@[simp]
lemma H2π_comp_mapH2 :
    mapH2 A B f φ ∘ₗ H2π B = H2π A ∘ₗ mapTwoCocycles A B f φ :=
  leftHomologyπ_naturality' (mapShortComplexH2 A B f φ) _ _

@[reassoc (attr := simp)]
lemma cocyclesMap_comp_isoTwoCocycles_hom :
    cocyclesMap A B f φ 2 ≫ (isoTwoCocycles A).hom
      = (isoTwoCocycles B).hom ≫ mapTwoCocycles A B f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 A)).i, mapTwoCocycles,
      Category.assoc, cyclesMap'_i, isoTwoCocycles, ← Category.assoc]
  simp

@[reassoc (attr := simp)]
lemma cohomologyMap_comp_isoH2_hom :
    cohomologyMap A B f φ 2 ≫ (isoH2 A).hom = (isoH2 B).hom ≫ mapH2 A B f φ := by
  simpa [← cancel_epi (groupCohomologyπ _ _), mapH2, Category.assoc]
    using (leftHomologyπ_naturality' (mapShortComplexH2 A B f φ)
    (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm

end IsPairMap
end groupCohomology
