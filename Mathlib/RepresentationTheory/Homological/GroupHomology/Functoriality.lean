import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
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

end LinearMap
namespace ModuleCat

variable (R : Type u) [Ring R]

lemma ofHom_comp {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    ofHom (g ∘ₗ f) = ofHom f ≫ ofHom g := rfl

lemma finsupp_lhom_ext {M N : ModuleCat R} {α : Type*} (f g : ModuleCat.of R (α →₀ M) ⟶ N)
    (h : ∀ x, ModuleCat.ofHom (Finsupp.lsingle x) ≫ f = ModuleCat.ofHom (Finsupp.lsingle x) ≫ g) :
    f = g :=
  Finsupp.lhom_ext' h

end ModuleCat

namespace groupHomology
open Rep

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  (A : Rep k G) (B : Rep k H) (f : G →* H) (φ : A →ₗ[k] B) (n : ℕ)

class IsPairMap : Prop where
  compatible : ∀ (g : G), B.ρ (f g) ∘ₗ φ = φ ∘ₗ A.ρ g

namespace IsPairMap
open Representation

variable {A B f φ} (S : Subgroup G)

lemma compatible_apply [IsPairMap A B f φ] (g : G) (x : A) :
    B.ρ (f g) (φ x) = φ (A.ρ g x) :=
  congr($(compatible g) x)

instance comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    (A : Rep k G) (B : Rep k H) (C : Rep k K) (f : G →* H) (g : H →* K) (φ : A →ₗ[k] B)
    (ψ : B →ₗ[k] C) [IsPairMap A B f φ] [IsPairMap B C g ψ] :
    IsPairMap A C (g.comp f) (ψ ∘ₗ φ) where
  compatible x := by
    ext y
    have := congr($(compatible (A := A) (B := B) (f := f) (φ := φ) x) y)
    have := congr($(compatible (A := B) (B := C) (f := g) (φ := ψ) (f x)) (φ y))
    simp_all

instance instCoinf [S.Normal] : IsPairMap A (coinf A S) (QuotientGroup.mk' S)
    (coinvariantsKer (A.ρ.comp S.subtype)).mkQ where
  compatible := by intros; rfl

instance instRes : IsPairMap ((Action.res _ f).obj B) B f LinearMap.id where
  compatible := by intros; rfl

instance instHom {A B : Rep k G} (f : A ⟶ B) : IsPairMap A B (MonoidHom.id G) f.hom where
  compatible g := (f.comm g).symm

variable [IsPairMap A B f φ] [DecidableEq G] [DecidableEq H]

variable (A B f φ) in
@[simps (config := .lemmasOnly)]
noncomputable def chainsMap :
    inhomogeneousChains A ⟶ inhomogeneousChains B where
  f i := ModuleCat.ofHom <| Finsupp.lsum k fun x => Finsupp.lsingle (f ∘ x) ∘ₗ φ
  comm' i j (hij : _ = _) := by
    subst hij
    refine Finsupp.lhom_ext ?_
    intro g a
    simp only [ChainComplex.of_x, ModuleCat.coe_of, ModuleCat.ofHom, inhomogeneousChains.d_def,
      ModuleCat.comp_def, LinearMap.coe_comp, Finsupp.coe_lsum, Function.comp_apply, Rep.d_single]
    rw [Finsupp.sum_add_index, Finsupp.sum_sum_index']
    · simpa [Fin.comp_contractNth] using congr(Finsupp.single (fun (k : Fin j) => f (g k.succ))
        $(compatible_apply (f := f) (g 0)⁻¹ _))
    all_goals simp

@[reassoc (attr := simp)]
lemma lsingle_comp_chainsMap (n : ℕ) (x : Fin n → G) :
    ModuleCat.ofHom (Finsupp.lsingle x) ≫ (chainsMap A B f φ).f n
      = ModuleCat.ofHom φ ≫ ModuleCat.ofHom (Finsupp.lsingle (f ∘ x)) := by
  ext
  exact Finsupp.sum_single_index (by simp)

@[simp]
lemma chainsMap_f_single (n : ℕ) (x : Fin n → G) (a : A) :
    (chainsMap A B f φ).f n (Finsupp.single x a) = Finsupp.single (f ∘ x) (φ a) :=
  Finsupp.sum_single_index (by simp)

@[simp]
lemma chainsMap_id :
    chainsMap A A (MonoidHom.id G) (Action.Hom.hom (𝟙 A)) = 𝟙 (inhomogeneousChains A) := by
  ext : 1
  apply ModuleCat.finsupp_lhom_ext
  exact lsingle_comp_chainsMap _

lemma chainsMap_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    (A : Rep k G) (B : Rep k H) (C : Rep k K) (f : G →* H) (g : H →* K) (φ : A →ₗ[k] B)
    (ψ : B →ₗ[k] C) [IsPairMap A B f φ] [IsPairMap B C g ψ] :
    chainsMap A C (g.comp f) (ψ ∘ₗ φ) = (chainsMap A B f φ) ≫ (chainsMap B C g ψ) := by
  ext : 1
  apply ModuleCat.finsupp_lhom_ext
  intro x
  simp [Rep.coe_def, ModuleCat.ofHom_comp, Function.comp.assoc]

variable (A B f φ)
noncomputable abbrev cyclesMap (n : ℕ) :
    groupHomology.cycles A n ⟶ groupHomology.cycles B n :=
  HomologicalComplex.cyclesMap (chainsMap A B f φ) n

noncomputable abbrev homologyMap (n : ℕ) :
  groupHomology A n ⟶ groupHomology B n :=
HomologicalComplex.homologyMap (chainsMap A B f φ) n

@[simps]
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupHomology A n
  map {A B} φ :=
    letI : IsPairMap A B (MonoidHom.id _) φ.hom := instHom φ
    homologyMap A B (MonoidHom.id _) φ.hom n
  map_id A := by
    simp only [homologyMap, chainsMap_id,
      HomologicalComplex.homologyMap_id (inhomogeneousChains A) n]
    rfl
  map_comp f g := by
    simp only [← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]
    rfl

@[reassoc (attr := simp)]
lemma chainsMap_f_0_comp_zeroChainsLEquiv :
    (chainsMap A B f φ).f 0 ≫ (zeroChainsLEquiv B : (inhomogeneousChains B).X 0 →ₗ[k] B)
      = (zeroChainsLEquiv A : (inhomogeneousChains A).X 0 →ₗ[k] A) ≫ ModuleCat.ofHom φ := by
  apply ModuleCat.finsupp_lhom_ext
  intro x
  ext y
  rw [lsingle_comp_chainsMap_assoc]
  simp [ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, Function.comp_apply,
    ModuleCat.comp_def, zeroChainsLEquiv, coe_def, Unique.eq_default]

@[reassoc (attr := simp)]
lemma chainsMap_f_1_comp_oneChainsLEquiv :
    (chainsMap A B f φ).f 1 ≫ (oneChainsLEquiv B : (inhomogeneousChains B).X 1 →ₗ[k] (H →₀ B))
      = (oneChainsLEquiv A).toModuleIso.hom
      ≫ ModuleCat.ofHom (Finsupp.lsum k fun g => Finsupp.lsingle (f g) ∘ₗ φ) := by
  apply ModuleCat.finsupp_lhom_ext
  intro x
  ext y
  rw [lsingle_comp_chainsMap_assoc]
  simp [ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, Function.comp_apply,
    ModuleCat.comp_def, oneChainsLEquiv, coe_def]

@[reassoc (attr := simp)]
lemma chainsMap_f_2_comp_twoChainsLEquiv :
    (chainsMap A B f φ).f 2
      ≫ (twoChainsLEquiv B : (inhomogeneousChains B).X 2 →ₗ[k] H × H →₀ B)
      = (twoChainsLEquiv A).toModuleIso.hom
      ≫ ModuleCat.ofHom (Finsupp.lsum k fun g => Finsupp.lsingle (f g.1, f g.2) ∘ₗ φ) := by
  apply ModuleCat.finsupp_lhom_ext
  intro x
  ext y
  rw [lsingle_comp_chainsMap_assoc]
  simp [ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, Function.comp_apply,
    ModuleCat.comp_def, twoChainsLEquiv, coe_def]

@[reassoc (attr := simp)]
lemma chainsMap_f_3_comp_threeChainsLEquiv :
    (chainsMap A B f φ).f 3
      ≫ (threeChainsLEquiv B : (inhomogeneousChains B).X 3 →ₗ[k] H × H × H →₀ B)
      = (threeChainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (Finsupp.lsum k
        fun g => Finsupp.lsingle (f g.1, f g.2.1, f g.2.2) ∘ₗ φ) := by
  apply ModuleCat.finsupp_lhom_ext
  intro x
  ext y
  rw [lsingle_comp_chainsMap_assoc]
  simp [ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, Function.comp_apply,
    ModuleCat.comp_def, threeChainsLEquiv, coe_def, ← Fin.comp_tail]

open ShortComplex

noncomputable def mapH0 : H0 A →ₗ[k] H0 B :=
  Submodule.mapQ _ _ φ <| Submodule.span_le.2 <| fun x ⟨⟨g, y⟩, hy⟩ =>
    mem_coinvariantsKer B.ρ (f g) (φ y) _ <| by simp [compatible_apply, ← hy]

@[simps]
noncomputable def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := ModuleCat.ofHom (Finsupp.lsum k fun g => Finsupp.lsingle (f g.1, f g.2) ∘ₗ φ)
  τ₂ := ModuleCat.ofHom (Finsupp.lsum k fun g => Finsupp.lsingle (f g) ∘ₗ φ)
  τ₃ := ModuleCat.ofHom φ
  comm₁₂ := Finsupp.lhom_ext fun a b => by
    simp [ModuleCat.coe_of, ModuleCat.comp_def, ModuleCat.ofHom, shortComplexH1,
      Finsupp.sum_add_index, Finsupp.sum_sub_index, ← compatible_apply (f := f)]
  comm₂₃ := Finsupp.lhom_ext fun a b => by
    simp [ModuleCat.coe_of, ModuleCat.comp_def, ModuleCat.ofHom, shortComplexH1,
      ← compatible_apply (f := f)]

noncomputable abbrev mapOneCycles :
    oneCycles A →ₗ[k] oneCycles B :=
  ShortComplex.cyclesMap' (mapShortComplexH1 A B f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

noncomputable abbrev mapH1 : H1 A →ₗ[k] H1 B :=
  ShortComplex.leftHomologyMap' (mapShortComplexH1 A B f φ)
    (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

@[simp]
lemma subtype_comp_mapOneCycles :
    (oneCycles B).subtype ∘ₗ mapOneCycles A B f φ
      = (Finsupp.lsum k fun g => Finsupp.lsingle (f g) ∘ₗ φ) ∘ₗ (oneCycles A).subtype :=
  ShortComplex.cyclesMap'_i (mapShortComplexH1 A B f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[simp]
lemma H1π_comp_mapH1 :
    mapH1 A B f φ ∘ₗ H1π A = H1π B ∘ₗ mapOneCycles A B f φ :=
  leftHomologyπ_naturality' (mapShortComplexH1 A B f φ) _ _

@[reassoc (attr := simp)]
lemma cyclesMap_comp_isoOneCycles_hom :
    cyclesMap A B f φ 1 ≫ (isoOneCycles B).hom
      = (isoOneCycles A).hom ≫ mapOneCycles A B f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapOneCycles,
      Category.assoc, cyclesMap'_i, isoOneCycles, ← Category.assoc]
  simp

@[reassoc (attr := simp)]
lemma homologyMap_comp_isoH1_hom :
    homologyMap A B f φ 1 ≫ (isoH1 B).hom = (isoH1 A).hom ≫ mapH1 A B f φ := by
  simpa [← cancel_epi (groupHomologyπ _ _), mapH1, Category.assoc]
    using (leftHomologyπ_naturality' (mapShortComplexH1 A B f φ)
    (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm

@[simps]
noncomputable def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := ModuleCat.ofHom (Finsupp.lsum k fun g => Finsupp.lsingle (f g.1, f g.2.1, f g.2.2) ∘ₗ φ)
  τ₂ := ModuleCat.ofHom (Finsupp.lsum k fun g => Finsupp.lsingle (f g.1, f g.2) ∘ₗ φ)
  τ₃ := ModuleCat.ofHom (Finsupp.lsum k fun g => Finsupp.lsingle (f g) ∘ₗ φ)
  comm₁₂ := Finsupp.lhom_ext fun a b => by
    simp [ModuleCat.coe_of, ModuleCat.comp_def, ModuleCat.ofHom, shortComplexH2,
      Finsupp.sum_add_index, Finsupp.sum_sub_index, ← compatible_apply (f := f)]
  comm₂₃ := Finsupp.lhom_ext fun a b => by
    simp [ModuleCat.coe_of, ModuleCat.comp_def, ModuleCat.ofHom, shortComplexH2,
      Finsupp.sum_add_index, Finsupp.sum_sub_index, ← compatible_apply (f := f)]

noncomputable abbrev mapTwoCycles :
    twoCycles A →ₗ[k] twoCycles B :=
  ShortComplex.cyclesMap' (mapShortComplexH2 A B f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

noncomputable abbrev mapH2 : H2 A →ₗ[k] H2 B :=
  ShortComplex.leftHomologyMap' (mapShortComplexH2 A B f φ)
    (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

@[simp]
lemma subtype_comp_mapTwoCycles :
    (twoCycles B).subtype ∘ₗ mapTwoCycles A B f φ
      = (Finsupp.lsum k fun g => Finsupp.lsingle (f g.1, f g.2) ∘ₗ φ) ∘ₗ (twoCycles A).subtype :=
  ShortComplex.cyclesMap'_i (mapShortComplexH2 A B f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[simp]
lemma H2π_comp_mapH2 :
    mapH2 A B f φ ∘ₗ H2π A = H2π B ∘ₗ mapTwoCycles A B f φ :=
  leftHomologyπ_naturality' (mapShortComplexH2 A B f φ) _ _

@[reassoc (attr := simp)]
lemma cyclesMap_comp_isoTwoCycles_hom :
    cyclesMap A B f φ 2 ≫ (isoTwoCycles B).hom
      = (isoTwoCycles A).hom ≫ mapTwoCycles A B f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapTwoCycles,
      Category.assoc, cyclesMap'_i, isoTwoCycles, ← Category.assoc]
  simp

@[reassoc (attr := simp)]
lemma homologyMap_comp_isoH2_hom :
    homologyMap A B f φ 2 ≫ (isoH2 B).hom = (isoH2 A).hom ≫ mapH2 A B f φ := by
  simpa [← cancel_epi (groupHomologyπ _ _), mapH2, Category.assoc]
    using (leftHomologyπ_naturality' (mapShortComplexH2 A B f φ)
    (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm

end IsPairMap
end groupHomology
