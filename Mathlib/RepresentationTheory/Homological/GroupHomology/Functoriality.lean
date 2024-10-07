import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
universe v u
variable (n : ℕ)

open CategoryTheory

lemma MonoidHom.coe_id {G : Type*} [MulOneClass G] :
    ⇑(MonoidHom.id G) = _root_.id := rfl

lemma Fin.comp_contractNth {G H : Type*} [MulOneClass G] [MulOneClass H] (f : G →* H)
    (j : Fin (n + 1)) (g : Fin (n + 1) → G) :
    f ∘ Fin.contractNth j (· * ·) g = Fin.contractNth j (· * ·) (f ∘ g) := by
  ext x
  rcases lt_trichotomy (x : ℕ) j with (h|h|h)
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_eq, h, f.map_mul]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_gt, h]

namespace Finsupp

def submodule {R M α : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (S : α → Submodule R M) : Submodule R (α →₀ M) where
  carrier := { x | ∀ i, x i ∈ S i }
  add_mem' hx hy i := (S i).add_mem (hx i) (hy i)
  zero_mem' i := (S i).zero_mem
  smul_mem' r _ hx i := (S i).smul_mem r (hx i)

@[simp]
lemma mem_submodule {R M α : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (S : α → Submodule R M) (x : α →₀ M) :
    x ∈ Finsupp.submodule S ↔ ∀ i, x i ∈ S i := by
  rfl

theorem ker_mapRange {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (I : Type*) [DecidableEq I] :
    LinearMap.ker (Finsupp.mapRange.linearMap (α := I) f)
      = Finsupp.submodule (fun _ => LinearMap.ker f) := by
  ext x
  simp [Finsupp.ext_iff]

theorem mapRange_linearMap_comp_lsingle
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) {I : Type*} [DecidableEq I] (i : I) :
    Finsupp.mapRange.linearMap f ∘ₗ Finsupp.lsingle i = Finsupp.lsingle i ∘ₗ f := by
  ext x y
  simp

theorem mapRange_injective_iff {α M N : Type*} [Zero M] [Zero N]
    [Nonempty α] (f : M → N) (hf : f 0 = 0) :
    (mapRange (α := α) f hf).Injective ↔ Function.Injective f :=
  ⟨fun h x y hxy => Nonempty.elim (α := α) inferInstance fun a => by
    simpa using congr($(@h (Finsupp.single a x) (Finsupp.single a y)
      (by simp only [hxy, mapRange_single])) a),
  fun h x y hxy => Finsupp.ext fun i => h <| by simpa using congr($hxy i)⟩

theorem range_mapRange {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : LinearMap.ker f = ⊥)
    (I : Type*) [DecidableEq I] :
    LinearMap.range (Finsupp.mapRange.linearMap (α := I) f)
      = Finsupp.submodule (fun _ => LinearMap.range f) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy]
    simp
  · intro hx
    choose y hy using hx
    refine ⟨⟨x.support, y, fun i => ?_⟩, by ext; simp_all⟩
    constructor
    <;> contrapose!
    <;> simp_all (config := {contextual := true}) [← hy, map_zero,
      LinearMap.ker_eq_bot'.1 hf]

end Finsupp

namespace ModuleCat

variable (R : Type u) [Ring R]

lemma ofHom_comp {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    ofHom (g ∘ₗ f) = ofHom f ≫ ofHom g := rfl

@[ext]
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
  f i := ModuleCat.ofHom <| Finsupp.mapRange.linearMap φ ∘ₗ Finsupp.lmapDomain A k (f ∘ ·)
  comm' i j (hij : _ = _) := by
    subst hij
    refine Finsupp.lhom_ext ?_
    intro g a
    simpa [ChainComplex.of_x, ModuleCat.coe_of, ModuleCat.ofHom, ModuleCat.comp_def, map_add,
      map_sum, Fin.comp_contractNth] using congr(Finsupp.single (fun (k : Fin j) => f (g k.succ))
        $(compatible_apply (f := f) (g 0)⁻¹ _))

@[reassoc (attr := simp)]
lemma lsingle_comp_chainsMap (n : ℕ) (x : Fin n → G) :
    ModuleCat.ofHom (Finsupp.lsingle x) ≫ (chainsMap A B f φ).f n
      = ModuleCat.ofHom φ ≫ ModuleCat.ofHom (Finsupp.lsingle (f ∘ x)) := by
  ext
  simp [chainsMap_f]

@[simp]
lemma chainsMap_f_single (n : ℕ) (x : Fin n → G) (a : A) :
    (chainsMap A B f φ).f n (Finsupp.single x a) = Finsupp.single (f ∘ x) (φ a) := by
  simp [chainsMap_f]

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

@[simp]
lemma chainsMap_eq_mapRange {A B : Rep k G} (i : ℕ) (φ : A ⟶ B) :
    (chainsMap A B (MonoidHom.id G) φ.hom).f i = Finsupp.mapRange.linearMap φ.hom := by
  ext x
  have : (fun (x : Fin i → G) => MonoidHom.id G ∘ x) = id := by ext; rfl
  simp [chainsMap_f, ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, ModuleCat.comp_def,
    this, -Finsupp.mapRange.linearMap_apply, -id_eq]

instance chainsMap_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : ℕ) :
    Mono ((chainsMap A B (MonoidHom.id G) φ.hom).f i) := by
  rw [chainsMap_eq_mapRange]
  exact (ModuleCat.mono_iff_injective _).2 <|
    (Finsupp.mapRange_injective_iff φ.hom (map_zero _)).2 <|
    (ModuleCat.mono_iff_injective φ.hom).1 <| (forget₂ (Rep k G) (ModuleCat k)).map_mono φ

instance chainsMap_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : ℕ) :
    Epi ((chainsMap A B (MonoidHom.id G) φ.hom).f i) where
  left_cancellation f g h := ModuleCat.finsupp_lhom_ext (R := k) _ _ fun x => by
    have h1 : ModuleCat.ofHom (Finsupp.lsingle x) ≫ Finsupp.mapRange.linearMap φ.hom
      = φ.hom ≫ ModuleCat.ofHom (Finsupp.lsingle x) :=
      Finsupp.mapRange_linearMap_comp_lsingle φ.hom x
    letI : Epi φ.hom := (forget₂ (Rep k G) (ModuleCat k)).map_epi φ
    simpa only [← cancel_epi φ.hom, ← Category.assoc, ← h1,
      ← chainsMap_eq_mapRange] using ModuleCat.finsupp_lhom_ext_iff.1 h x

variable (A B f φ)
noncomputable abbrev cyclesMap (n : ℕ) :
    groupHomology.cycles A n ⟶ groupHomology.cycles B n :=
  HomologicalComplex.cyclesMap (chainsMap A B f φ) n

noncomputable abbrev homologyMap (n : ℕ) :
  groupHomology A n ⟶ groupHomology B n :=
HomologicalComplex.homologyMap (chainsMap A B f φ) n

noncomputable abbrev fOne := Finsupp.mapRange.linearMap φ ∘ₗ Finsupp.lmapDomain A k f
noncomputable abbrev fTwo := Finsupp.mapRange.linearMap φ ∘ₗ Finsupp.lmapDomain A k (Prod.map f f)
noncomputable abbrev fThree := Finsupp.mapRange.linearMap φ
  ∘ₗ Finsupp.lmapDomain A k (Prod.map f (Prod.map f f))

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
      = (oneChainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fOne A B f φ) := by
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
      = (twoChainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fTwo A B f φ) := by
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
      = (threeChainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fThree A B f φ) := by
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
  τ₁ := ModuleCat.ofHom (fTwo A B f φ)
  τ₂ := ModuleCat.ofHom (fOne A B f φ)
  τ₃ := ModuleCat.ofHom φ
  comm₁₂ := Finsupp.lhom_ext fun a b => by
    simp [ModuleCat.coe_of, ModuleCat.comp_def, ModuleCat.ofHom, shortComplexH1,
      ← compatible_apply (f := f), map_add, map_sub]
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
    (oneCycles B).subtype ∘ₗ mapOneCycles A B f φ = fOne A B f φ ∘ₗ (oneCycles A).subtype :=
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
  τ₁ := ModuleCat.ofHom (fThree A B f φ)
  τ₂ := ModuleCat.ofHom (fTwo A B f φ)
  τ₃ := ModuleCat.ofHom (fOne A B f φ)
  comm₁₂ := Finsupp.lhom_ext fun a b => by
    simp [ModuleCat.coe_of, ModuleCat.comp_def, ModuleCat.ofHom, shortComplexH2,
      map_add, map_sub, ← compatible_apply (f := f)]
  comm₂₃ := Finsupp.lhom_ext fun a b => by
    simp [ModuleCat.coe_of, ModuleCat.comp_def, ModuleCat.ofHom, shortComplexH2,
      map_add, map_sub, ← compatible_apply (f := f)]

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
      = fTwo A B f φ ∘ₗ (twoCycles A).subtype :=
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
open IsPairMap

variable [DecidableEq G]

variable (k G) in
@[simps]
noncomputable def chainsFunctor : Rep k G ⥤ ChainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousChains A
  map f := chainsMap _ _ (MonoidHom.id _) f.hom
  map_id _ := chainsMap_id
  map_comp {X Y Z} φ ψ := chainsMap_comp X Y Z (MonoidHom.id G) (MonoidHom.id G) φ.hom ψ.hom

instance : (chainsFunctor k G).PreservesZeroMorphisms where
  map_zero X Y := by
    ext i : 1
    apply Finsupp.lhom_ext
    intro x y
    simp only [chainsFunctor_obj, ChainComplex.of_x, ModuleCat.coe_of, chainsFunctor_map,
      Action.zero_hom, chainsMap_f, ModuleCat.ofHom, LinearMap.coe_comp, Function.comp_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, HomologicalComplex.zero_f]
    exact Finsupp.single_zero _ -- :/

variable (k G) in

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

open ShortComplex

def mapShortExact (X : ShortComplex (Rep k G)) (H : ShortExact X) :
    ShortExact ((chainsFunctor k G).mapShortComplex.obj X) :=
  letI := H.2
  letI := H.3
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      have : LinearMap.range X.f.hom = LinearMap.ker X.g.hom :=
        (H.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      show LinearMap.range ((chainsMap X.X₁ X.X₂ (MonoidHom.id G) X.f.hom).f i)
        = LinearMap.ker ((chainsMap X.X₂ X.X₃ (MonoidHom.id G) X.g.hom).f i)
      rw [chainsMap_eq_mapRange, chainsMap_eq_mapRange, Finsupp.ker_mapRange,
        Finsupp.range_mapRange, this]
      · exact LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 <|
          (forget₂ (Rep k G) (ModuleCat k)).map_mono X.f)
    mono_f := chainsMap_f_map_mono X.f i
    epi_g := chainsMap_f_map_epi X.g i }

theorem δ_succ_apply_aux {X : ShortComplex (Rep k G)} (H : ShortExact X) (n : ℕ)
    (y : (Fin (n + 2) → G) →₀ X.X₂) (x : (Fin (n + 1) → G) →₀ X.X₁)
    (hx : Finsupp.mapRange.linearMap X.f.hom x = inhomogeneousChains.d X.X₂ (n + 1) y) :
    inhomogeneousChains.d X.X₁ n x = 0 := by
  letI := H.2
  simp only [coe_def] at hx
  have := congr($((chainsMap X.X₁ X.X₂ (MonoidHom.id G) X.f.hom).comm (n + 1) n) x)
  simp only [ChainComplex.of_x, ModuleCat.coe_of, ModuleCat.hom_def, chainsMap_eq_mapRange,
    inhomogeneousChains.d_def, ModuleCat.comp_def, LinearMap.coe_comp,
    Function.comp_apply, hx] at this
  apply (ModuleCat.mono_iff_injective ((chainsMap X.X₁ X.X₂ (MonoidHom.id G) X.f.hom).f n)).1
  · infer_instance
  · simp only [ChainComplex.of_x, chainsMap_eq_mapRange, map_zero]
    exact this ▸ congr($(inhomogeneousChains.d_comp_d X.X₂) y)

theorem δ₁_apply_aux {X : ShortComplex (Rep k G)} (H : ShortExact X) (y : G × G →₀ X.X₂)
    (x : G →₀ X.X₁) (hx : Finsupp.mapRange.linearMap X.f.hom x = dOne X.X₂ y) :
    dZero X.X₁ x = 0 := by
  have h1 := δ_succ_apply_aux H 0 ((twoChainsLEquiv X.X₂).symm y) ((oneChainsLEquiv X.X₁).symm x)
  have h2 := congr($((CommSq.horiz_inv ⟨(shortComplexH1Iso X.X₂).hom.comm₁₂⟩).w) y)
  have h3 := congr($((Iso.eq_inv_comp _).2 (shortComplexH1Iso X.X₁).hom.comm₂₃) x)
  have h4 := congr($((CommSq.vert_inv (h := (oneChainsLEquiv X.X₂).toModuleIso)
    ⟨(chainsMap_f_1_comp_oneChainsLEquiv X.X₁ X.X₂ (MonoidHom.id G) X.f.hom)⟩).w) x)
  exact h3.trans <| (zeroChainsLEquiv X.X₁).map_eq_zero_iff.2 <| h1 (h2.trans <|
    by simpa [shortComplexH1, MonoidHom.coe_id, hx.symm] using h4).symm

theorem δ_succ_apply (X : ShortComplex (Rep k G)) (H : ShortExact X) (n : ℕ)
    (z : (Fin (n + 2) → G) →₀ X.X₃) (hz : inhomogeneousChains.d X.X₃ (n + 1) z = 0)
    (y : (Fin (n + 2) → G) →₀ X.X₂)
    (hy : (chainsMap X.X₂ X.X₃ (MonoidHom.id G) X.g.hom).f (n + 2) y = z)
    (x : (Fin (n + 1) → G) →₀ X.X₁)
    (hx : Finsupp.mapRange.linearMap X.f.hom x = inhomogeneousChains.d X.X₂ (n + 1) y) :
    (mapShortExact X H).δ (n + 2) (n + 1) rfl (groupHomologyπ X.X₃ (n + 2) <|
      (cyclesSuccIso X.X₃ (n + 1)).inv ⟨z, hz⟩) = groupHomologyπ X.X₁ (n + 1)
      ((cyclesSuccIso X.X₁ n).inv ⟨x, δ_succ_apply_aux H n y x hx⟩) := by
  simp_rw [cyclesSuccIso_inv_eq]
  exact ShortExact.δ_apply (mapShortExact X H) (n + 2) (n + 1) rfl z (by simpa using hz) y hy x
    (by simpa using hx) n (by simp)

theorem δ₀_apply (X : ShortComplex (Rep k G)) (H : ShortExact X)
    (z : G →₀ X.X₃) (hz : dZero X.X₃ z = 0) (y : G →₀ X.X₂)
    (hy : Finsupp.mapRange.linearMap X.g.hom y = z)
    (x : X.X₁) (hx : X.f.hom x = dZero X.X₂ y) :
    (mapShortExact X H).δ 1 0 rfl (groupHomologyπ X.X₃ 1 <|
      (isoOneCycles X.X₃).inv ⟨z, hz⟩) = groupHomologyπ X.X₁ 0
      ((isoZeroCycles X.X₁).inv x) := by
  have h0z : ((inhomogeneousChains X.X₃).d 1 0) ((oneChainsLEquiv X.X₃).symm z) = 0 := by
    have := congr($((LinearEquiv.symm_comp_eq_comp_symm_iff _ _).2 (dZero_comp_eq X.X₃)) z)
    simp_all [ModuleCat.coe_of]
  have := ShortExact.δ_apply (mapShortExact X H) 1 0 rfl ((oneChainsLEquiv X.X₃).symm z)
    h0z ((oneChainsLEquiv X.X₂).symm y) ?_ ((zeroChainsLEquiv X.X₁).symm x) ?_ 0 (by simp)
  convert this
  · simp only [← cyclesSuccIso_0_trans_eq, Iso.trans_inv, ModuleCat.coe_comp, Function.comp_apply,
      cyclesSuccIso_inv_eq]
    rfl
  · simp only [HomologicalComplex.cyclesMk, ← moduleCatCyclesIso_inv_apply,
      isoZeroCycles_eq_moduleCatCyclesIso_trans]
    rfl
  · have := congr($((CommSq.vert_inv (h := (oneChainsLEquiv X.X₃).toModuleIso)
      ⟨(chainsMap_f_1_comp_oneChainsLEquiv X.X₂ X.X₃ (MonoidHom.id G) X.g.hom)⟩).w) y)
    simp only [ChainComplex.of_x, ModuleCat.coe_of, ModuleCat.hom_def, ModuleCat.ofHom,
      LinearEquiv.toModuleIso_inv, ModuleCat.comp_def, LinearMap.coe_comp, LinearEquiv.coe_coe,
      MonoidHom.coe_id, Finsupp.lmapDomain_id, LinearMap.id_coe,
      Function.comp_apply, chainsMap_eq_mapRange] at this
    simp [← hy, -Finsupp.mapRange.linearMap_toAddMonoidHom, -Finsupp.mapRange.linearMap_apply,
      coe_def, ModuleCat.coe_of, ← this]
  · have h1 := congr($((CommSq.vert_inv (g := (zeroChainsLEquiv X.X₁).toModuleIso)
      (h := (zeroChainsLEquiv X.X₂).toModuleIso)
      ⟨(chainsMap_f_0_comp_zeroChainsLEquiv X.X₁ X.X₂ (MonoidHom.id G) X.f.hom)⟩).w) x)
    have h2 := congr($((LinearEquiv.symm_comp_eq_comp_symm_iff _ _).2 (dZero_comp_eq X.X₂)) y)
    simp only [ChainComplex.of_x, ModuleCat.coe_of, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, inhomogeneousChains.d_def] at h2
    simpa [ModuleCat.coe_of, ← h2, ← hx] using h1.symm

theorem δ₁_apply (X : ShortComplex (Rep k G)) (H : ShortExact X)
    (z : G × G →₀ X.X₃) (hz : z ∈ twoCycles X.X₃) (y : G × G →₀ X.X₂)
    (hy : Finsupp.mapRange.linearMap X.g.hom y = z)
    (x : G →₀ X.X₁) (hx : Finsupp.mapRange.linearMap X.f.hom x = dOne X.X₂ y) :
    (mapShortExact X H).δ 2 1 rfl (groupHomologyπ X.X₃ 2 <|
      (isoTwoCycles X.X₃).inv ⟨z, hz⟩) = groupHomologyπ X.X₁ 1
      ((isoOneCycles X.X₁).inv ⟨x, δ₁_apply_aux H y _ hx⟩) := by
  have h1z : (inhomogeneousChains.d X.X₃ 1) ((twoChainsLEquiv X.X₃).symm z) = 0 := by
    have := congr($((LinearEquiv.symm_comp_eq_comp_symm_iff _ _).2 (dOne_comp_eq X.X₃)) z)
    simp_all [ModuleCat.coe_of, -Finsupp.coe_lsum, twoCycles]
  have h2x : (inhomogeneousChains.d X.X₁ 0) ((oneChainsLEquiv X.X₁).symm x) = 0 := by
    have := congr($((LinearEquiv.symm_comp_eq_comp_symm_iff _ _).2 (dZero_comp_eq X.X₁)) x)
    simp_all [δ₁_apply_aux H y x hx, -Finsupp.coe_lsum, ModuleCat.coe_of]
  have := δ_succ_apply X H 0 ((twoChainsLEquiv X.X₃).symm z) h1z
    ((twoChainsLEquiv X.X₂).symm y) ?_ ((oneChainsLEquiv X.X₁).symm x) ?_
  convert this
  · rw [← cyclesSuccIso_1_trans_eq]
    simp only [Nat.reduceAdd, Iso.trans_inv, LinearEquiv.toModuleIso_inv, ModuleCat.coe_comp,
      Function.comp_apply, CochainComplex.of_x]
    rfl
  · rw [← cyclesSuccIso_0_trans_eq]
    simp only [Nat.reduceAdd, Iso.trans_inv, LinearEquiv.toModuleIso_inv, ModuleCat.coe_comp,
      Function.comp_apply, CochainComplex.of_x]
    rfl
  · have h := congr($((CommSq.vert_inv (h := (twoChainsLEquiv X.X₃).toModuleIso)
      ⟨(chainsMap_f_2_comp_twoChainsLEquiv X.X₂ X.X₃ (MonoidHom.id G) X.g.hom)⟩).w) y)
    cases hy
    simp_all [ModuleCat.coe_of, ModuleCat.ofHom, ModuleCat.comp_def, ModuleCat.hom_def,
      chainsMap_eq_mapRange, -Finsupp.coe_lsum, MonoidHom.coe_id,
      -Finsupp.mapRange.linearMap_apply, coe_def]
  · have := congr($((LinearEquiv.symm_comp_eq_comp_symm_iff _ _).2 (dOne_comp_eq X.X₂)) y)
    have h4 := congr($((CommSq.vert_inv (h := (oneChainsLEquiv X.X₂).toModuleIso)
      ⟨(chainsMap_f_1_comp_oneChainsLEquiv X.X₁ X.X₂ (MonoidHom.id G) X.f.hom)⟩).w) x)
    simp_all [ModuleCat.coe_of, -Finsupp.coe_lsum, ← hx, ModuleCat.ofHom, ModuleCat.comp_def,
      ModuleCat.hom_def, chainsMap_eq_mapRange, MonoidHom.coe_id, coe_def]

end groupHomology
