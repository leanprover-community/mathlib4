/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Functoriality of group homology
Given a commutative ring `k`, a group homomorphism `f : G →* H`, a `k`-linear `G`-representation
`A`, a `k`-linear `H`-representation `B`, and a representation morphism `A ⟶ Res(f)(B)`, we get
a chain map `inhomogeneousChains A ⟶ inhomogeneousChains B` and hence maps on homology
`Hₙ(G, A) ⟶ Hₙ(H, B)`. We use this to show a short exact sequence of representations induces a
short exact sequence of complexes of inhomogeneous chains, allowing us to specialize API for long
exact sequences to group homology.
We also provide extra API for these functoriality maps in degrees 0, 1, 2.
## Main definitions
* `groupHomology.chainsMap f φ` is the map `inhomogeneousChains A ⟶ inhomogeneousChains B`
induced by a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`.
* `groupHomology.map f φ n` is the map `Hₙ(G, A) ⟶ Hₙ(H, B)` induced by a group homomorphism
`f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`.
-/

universe v u
variable (n : ℕ)

open CategoryTheory

@[simp]
lemma QuotientGroup.mk'_comp_subtype {G : Type*} [Group G] (H : Subgroup G) [H.Normal] :
    (QuotientGroup.mk' H).comp H.subtype = 1 := by
  ext
  simp

lemma Fin.comp_contractNth {G H : Type*} [MulOneClass G] [MulOneClass H] (f : G →* H)
    (j : Fin (n + 1)) (g : Fin (n + 1) → G) :
    f ∘ Fin.contractNth j (· * ·) g = Fin.contractNth j (· * ·) (f ∘ g) := by
  ext x
  rcases lt_trichotomy (x : ℕ) j with (h|h|h)
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_eq, h, f.map_mul]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_gt, h]

namespace Finsupp

/-- Given a family `Sᵢ` of `R`-submodules of `M` indexed by a type `α`, this is the `R`-submodule
of `α →₀ M` of functions `f` such that `f i ∈ Sᵢ` for all `i : α`. -/
def submodule {R M α : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (S : α → Submodule R M) : Submodule R (α →₀ M) where
  carrier := { x | ∀ i, x i ∈ S i }
  add_mem' hx hy i := (S i).add_mem (hx i) (hy i)
  zero_mem' i := (S i).zero_mem
  smul_mem' r _ hx i := (S i).smul_mem r (hx i)

@[simp]
lemma mem_submodule_iff {R M α : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (S : α → Submodule R M) (x : α →₀ M) :
    x ∈ Finsupp.submodule S ↔ ∀ i, x i ∈ S i := by
  rfl

theorem ker_mapRange {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (I : Type*) :
    LinearMap.ker (Finsupp.mapRange.linearMap (α := I) f) =
      Finsupp.submodule (fun _ => LinearMap.ker f) := by
  ext x
  simp [Finsupp.ext_iff]

theorem mapRange_linearMap_comp_lsingle
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) {I : Type*} (i : I) :
    Finsupp.mapRange.linearMap f ∘ₗ Finsupp.lsingle i = Finsupp.lsingle i ∘ₗ f := by
  ext x y
  simp

theorem mapRange_injective_iff {α M N : Type*} [Zero M] [Zero N] [Nonempty α]
    (f : M → N) (hf : f 0 = 0) :
    (mapRange (α := α) f hf).Injective ↔ Function.Injective f :=
  ⟨fun h x y hxy => Nonempty.elim (α := α) inferInstance fun a => by
    simpa using congr($(@h (Finsupp.single a x) (Finsupp.single a y)
      (by simp only [hxy, mapRange_single])) a),
  fun h _ _ hxy => Finsupp.ext fun i => h <| by simpa using congr($hxy i)⟩

lemma mapDomain_surjective {α β M : Type*} [AddCommMonoid M] (f : α → β) (hf : f.Surjective) :
    (mapDomain (M := M) f).Surjective := by
  intro x
  induction' x using Finsupp.induction with b m x _ _ hy
  · use 0
    rw [mapDomain_zero]
  · rcases hy with ⟨y, rfl⟩
    rcases hf b with ⟨a, rfl⟩
    use single a m + y
    rw [mapDomain_add, mapDomain_single]

theorem range_mapRange_linearMap
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : LinearMap.ker f = ⊥) (I : Type*) :
    LinearMap.range (Finsupp.mapRange.linearMap (α := I) f)
      = Finsupp.submodule (fun _ => LinearMap.range f) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    simp [← hy]
  · intro hx
    choose y hy using hx
    refine ⟨⟨x.support, y, fun i => ?_⟩, by ext; simp_all⟩
    constructor
    <;> contrapose!
    <;> simp_all (config := {contextual := true}) [← hy, map_zero, LinearMap.ker_eq_bot'.1 hf]

end Finsupp

namespace groupHomology
open Rep Finsupp

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k G} {B : Rep k H} (f : G →* H) (φ : A ⟶ (Action.res _ f).obj B) (n : ℕ)

open Representation

variable (S : Subgroup G)

variable [DecidableEq G] [DecidableEq H]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the chain map sending `∑ aᵢ • gᵢ : (Fin n → G) →₀ A)` to
`∑ φ(aᵢ) • (f ∘ gᵢ)) : (Fin n → H) →₀ B`. -/
@[simps (config := .lemmasOnly) f f_hom]
noncomputable def chainsMap :
    inhomogeneousChains A ⟶ inhomogeneousChains B where
  f i := ModuleCat.ofHom <| mapRange.linearMap φ.hom.hom ∘ₗ lmapDomain A k (f ∘ ·)
  comm' i j (hij : _ = _) := by
    subst hij
    refine ModuleCat.hom_ext <| lhom_ext fun g a => ?_
    simpa [Fin.comp_contractNth, map_add] using
      congr(single (fun (k : Fin j) => f (g k.succ)) $((hom_comm_apply φ (g 0)⁻¹ a).symm))

@[reassoc (attr := simp)]
lemma lsingle_comp_chainsMap (n : ℕ) (x : Fin n → G) :
    ModuleCat.ofHom (lsingle x) ≫ (chainsMap f φ).f n =
      φ.hom ≫ ModuleCat.ofHom (lsingle (f ∘ x)) := by
  ext
  simp [chainsMap_f]

lemma chainsMap_f_single (n : ℕ) (x : Fin n → G) (a : A) :
    (chainsMap f φ).f n (single x a) = single (f ∘ x) (φ.hom a) := by
  simp [chainsMap_f]

@[simp]
lemma chainsMap_id :
    chainsMap (MonoidHom.id G) (𝟙 A) = 𝟙 (inhomogeneousChains A) := by
  ext : 1
  exact ModuleCat.hom_ext <| lhom_ext' fun _ =>
    ModuleCat.hom_ext_iff.1 <| lsingle_comp_chainsMap (k := k) (MonoidHom.id G) _ _ _

@[simp]
lemma chainsMap_id_eq_mapRange {A B : Rep k G} (i : ℕ) (φ : A ⟶ B) :
    (chainsMap (MonoidHom.id G) φ).f i = ModuleCat.ofHom (mapRange.linearMap φ.hom.hom) := by
  refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
  simp [chainsMap_f, MonoidHom.coe_id]

@[simp]
lemma chainsMap_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K] {A : Rep k G} {B : Rep k H} {C : Rep k K}
    (f : G →* H) (g : H →* K) (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    chainsMap (g.comp f) (φ ≫ (Action.res _ f).map ψ) = chainsMap f φ ≫ chainsMap g ψ := by
  ext : 1
  refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
  simp [chainsMap_f, Function.comp_assoc]

@[simp]
lemma chainsMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    chainsMap (MonoidHom.id G) (φ ≫ ψ) =
      chainsMap (MonoidHom.id G) φ ≫ chainsMap (MonoidHom.id G) ψ :=
  chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[simp]
lemma chainsMap_zero : chainsMap f (0 : A ⟶ (Action.res _ f).obj B) = 0 :=
  HomologicalComplex.hom_ext _ _ <| fun i => ModuleCat.hom_ext <| lhom_ext' <|
    fun x => LinearMap.ext fun (y : A) => by simp [chainsMap_f, LinearMap.zero_apply (M₂ := B)]

lemma chainsMap_f_map_mono (hf : Function.Injective f) [Mono φ] (i : ℕ) :
    Mono ((chainsMap f φ).f i) := by
  simpa [ModuleCat.mono_iff_injective] using
    ((mapRange_injective_iff φ.hom (map_zero _)).2 <| (Rep.mono_iff_injective φ).1
    inferInstance).comp (mapDomain_injective hf.comp_left)

instance chainsMap_id_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : ℕ) :
    Mono ((chainsMap (MonoidHom.id G) φ).f i) :=
  chainsMap_f_map_mono (MonoidHom.id G) φ (fun _ _ h => h) _

lemma chainsMap_f_map_epi (hf : Function.Surjective f) [Epi φ] (i : ℕ) :
    Epi ((chainsMap f φ).f i) := by
  simpa [ModuleCat.epi_iff_surjective] using
    (mapRange_surjective φ.hom (map_zero _) ((Rep.epi_iff_surjective φ).1 inferInstance)).comp
    (mapDomain_surjective _ hf.comp_left)

instance chainsMap_id_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : ℕ) :
    Epi ((chainsMap (MonoidHom.id G) φ).f i) :=
  chainsMap_f_map_epi _ _ (fun x => ⟨x, rfl⟩) _

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `Zₙ(G, A) ⟶ Zₙ(H, B)` sending `∑ aᵢ • gᵢ : (Fin n → G) →₀ A)` to
`∑ φ(aᵢ) • (f ∘ gᵢ) : (Fin n → H) →₀ B`. -/
noncomputable abbrev cyclesMap (n : ℕ) :
    groupHomology.cycles A n ⟶ groupHomology.cycles B n :=
  HomologicalComplex.cyclesMap (chainsMap f φ) n

@[simp]
theorem cyclesMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    cyclesMap (MonoidHom.id G) (φ ≫ ψ) n =
      cyclesMap (MonoidHom.id G) φ n ≫ cyclesMap (MonoidHom.id G) ψ n := by
  simp [cyclesMap, chainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `Hₙ(G, A) ⟶ Hₙ(H, B)` sending `∑ aᵢ • gᵢ : (Fin n → G) →₀ A)` to
`∑ φ(aᵢ) • (f ∘ gᵢ) : (Fin n → H) →₀ B`. -/
noncomputable abbrev map (n : ℕ) :
  groupHomology A n ⟶ groupHomology B n :=
HomologicalComplex.homologyMap (chainsMap f φ) n

@[simp]
theorem map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    map (MonoidHom.id G) (φ ≫ ψ) n =
      map (MonoidHom.id G) φ n ≫ map (MonoidHom.id G) ψ n := by
  rw [map, chainsMap_id_comp, HomologicalComplex.homologyMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map sending `∑ aᵢ • gᵢ : G →₀ A)` to `∑ φ(aᵢ) • f(gᵢ) : H →₀ B` -/
noncomputable abbrev fOne := mapRange.linearMap φ.hom.hom ∘ₗ lmapDomain A k f

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map sending `∑ aᵢ • (gᵢ₁, gᵢ₂) : G × G →₀ A` to
`∑ φ(aᵢ) • (f(gᵢ₁), f(gᵢ₂)) : H × H →₀ B`.  -/
noncomputable abbrev fTwo := mapRange.linearMap φ.hom.hom ∘ₗ lmapDomain A k (Prod.map f f)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map sending `∑ aᵢ • (gᵢ₁, gᵢ₂, gᵢ₃) : G × G × G →₀ A` to
`∑ φ(aᵢ) • (f(gᵢ₁), f(gᵢ₂), f(gᵢ₃)) : H × H × H →₀ B`.  -/
noncomputable abbrev fThree :=
  mapRange.linearMap φ.hom.hom ∘ₗ lmapDomain A k (Prod.map f (Prod.map f f))

@[reassoc (attr := simp)]
lemma chainsMap_f_0_comp_zeroChainsLequiv :
    (chainsMap f φ).f 0 ≫ (zeroChainsLequiv B).toModuleIso.hom =
      (zeroChainsLequiv A).toModuleIso.hom ≫ φ.hom := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, zeroChainsLequiv, Unique.eq_default]

@[reassoc (attr := simp)]
lemma chainsMap_f_1_comp_oneChainsLequiv :
    (chainsMap f φ).f 1 ≫ (oneChainsLequiv B).toModuleIso.hom =
      (oneChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fOne f φ) := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, oneChainsLequiv, fOne]

@[reassoc (attr := simp)]
lemma chainsMap_f_2_comp_twoChainsLequiv :
    (chainsMap f φ).f 2 ≫ (twoChainsLequiv B).toModuleIso.hom =
      (twoChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fTwo f φ) := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, twoChainsLequiv, fTwo]

@[reassoc (attr := simp)]
lemma chainsMap_f_3_comp_threeChainsLequiv :
    (chainsMap f φ).f 3 ≫
      (threeChainsLequiv B).toModuleIso.hom =
      (threeChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fThree f φ) := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, threeChainsLequiv, fThree, ← Fin.comp_tail]

open ShortComplex

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is induced map `A_G ⟶ B_H`. -/
noncomputable def H0Map : ModuleCat.of k (H0 A) ⟶ ModuleCat.of k (H0 B) :=
  ModuleCat.ofHom <| Submodule.mapQ _ _ φ.hom.hom <| Submodule.span_le.2 <| fun _ ⟨⟨g, y⟩, hy⟩ =>
    mem_augmentationSubmodule_of_eq (f g) (φ.hom y) _ <| by
      simpa [← hy] using (hom_comm_apply φ _ _).symm

omit [DecidableEq G] in
@[simp]
theorem H0Map_id : H0Map (MonoidHom.id G) (𝟙 A) = 𝟙 _ :=
  ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl

@[simp]
theorem H0Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    H0Map (g.comp f) (φ ≫ (Action.res _ f).map ψ) = H0Map f φ ≫ H0Map g ψ :=
  ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl

omit [DecidableEq G] in
theorem H0Map_eq_coinvariantsFunctor_map {A B : Rep k G} (f : A ⟶ B) :
    H0Map (MonoidHom.id G) f = (coinvariantsFunctor k G).map f := by
  rfl

instance epi_H0Map_of_epi {A B : Rep k G} (f : A ⟶ B) [Epi f] :
    Epi (H0Map (MonoidHom.id G) f) :=
  (inferInstanceAs (Epi <| (coinvariantsFunctor k G).map f))

omit [DecidableEq G] [DecidableEq H] in
@[reassoc (attr := simp)]
theorem H0π_comp_H0Map :
    H0π A ≫ H0Map f φ = φ.hom ≫ H0π B := by
  refine ModuleCat.hom_ext <| LinearMap.ext fun _ => ?_
  simp [H0Map, H0π, shortComplexH0]

@[reassoc (attr := simp)]
theorem map_comp_isoH0_hom :
    map f φ 0 ≫ (isoH0 B).hom = (isoH0 A).hom ≫ H0Map f φ := by
  simp [isoZeroCycles, ← cancel_epi (groupHomologyπ _ _),
    chainsMap_f_0_comp_zeroChainsLequiv_assoc f φ]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map from the short complex `(H × H →₀ A) --dOne--> (H →₀ A) --dZero--> A`
to `(G × G →₀ B) --dOne--> (G →₀ B) --dZero--> B`. -/
@[simps]
noncomputable def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := ModuleCat.ofHom (fTwo f φ)
  τ₂ := ModuleCat.ofHom (fOne f φ)
  τ₃ := φ.hom
  comm₁₂ := ModuleCat.hom_ext <| lhom_ext fun a b => by
    simpa [dOne, map_add, map_sub, shortComplexH1, fTwo, fOne, ← map_inv]
      using congr(Finsupp.single (f a.2) $((hom_comm_apply φ _ _).symm))
  comm₂₃ := ModuleCat.hom_ext <| lhom_ext fun a b => by
    simpa [map_add, map_sub, shortComplexH1, fOne, ← map_inv]
      using (hom_comm_apply φ _ _).symm

@[simp]
theorem mapShortComplexH1_zero :
    mapShortComplexH1 (A := A) (B := B) f 0 = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
    show mapRange.linearMap 0 (mapDomain _ (single _ _)) = 0
    simp [LinearMap.zero_apply (M₂ := B)] }

@[simp]
theorem mapShortComplexH1_id : mapShortComplexH1 (MonoidHom.id G) (𝟙 A) = 𝟙 _ := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => ?_
    show Finsupp.mapRange.linearMap LinearMap.id _ = Finsupp.single _ _
    simp [MonoidHom.coe_id] }

@[simp]
theorem mapShortComplexH1_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    mapShortComplexH1 (g.comp f) (φ ≫ (Action.res _ f).map ψ) =
      (mapShortComplexH1 f φ) ≫ (mapShortComplexH1 g ψ) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
    simp [shortComplexH1, Prod.map, fTwo, fOne] }

@[simp]
theorem mapShortComplexH1_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH1 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH1 (MonoidHom.id G) φ ≫ mapShortComplexH1 (MonoidHom.id G) ψ :=
  mapShortComplexH1_comp (MonoidHom.id G) (MonoidHom.id G) _ _

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is induced map `Z₁(G, A) ⟶ Z₁(H, B)`. -/
noncomputable abbrev mapOneCycles :
    ModuleCat.of k (oneCycles A) ⟶ ModuleCat.of k (oneCycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is induced map `H₁(G, A) ⟶ H₁(H, B)`. -/
noncomputable abbrev H1Map :
    ModuleCat.of k (H1 A) ⟶ ModuleCat.of k (H1 B) :=
  ShortComplex.leftHomologyMap' (mapShortComplexH1 f φ)
    (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

@[simp]
theorem H1Map_id : H1Map (MonoidHom.id G) (𝟙 A) = 𝟙 _ := by
  simp only [H1Map, shortComplexH1, mapShortComplexH1_id, leftHomologyMap'_id]
  rfl

@[simp]
theorem H1Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    H1Map (g.comp f) (φ ≫ (Action.res _ f).map ψ) = H1Map f φ ≫ H1Map g ψ := by
  simpa [H1Map, shortComplexH1, mapShortComplexH1_comp] using leftHomologyMap'_comp _ _ _ _ _

@[simp]
theorem H1Map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    H1Map (MonoidHom.id G) (φ ≫ ψ) = H1Map (MonoidHom.id G) φ ≫ H1Map (MonoidHom.id G) ψ :=
  H1Map_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[reassoc (attr := simp), elementwise]
lemma mapOneCycles_comp_subtype :
    mapOneCycles f φ ≫ ModuleCat.ofHom (oneCycles B).subtype =
      ModuleCat.ofHom (fOne f φ ∘ₗ (oneCycles A).subtype) :=
  ShortComplex.cyclesMap'_i (mapShortComplexH1 f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

lemma coe_mapOneCycles (x : oneCycles A) :
    (mapOneCycles f φ x).1 = fOne f φ (x.1) := rfl

@[reassoc (attr := simp)]
lemma H1π_comp_H1Map :
    H1π A ≫ H1Map f φ = mapOneCycles f φ ≫ H1π B :=
  leftHomologyπ_naturality' (mapShortComplexH1 f φ) _ _

@[reassoc (attr := simp)]
lemma cyclesMap_comp_isoOneCycles_hom :
    cyclesMap f φ 1 ≫ (isoOneCycles B).hom
      = (isoOneCycles A).hom ≫ mapOneCycles f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapOneCycles,
      Category.assoc, cyclesMap'_i, isoOneCycles, ← Category.assoc]
  simp [chainsMap_f_1_comp_oneChainsLequiv f φ, mapShortComplexH1]


@[reassoc (attr := simp)]
lemma map_comp_isoH1_hom :
    map f φ 1 ≫ (isoH1 B).hom = (isoH1 A).hom ≫ H1Map f φ := by
  simp [← cancel_epi (groupHomologyπ _ _), H1Map, Category.assoc,
    (leftHomologyπ_naturality' (mapShortComplexH1 f φ)
    (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map from the short complex
`(G × G × G →₀ A) --dTwo--> (G × G →₀ A) --dOne--> (G →₀ A)` to
`(H × H × H →₀ B) --dTwo--> (H × H →₀ B) --dOne--> (H →₀ B)`. -/
@[simps]
noncomputable def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := ModuleCat.ofHom (fThree f φ)
  τ₂ := ModuleCat.ofHom (fTwo f φ)
  τ₃ := ModuleCat.ofHom (fOne f φ)
  comm₁₂ := ModuleCat.hom_ext <| lhom_ext fun a b => by
    simpa [dTwo, shortComplexH2, map_add, map_sub, fThree, fTwo, ← map_inv]
      using congr(Finsupp.single _ $((hom_comm_apply φ _ _).symm))
  comm₂₃ := ModuleCat.hom_ext <| lhom_ext fun a b => by
    simpa [dOne, shortComplexH2, map_add, map_sub, fTwo, fOne, ← map_inv]
      using congr(Finsupp.single _ $((hom_comm_apply φ _ _).symm))

@[simp]
theorem mapShortComplexH2_zero :
    mapShortComplexH2 (A := A) (B := B) f 0 = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => ?_
    show Finsupp.mapRange.linearMap 0 (Finsupp.mapDomain _ (Finsupp.single _ _)) = 0
    simp [LinearMap.zero_apply (M₂ := B)] }

@[simp]
theorem mapShortComplexH2_id : mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => ?_
    show Finsupp.mapRange.linearMap LinearMap.id _ = Finsupp.single _ _
    simp [MonoidHom.coe_id] }

@[simp]
theorem mapShortComplexH2_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    mapShortComplexH2 (g.comp f) (φ ≫ (Action.res _ f).map ψ)
      = (mapShortComplexH2 f φ) ≫ (mapShortComplexH2 g ψ) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => ?_
    simp [shortComplexH2, Prod.map, fThree, fTwo, fOne] }

@[simp]
theorem mapShortComplexH2_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH2 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH2 (MonoidHom.id G) φ ≫ mapShortComplexH2 (MonoidHom.id G) ψ :=
  mapShortComplexH2_comp (MonoidHom.id G) (MonoidHom.id G) _ _

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is induced map `Z₂(G, A) ⟶ Z₂(H, B)`. -/
noncomputable abbrev mapTwoCycles :
    ModuleCat.of k (twoCycles A) ⟶ ModuleCat.of k (twoCycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is induced map `H₂(G, A) ⟶ H₂(H, B)`. -/
noncomputable abbrev H2Map :
    ModuleCat.of k (H2 A) ⟶ ModuleCat.of k (H2 B) :=
  ShortComplex.leftHomologyMap' (mapShortComplexH2 f φ)
    (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

@[simp]
theorem H2Map_id : H2Map (MonoidHom.id G) (𝟙 A) = 𝟙 _ := by
  simp only [H2Map, shortComplexH2, mapShortComplexH2_id, leftHomologyMap'_id]
  rfl

@[simp]
theorem H2Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    H2Map (g.comp f) (φ ≫ (Action.res _ f).map ψ) = H2Map f φ ≫ H2Map g ψ := by
  simpa [H2Map, shortComplexH2, mapShortComplexH2_comp] using leftHomologyMap'_comp _ _ _ _ _

@[simp]
theorem H2Map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    H2Map (MonoidHom.id G) (φ ≫ ψ) = H2Map (MonoidHom.id G) φ ≫ H2Map (MonoidHom.id G) ψ :=
  H2Map_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[reassoc (attr := simp)]
lemma mapTwoCycles_comp_subtype :
    mapTwoCycles f φ ≫ ModuleCat.ofHom (twoCycles B).subtype =
      ModuleCat.ofHom (fTwo f φ ∘ₗ (twoCycles A).subtype) :=
  ShortComplex.cyclesMap'_i (mapShortComplexH2 f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[reassoc (attr := simp)]
lemma H2π_comp_H2Map :
     H2π A ≫ H2Map f φ = mapTwoCycles f φ ≫ H2π B :=
  leftHomologyπ_naturality' (mapShortComplexH2 f φ) _ _

@[reassoc (attr := simp)]
lemma cyclesMap_comp_isoTwoCycles_hom :
    cyclesMap f φ 2 ≫ (isoTwoCycles B).hom =
      (isoTwoCycles A).hom ≫ mapTwoCycles f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapTwoCycles,
      Category.assoc, cyclesMap'_i, isoTwoCycles, ← Category.assoc]
  simp [chainsMap_f_2_comp_twoChainsLequiv f φ, mapShortComplexH2]

@[reassoc (attr := simp)]
lemma map_comp_isoH2_hom :
    map f φ 2 ≫ (isoH2 B).hom = (isoH2 A).hom ≫ H2Map f φ := by
  simp [← cancel_epi (groupHomologyπ _ _), H2Map, Category.assoc]

variable (k G) in
/-- The functor sending a representation to its complex of inhomogeneous chains. -/
@[simps]
noncomputable def chainsFunctor [DecidableEq G] :
    Rep k G ⥤ ChainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousChains A
  map f := chainsMap (MonoidHom.id _) f
  map_id _ := chainsMap_id
  map_comp φ ψ := chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

instance : (chainsFunctor k G).PreservesZeroMorphisms where
  map_zero X Y := by
    ext i : 1
    refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => ?_
    simp

variable (k G) in
/-- The functor sending a `G`-representation `A` to `Hₙ(G, A)`. -/
@[simps]
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupHomology A n
  map {A B} φ := map (MonoidHom.id _) φ n
  map_id A := by simp [map]
  map_comp f g := by
    simp only [← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]
    rfl

instance (n : ℕ) : (functor k G n).PreservesZeroMorphisms where
  map_zero _ _ := by simp [map]

end groupHomology
