/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
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


namespace ModuleCat

variable (R : Type u) [Ring R]

/-@[ext]
lemma finsupp_lhom_ext {M N : ModuleCat R} {α : Type*} (f g : ModuleCat.of R (α →₀ M) ⟶ N)
    (h : ∀ x, Finsupp.lsingle x ≫ f = Finsupp.lsingle x ≫ g) :
    f = g := Finsupp.lhom_ext' h-/

end ModuleCat

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

@[reassoc (attr := simp)]
lemma chainsMap_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K] {A : Rep k G} {B : Rep k H} {C : Rep k K}
    (f : G →* H) (g : H →* K) (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    chainsMap (g.comp f) (φ ≫ (Action.res _ f).map ψ) = chainsMap f φ ≫ chainsMap g ψ := by
  ext : 1
  refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
  simp [chainsMap_f, Function.comp_assoc]

@[reassoc (attr := simp)]
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

@[reassoc (attr := simp)]
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

@[reassoc (attr := simp)]
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
lemma chainsMap_f_0_comp_zeroChainsLEquiv :
    (chainsMap f φ).f 0 ≫ (zeroChainsLEquiv B).toModuleIso.hom =
      (zeroChainsLEquiv A).toModuleIso.hom ≫ φ.hom := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, zeroChainsLEquiv, Unique.eq_default]

@[reassoc (attr := simp)]
lemma chainsMap_f_1_comp_oneChainsLEquiv :
    (chainsMap f φ).f 1 ≫ (oneChainsLEquiv B).toModuleIso.hom =
      (oneChainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fOne f φ) := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, oneChainsLEquiv, fOne]

@[reassoc (attr := simp)]
lemma chainsMap_f_2_comp_twoChainsLEquiv :
    (chainsMap f φ).f 2 ≫ (twoChainsLEquiv B).toModuleIso.hom =
      (twoChainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fTwo f φ) := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, twoChainsLEquiv, fTwo]

@[reassoc (attr := simp)]
lemma chainsMap_f_3_comp_threeChainsLEquiv :
    (chainsMap f φ).f 3 ≫
      (threeChainsLEquiv B).toModuleIso.hom =
      (threeChainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fThree f φ) := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, threeChainsLEquiv, fThree, ← Fin.comp_tail]

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

@[reassoc (attr := simp)]
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
    chainsMap_f_0_comp_zeroChainsLEquiv_assoc f φ]

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

@[reassoc (attr := simp)]
theorem mapShortComplexH1_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    mapShortComplexH1 (g.comp f) (φ ≫ (Action.res _ f).map ψ)
      = (mapShortComplexH1 f φ) ≫ (mapShortComplexH1 g ψ) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
    simp [shortComplexH1, Prod.map, fTwo, fOne] }

@[reassoc (attr := simp)]
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

@[reassoc (attr := simp)]
theorem H1Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    H1Map (g.comp f) (φ ≫ (Action.res _ f).map ψ) = H1Map f φ ≫ H1Map g ψ := by
  simpa [H1Map, shortComplexH1, mapShortComplexH1_comp] using leftHomologyMap'_comp _ _ _ _ _

@[reassoc (attr := simp)]
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
  simp [chainsMap_f_1_comp_oneChainsLEquiv f φ, mapShortComplexH1]


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

@[reassoc (attr := simp)]
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

@[reassoc (attr := simp)]
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

@[reassoc (attr := simp)]
theorem H2Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    H2Map (g.comp f) (φ ≫ (Action.res _ f).map ψ) = H2Map f φ ≫ H2Map g ψ := by
  simpa [H2Map, shortComplexH2, mapShortComplexH2_comp] using leftHomologyMap'_comp _ _ _ _ _

@[reassoc (attr := simp)]
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
  simp [chainsMap_f_2_comp_twoChainsLEquiv f φ, mapShortComplexH2]

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

variable {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

lemma chainsMap_shortExact :
    ShortExact ((chainsFunctor k G).mapShortComplex.obj X) :=
  letI := hX.2
  letI := hX.3
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      show LinearMap.range ((chainsMap (MonoidHom.id G) X.f).f i).hom =
        LinearMap.ker ((chainsMap (MonoidHom.id G) X.g).f i).hom
      rw [chainsMap_id_eq_mapRange, chainsMap_id_eq_mapRange, ker_mapRange,
        range_mapRange_linearMap, this]
      exact LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 <|
        (forget₂ (Rep k G) (ModuleCat k)).map_mono X.f)
    mono_f := chainsMap_id_f_map_mono X.f i
    epi_g := chainsMap_id_f_map_epi X.g i }

/-- The short complex  `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)` associated to an exact sequence
of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : j + 1 = i) :=
  ShortComplex.mk _ _ ((chainsMap_shortExact hX).δ_comp i j hij)

variable (X) in
/-- The short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev mapShortComplex₂ (i : ℕ) :=
  ShortComplex.mk (map (MonoidHom.id G) X.f i) (map (MonoidHom.id G) X.g i) <| by
    simp [← map_id_comp, X.zero, map]

/-- The short complex `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : j + 1 = i) :=
  ShortComplex.mk _ _ ((chainsMap_shortExact hX).comp_δ i j hij)

/-- Exactness of `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)`. -/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₁ hX hij).Exact :=
  (chainsMap_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)`. -/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (chainsMap_shortExact hX).homology_exact₂ i

/--  Exactness of `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)`. -/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₃ hX hij).Exact :=
  (chainsMap_shortExact hX).homology_exact₃ i j hij

theorem δ_succ_apply_aux {i j l : ℕ}
    (y : (Fin i → G) →₀ X.X₂) (x : (Fin j → G) →₀ X.X₁)
    (hx : mapRange.linearMap X.f.hom.hom x = (inhomogeneousChains X.X₂).d i j y) :
    (inhomogeneousChains X.X₁).d j l x = 0 :=
  ShortExact.δ_apply_aux (chainsMap_shortExact hX) i j y x
    (by simpa [chainsMap_id_eq_mapRange] using hx) l

theorem δ_succ_apply (i j l : ℕ) (hij : j + 1 = i) (hjl : (ComplexShape.down ℕ).next j = l)
    (z : (Fin i → G) →₀ X.X₃) (hz : (inhomogeneousChains X.X₃).d i j z = 0)
    (y : (Fin i → G) →₀ X.X₂) (hy : (chainsMap (MonoidHom.id G) X.g).f i y = z)
    (x : (Fin j → G) →₀ X.X₁)
    (hx : Finsupp.mapRange.linearMap X.f.hom.hom x = (inhomogeneousChains X.X₂).d i j y) :
    (chainsMap_shortExact hX).δ i j hij (groupHomologyπ X.X₃ i <|
      (moduleCatCyclesIso _).inv ⟨z, show ((inhomogeneousChains X.X₃).dFrom i).hom z = 0 by
        simp_all [(inhomogeneousChains X.X₃).dFrom_eq hij]⟩) = groupHomologyπ X.X₁ j
      ((moduleCatCyclesIso _).inv ⟨x, δ_succ_apply_aux hX y x hx⟩) := by
  convert ShortExact.δ_apply (chainsMap_shortExact hX) i j hij z
    hz y hy x (by simpa [chainsMap_id_eq_mapRange] using hx) l hjl
  <;> rw [moduleCatCyclesIso_inv_apply]
  <;> rfl

/-- The degree 0 connecting homomorphism `H₁(G, X₃) ⟶ X₁_G` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H₀` and `H₁` than
general `δ`. -/
noncomputable def δ₀ :
    ModuleCat.of k (H1 X.X₃) ⟶ ModuleCat.of k (H0 X.X₁) :=
  (isoH1 X.X₃).inv ≫ (chainsMap_shortExact hX).δ 1 0 rfl ≫ (isoH0 X.X₁).hom

theorem δ₀_apply (z : G →₀ X.X₃) (hz : dZero X.X₃ z = 0) (y : G →₀ X.X₂)
    (hy : mapRange.linearMap X.g.hom.hom y = z) (x : X.X₁) (hx : X.f.hom x = dZero X.X₂ y) :
    δ₀ hX (H1π X.X₃ ⟨z, hz⟩) = H0π X.X₁ x := by
  have hxy : mapRange.linearMap X.f.hom.hom ((zeroChainsLEquiv X.X₁).symm x) =
      (inhomogeneousChains X.X₂).d 1 0 ((oneChainsLEquiv X.X₂).symm y) := by
    have := congr($((CommSq.horiz_inv ⟨dZero_comp_eq X.X₂⟩).w) y)
    simp_all [← hx, zeroChainsLEquiv, single_eq_same]
  have δ_1_0 := congr((isoH0 X.X₁).hom $((chainsMap_shortExact hX).δ_apply 1 0 rfl
    ((oneChainsLEquiv X.X₃).symm z)
    (by simpa [hz] using congr($((CommSq.horiz_inv ⟨dZero_comp_eq X.X₃⟩).w) z))
    ((oneChainsLEquiv X.X₂).symm y) (Finsupp.ext fun _ => by simp [← hy, oneChainsLEquiv])
    ((zeroChainsLEquiv X.X₁).symm x) (by simpa using hxy) 0 (by simp)))
  · convert δ_1_0
    · show (H1π X.X₃ ≫ δ₀ hX) ⟨z, hz⟩ = _
      simp [δ₀, ← Category.assoc, (CommSq.vert_inv ⟨groupHomologyπ_comp_isoH1_hom X.X₃⟩).w,
        isoOneCycles_inv_apply_eq_cyclesMk X.X₃ ⟨z, hz⟩]
    · simp [(Iso.eq_inv_comp _).2 (π_comp_isoH0_hom X.X₁).symm, -π_comp_isoH0_hom,
        isoZeroCycles_inv_apply_eq_cyclesMk X.X₁ x]

open Limits

theorem epi_δ₀_of_isZero (h0 : IsZero (ModuleCat.of k <| H0 X.X₂)) : Epi (δ₀ hX) := by
  letI : Epi ((chainsMap_shortExact hX).δ 1 0 rfl) := (chainsMap_shortExact hX).epi_δ _ _ rfl
    (h0.of_iso (isoH0 X.X₂))
  exact epi_comp _ _

/-- The degree 1 connecting homomorphism `H₂(G, X₃) ⟶ H₁(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H₁` and `H₂` than
general `δ`. -/
noncomputable def δ₁ :
    ModuleCat.of k (H2 X.X₃) ⟶ ModuleCat.of k (H1 X.X₁) :=
  (isoH2 X.X₃).inv ≫ (chainsMap_shortExact hX).δ 2 1 rfl ≫ (isoH1 X.X₁).hom

theorem δ₁_apply_aux (y : G × G →₀ X.X₂) (x : G →₀ X.X₁)
    (hx : mapRange.linearMap X.f.hom.hom x = dOne X.X₂ y) :
    dZero X.X₁ x = 0 := by
  have h1 := δ_succ_apply_aux hX (l := 0) ((twoChainsLEquiv X.X₂).symm y)
    ((oneChainsLEquiv X.X₁).symm x)
  have h2 := congr($((CommSq.horiz_inv ⟨(shortComplexH1Iso X.X₂).hom.comm₁₂⟩).w) y)
  have h3 := congr($((Iso.eq_inv_comp _).2 (shortComplexH1Iso X.X₁).hom.comm₂₃) x)
  have h4 := congr($((CommSq.vert_inv (h := (oneChainsLEquiv X.X₂).toModuleIso)
    ⟨(chainsMap_f_1_comp_oneChainsLEquiv (MonoidHom.id G) X.f)⟩).w) x)
  simp_all [shortComplexH1, fOne, MonoidHom.coe_id]

theorem δ₁_apply (z : G × G →₀ X.X₃) (hz : dOne X.X₃ z = 0) (y : G × G →₀ X.X₂)
    (hy : mapRange.linearMap X.g.hom.hom y = z) (x : G →₀ X.X₁)
    (hx : mapRange.linearMap X.f.hom.hom x = dOne X.X₂ y) :
    δ₁ hX (H2π X.X₃ ⟨z, hz⟩) = H1π X.X₁ ⟨x, δ₁_apply_aux hX y x hx⟩ := by
  have hxy : Finsupp.mapRange.linearMap X.f.hom.hom ((oneChainsLEquiv X.X₁).symm x) =
        (inhomogeneousChains X.X₂).d 2 1 ((twoChainsLEquiv X.X₂).symm y) :=
    have := congr($((CommSq.horiz_inv ⟨dOne_comp_eq X.X₂⟩).w) y)
    Finsupp.ext fun _ => by simp_all [← hx, oneChainsLEquiv]
  have δ_2_1 := congr((isoH1 X.X₁).hom $(δ_succ_apply hX _ _ 0 rfl (by simp)
    ((twoChainsLEquiv X.X₃).symm z)
    (by simpa [hz] using congr($((CommSq.horiz_inv ⟨dOne_comp_eq X.X₃⟩).w) z))
    ((twoChainsLEquiv X.X₂).symm y) (Finsupp.ext fun _ => by simp [← hy, twoChainsLEquiv])
    ((oneChainsLEquiv X.X₁).symm x) hxy))
  · convert δ_2_1
    · show (H2π X.X₃ ≫ δ₁ hX) ⟨z, hz⟩ = _
      rw [moduleCatCyclesIso_inv_apply]
      simp [δ₁, ← Category.assoc, (CommSq.vert_inv ⟨groupHomologyπ_comp_isoH2_hom X.X₃⟩).w,
        isoTwoCycles_inv_apply_eq_cyclesMk X.X₃ ⟨z, hz⟩, HomologicalComplex.cyclesMk]
    · rw [moduleCatCyclesIso_inv_apply]
      simp [(Iso.eq_inv_comp _).2 (groupHomologyπ_comp_isoH1_hom X.X₁).symm,
        -groupHomologyπ_comp_isoH1_hom, isoOneCycles_inv_apply_eq_cyclesMk X.X₁ ⟨x, _⟩,
        HomologicalComplex.cyclesMk]

theorem epi_δ₁_of_isZero (h1 : IsZero (ModuleCat.of k <| H1 X.X₂)) :
    Epi (δ₁ hX) := by
  letI : Epi ((chainsMap_shortExact hX).δ 2 1 rfl) := (chainsMap_shortExact hX).epi_δ _ _ rfl
    (h1.of_iso (isoH1 X.X₂))
  exact epi_comp _ _

variable (X) in
/-- The short complex `X₁_G ⟶ X₂_G ⟶ X₃_G` associated to a short complex of representations
`X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev H0ShortComplex₂ :=
  ShortComplex.mk (H0Map (MonoidHom.id G) X.f) (H0Map (MonoidHom.id G) X.g) <|
    ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| by
      ext x
      have := congr(Action.Hom.hom $(X.zero) x)
      simp_all [-ShortComplex.zero, H0Map, LinearMap.zero_apply (M₂ := X.X₃) x]

variable (X) in
/-- When `i = 0`, the general short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to a
short complex of representations agrees with our simpler expression of `X₁_G ⟶ X₂_G ⟶ X₃_G.` -/
noncomputable def isoH0ShortComplex₂ :
    mapShortComplex₂ X 0 ≅ H0ShortComplex₂ X :=
  isoMk (isoH0 _) (isoH0 _) (isoH0 _) (map_comp_isoH0_hom (MonoidHom.id G) X.f).symm
    (map_comp_isoH0_hom (MonoidHom.id G) X.g).symm

theorem H0ShortComplex₂_exact :
    (H0ShortComplex₂ X).Exact :=
  exact_of_iso (isoH0ShortComplex₂ X) (mapShortComplex₂_exact hX _)

/-- The short complex `H₁(G, X₃) ⟶ X₁_G ⟶ X₂_G` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H0ShortComplex₁ :=
  ShortComplex.mk (δ₀ hX) (H0Map (MonoidHom.id G) X.f) <| by
    simpa [δ₀, ← map_comp_isoH0_hom] using (chainsMap_shortExact hX).δ_comp_assoc 1 0 rfl _

/-- When `i = 0`, the general short complex `Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂)` associated to a
short exact sequence of representations agrees with our simpler expression for
`H₁(G, X₃) ⟶ X₁_G ⟶ X₂_G.` -/
noncomputable def isoH0ShortComplex₁ :
    mapShortComplex₁ hX (i := 1) rfl ≅ H0ShortComplex₁ hX :=
  isoMk (isoH1 _) (isoH0 _) (isoH0 _) (by simp [δ₀])
    (map_comp_isoH0_hom (MonoidHom.id G) _).symm

theorem H0ShortComplex₁_exact :
    (H0ShortComplex₁ hX).Exact :=
  exact_of_iso (isoH0ShortComplex₁ hX) (mapShortComplex₁_exact _ _)

/-- The short complex  `H₁(G, X₂) ⟶ H₁(G, X₃) ⟶ X₁_G` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H1ShortComplex₃ :=
  ShortComplex.mk (H1Map (MonoidHom.id G) X.g) (δ₀ hX) <| by
    have := (CommSq.vert_inv ⟨map_comp_isoH1_hom (MonoidHom.id G) X.g⟩).w
    have h := (chainsMap_shortExact hX).comp_δ 1 0 rfl
    simp_all only [δ₀, ← Category.assoc, Preadditive.IsIso.comp_right_eq_zero]
    simp_all

/-- When `i = 0`, the general short complex `Hᵢ₊₁(G, X₂) ⟶ Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H₁(G, X₂) ⟶ H₁(G, X₃) ⟶ X₁_G.` -/
noncomputable def isoH1ShortComplex₃ :
    mapShortComplex₃ hX (j := 0) rfl ≅ H1ShortComplex₃ hX :=
  isoMk (isoH1 _) (isoH1 _) (isoH0 _)
    (map_comp_isoH1_hom (MonoidHom.id G) _).symm (by simp [δ₀])

theorem H1ShortComplex₃_exact :
    (H1ShortComplex₃ hX).Exact :=
  exact_of_iso (isoH1ShortComplex₃ hX) (mapShortComplex₃_exact _ _)

variable (X) in
/-- The short complex `H₁(G, X₁) ⟶ H₁(G, X₂) ⟶ H₁(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev H1ShortComplex₂ :=
  ShortComplex.mk (H1Map (MonoidHom.id G) X.f) (H1Map (MonoidHom.id G) X.g) <| by
    simp [← H1Map_id_comp, X.zero, H1Map]

variable (X) in
/-- When `i = 1`, the general short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to
a short complex of representations agrees with our simpler expression for
`H₁(G, X₁) ⟶ H₁(G, X₂) ⟶ H₁(G, X₃).` -/
noncomputable def isoH1ShortComplex₂ :
    mapShortComplex₂ X 1 ≅ H1ShortComplex₂ X :=
  isoMk (isoH1 _) (isoH1 _) (isoH1 _) (map_comp_isoH1_hom _ _).symm
    (map_comp_isoH1_hom _ _).symm

theorem H1ShortComplex₂_exact :
    (H1ShortComplex₂ X).Exact :=
  exact_of_iso (isoH1ShortComplex₂ X) (mapShortComplex₂_exact hX _)

/-- The short complex `H₂(G, X₃) ⟶ H₁(G, X₁) ⟶ H₁(G, X₂)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H1ShortComplex₁ :=
  ShortComplex.mk (δ₁ hX) (H1Map (MonoidHom.id G) X.f) <| by
    simpa [δ₁, ← map_comp_isoH1_hom] using (chainsMap_shortExact hX).δ_comp_assoc 2 1 rfl _

/-- When `i = 1`, the general short complex `Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂)` associated to a
short exact sequence of representations agrees with our simpler expression for
`H₂(G, X₃) ⟶ H₁(G, X₁) ⟶ H₁(G, X₂).` -/
noncomputable def isoH1ShortComplex₁ :
    mapShortComplex₁ hX (i := 2) rfl ≅ H1ShortComplex₁ hX :=
  isoMk (isoH2 _) (isoH1 _) (isoH1 _) (by simp [δ₁])
    (map_comp_isoH1_hom (MonoidHom.id G) _).symm

theorem H1ShortComplex₁_exact :
    (H1ShortComplex₁ hX).Exact :=
  exact_of_iso (isoH1ShortComplex₁ hX) (mapShortComplex₁_exact _ _)

/-- The short complex  `H₂(G, X₂) ⟶ H₂(G, X₃) ⟶ H₁(G, X₁)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H2ShortComplex₃ :=
  ShortComplex.mk (H2Map (MonoidHom.id G) X.g) (δ₁ hX) <| by
    have := (CommSq.vert_inv ⟨map_comp_isoH2_hom (MonoidHom.id G) X.g⟩).w
    have h := (chainsMap_shortExact hX).comp_δ 2 1 rfl
    simp_all only [δ₁, ← Category.assoc, Preadditive.IsIso.comp_right_eq_zero]
    simp_all

/-- When `i = 1`, the general short complex `Hᵢ₊₁(G, X₂) ⟶ Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H₂(G, X₂) ⟶ H₂(G, X₃) ⟶ H₁(G, X₁).` -/
noncomputable def isoH2ShortComplex₃ :
    mapShortComplex₃ hX (j := 1) rfl ≅ H2ShortComplex₃ hX :=
  isoMk (isoH2 _) (isoH2 _) (isoH1 _) (map_comp_isoH2_hom _ _).symm (by simp [δ₁])

theorem H2ShortComplex₃_exact :
    (H2ShortComplex₃ hX).Exact :=
  exact_of_iso (isoH2ShortComplex₃ hX) (mapShortComplex₃_exact _ _)

end groupHomology
