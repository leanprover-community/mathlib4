/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

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

end groupHomology
