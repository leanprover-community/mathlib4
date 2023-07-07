import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ShortExact.Abelian
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Topology.Separation
import Mathlib.Topology.Connected

set_option autoImplicit false

universe u

def setHomeoSubtype {X : Type _} [TopologicalSpace X] (s : Set X) : s ≃ₜ {x // x ∈ s} :=
{ toFun := fun x ↦ ⟨x.val, x.prop⟩
  invFun := fun x ↦ x
  left_inv := by
    intro x
    dsimp
  right_inv := by
    intro x
    dsimp }

namespace Function

open Classical

noncomputable
def ExtendBy {X Y : Type _} {C : Set X} (f : {i // i ∈ C} → Y) (junk : Y) : X → Y :=
fun x ↦ if hx : x ∈ C then f ⟨x, hx⟩ else junk

lemma restrict_extendBy_eq_self {X Y : Type _} {C : Set X} (f : {i // i ∈ C} → Y) (junk : Y) :
    C.restrict (f.ExtendBy junk) = f := by
  ext x
  dsimp [ExtendBy]
  simp only [Subtype.coe_prop, Subtype.coe_eta, dite_eq_ite, ite_true]

lemma extendBy_preimage_of_junk_ne_mem {X Y : Type _} {C : Set X} (f : {i // i ∈ C} → Y) (junk : Y)
    (s : Set Y) (hj : ¬ junk ∈ s) : (f.ExtendBy junk) ⁻¹' s = Subtype.val '' (f ⁻¹' s) := by
  ext x
  dsimp [ExtendBy]
  simp only [Set.mem_preimage, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  constructor
  <;> intro hx
  · split_ifs at hx with h
    · use h
      exact hx
    · exfalso
      exact hj hx
  · obtain ⟨hx,hfx⟩ := hx
    split_ifs
    exact hfx

lemma extendBy_preimage_of_junk_mem {X Y : Type _} {C : Set X} (f : {i // i ∈ C} → Y) (junk : Y)
    (s : Set Y) (hj : junk ∈ s) : (f.ExtendBy junk) ⁻¹' s = Subtype.val '' (f ⁻¹' s) ∪ Cᶜ := by
  ext x
  dsimp [ExtendBy]
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, Set.mem_compl_iff]
  constructor
  <;> intro hx
  · split_ifs at hx with h
    · left
      use h
      exact hx
    · right
      exact h
  · obtain ⟨hx,hfx⟩ := hx
    split_ifs
    · exact hfx
    · split_ifs
      assumption

end Function

namespace Set

open Classical

noncomputable
def piecewise' {X Y : Type _} {C : Set X} {p : X → Prop} (f : {i // i ∈ C} → Y)
    (g : (Subtype p) → Y) (junk : Y) : X → Y := C.piecewise (f.ExtendBy junk) (g.ExtendBy junk)

end Set

namespace LinearIndependent

variable {ι₁ : Type _} {ι₂ : Type _} (R : Type _) (M₁ : Type _) (M₂ : Type _)
  [Ring R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

instance : Module R (M₁ × M₂) := inferInstance

def ProdInl : M₁ →ₗ[R] M₁ × M₂ :=
{ toFun := fun m ↦ (m, 0)
  map_add' := by
    intro x y
    simp only [Prod.mk_add_mk, add_zero]
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply, Prod.smul_mk, smul_zero] }

def ProdInr : M₂ →ₗ[R] M₁ × M₂ :=
{ toFun := fun m ↦ (0, m)
  map_add' := by
    intro x y
    simp only [Prod.mk_add_mk, add_zero]
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply, Prod.smul_mk, smul_zero] }

lemma injective_prodInl : LinearMap.ker (ProdInl R M₁ M₂) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y h
  dsimp [ProdInl] at h
  rw [Prod.ext_iff] at h
  exact h.1

lemma injective_prodInr : LinearMap.ker (ProdInr R M₁ M₂) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y h
  dsimp [ProdInr] at h
  rw [Prod.ext_iff] at h
  exact h.2

variable {R M₁ M₂} (v₁ : ι₁ → M₁) (v₂ : ι₂ → M₂)

lemma sum_prod : LinearIndependent R v₁ → LinearIndependent R v₂ →
    LinearIndependent R (Sum.elim ((ProdInl R M₁ M₂) ∘ v₁)
    ((ProdInr R M₁ M₂) ∘ v₂))  := by
  intro h₁ h₂
  apply sum_type
  · rwa [LinearMap.linearIndependent_iff (ProdInl R M₁ M₂) (injective_prodInl R M₁ M₂)]
  · rwa [LinearMap.linearIndependent_iff (ProdInr R M₁ M₂) (injective_prodInr R M₁ M₂)]
  · rw [Submodule.disjoint_def]
    intro f hf₁ hf₂
    rw [mem_span_set] at hf₁ hf₂
    obtain ⟨c₁, ⟨hc₁, hsum₁⟩⟩ := hf₁
    obtain ⟨c₂, ⟨hc₂, hsum₂⟩⟩ := hf₂
    ext
    <;> dsimp
    · rw [Prod.ext_iff] at hsum₂
      rw [← hsum₂.1]
      have : (Finsupp.sum c₂ fun mi r ↦ r • mi).fst =
          LinearMap.fst R M₁ M₂ (Finsupp.sum c₂ fun mi r ↦ r • mi) := rfl
      rw [this, map_finsupp_sum]
      rw [← @Finsupp.sum_zero _ _ _ _ _ c₂]
      apply Finsupp.sum_congr
      intro x hx
      dsimp
      obtain ⟨y,hy⟩ := hc₂ hx
      dsimp [ProdInr] at hy
      rw [← hy]
      simp only [smul_zero]
    · rw [Prod.ext_iff] at hsum₁
      rw [← hsum₁.2]
      have : (Finsupp.sum c₁ fun mi r ↦ r • mi).snd =
          LinearMap.snd R M₁ M₂ (Finsupp.sum c₁ fun mi r ↦ r • mi) := rfl
      rw [this, map_finsupp_sum]
      rw [← @Finsupp.sum_zero _ _ _ _ _ c₁]
      apply Finsupp.sum_congr
      intro x hx
      dsimp
      obtain ⟨y,hy⟩ := hc₁ hx
      dsimp [ProdInl] at hy
      rw [← hy]
      simp only [smul_zero]

end LinearIndependent

namespace ModuleCat

variable {I : Type _} {J : Type _} {R : Type _} [Ring R] {N P : ModuleCat R} {v : I → N} {w : J → P}
  (hv : LinearIndependent R v) (hw : LinearIndependent R w)

open CategoryTheory
open CategoryTheory.Limits

lemma hom_inv_id_apply (e : P ≅ N) (x : P) : e.inv (e.hom x) = x := by
  apply Eq.symm _
  nth_rw 2 [← ModuleCat.id_apply x]
  rw [← e.hom_inv_id]
  rfl

lemma inv_hom_id_apply (e : P ≅ N) (x : N) : e.hom (e.inv x) = x := by
  apply Eq.symm _
  nth_rw 2 [← ModuleCat.id_apply x]
  rw [← e.inv_hom_id]
  rfl

lemma iso_inv_inj (e : P ≅ N) : Function.Injective e.inv := by
  apply Function.HasLeftInverse.injective
  use e.hom
  intro a
  exact inv_hom_id_apply e a

lemma iso_hom_inj (e : P ≅ N) : Function.Injective e.hom := by
  apply Function.HasLeftInverse.injective
  use e.inv
  intro a
  exact hom_inv_id_apply e a

@[simp]
lemma biprod.inl_fst_apply (x : N) :
    (biprod.fst : N ⊞ P ⟶ N) ((biprod.inl : N ⟶ N ⊞ P) x) = x := by
  apply Eq.symm _
  nth_rw 2 [← ModuleCat.id_apply x]
  rw [← biprod.inl_fst]
  rfl

@[simp]
lemma biprod.inl_snd_apply (x : N) :
    (biprod.snd : N ⊞ P ⟶ P) ((biprod.inl : N ⟶ N ⊞ P) x) = 0 := by
  rw [← forget_map]
  rw [← forget_map]
  rw [← types_comp_apply ((forget (ModuleCat R)).map _)
    ((forget (ModuleCat R)).map _) x]
  simp only [← CategoryTheory.Functor.map_comp]
  simp only [BinaryBicone.inl_snd, forget_map]
  rfl

@[simp]
lemma biprod.inr_fst_apply (x : P) :
    (biprod.fst : N ⊞ P ⟶ N) ((biprod.inr : P ⟶ N ⊞ P) x) = 0 := by
  rw [← forget_map]
  rw [← forget_map]
  rw [← types_comp_apply ((forget (ModuleCat R)).map _)
    ((forget (ModuleCat R)).map _) x]
  simp only [← CategoryTheory.Functor.map_comp]
  simp only [BinaryBicone.inr_fst, forget_map]
  rfl

@[simp]
lemma biprod.inr_snd_apply (x : P) :
    (biprod.snd : N ⊞ P ⟶ P) ((biprod.inr : P ⟶ N ⊞ P) x) = x := by
  apply Eq.symm _
  nth_rw 2 [← ModuleCat.id_apply x]
  rw [← biprod.inr_snd]
  rfl

lemma linearIndependent_sum_prod : LinearIndependent R
    (Sum.elim ((biprod.inl : N ⟶ N ⊞ P) ∘ v) ((biprod.inr : P ⟶ N ⊞ P) ∘ w)) := by
  have hN : (LinearIndependent.ProdInl R N P : N → N × P)  =
    (biprodIsoProd N P).hom ∘ (biprod.inl : N ⟶ N ⊞ P)
  · dsimp [LinearIndependent.ProdInl]
    ext n
    · simp only [Function.comp_apply]
      rw [biprodIsoProd_hom_apply]
      dsimp
      nth_rw 1 [← ModuleCat.id_apply n,  ← biprod.inl_fst]
      rfl
    · simp only [Function.comp_apply]
      rw [biprodIsoProd_hom_apply]
      dsimp
      rw [← forget_map biprod.snd]
      rw [← forget_map, ← types_comp_apply ((forget (ModuleCat R)).map _)
        ((forget (ModuleCat R)).map _) n]
      simp only [← CategoryTheory.Functor.map_comp]
      simp only [BinaryBicone.inl_snd, forget_map]
      rfl
  have hP : (LinearIndependent.ProdInr R N P : P → N × P) =
    (biprodIsoProd N P).hom ∘ (biprod.inr : P ⟶ N ⊞ P)
  · dsimp [LinearIndependent.ProdInl]
    ext n
    · simp only [Function.comp_apply]
      rw [biprodIsoProd_hom_apply]
      dsimp
      rw [← forget_map biprod.fst]
      rw [← forget_map, ← types_comp_apply ((forget (ModuleCat R)).map _)
        ((forget (ModuleCat R)).map _) n]
      simp only [← CategoryTheory.Functor.map_comp]
      simp only [BinaryBicone.inr_fst, forget_map]
      rfl
    · simp only [Function.comp_apply]
      rw [biprodIsoProd_hom_apply]
      dsimp
      nth_rw 1 [← ModuleCat.id_apply n,  ← biprod.inr_snd]
      rfl
  have h := LinearIndependent.sum_prod v w hv hw
  rw [hN, hP, Function.comp.assoc, Function.comp.assoc, ← forget_map, ← forget_map,
     ← Sum.comp_elim ((forget (ModuleCat R)).map (biprodIsoProd N P).hom) _ _] at h
  have h_inj : LinearMap.ker (biprodIsoProd N P).hom = ⊥
  · rw [LinearMap.ker_eq_bot]
    exact iso_hom_inj (biprodIsoProd N P)
  rw [← LinearMap.linearIndependent_iff _ h_inj]
  exact h

variable {M : ModuleCat R} {u : I ⊕ J → M} (hu : Function.Injective u) {f : N ⟶ M}
  {g : M ⟶ P} (hse : ShortExact f g) (huv : u ∘ Sum.inl = f ∘ v) (huw : g ∘ u ∘ Sum.inr = w)

lemma linearIndependent_shortExact : LinearIndependent R u := by
  rw [linearIndependent_sum]
  refine' ⟨_,_,_⟩
  · rw [huv]
    refine' (LinearMap.linearIndependent_iff (f : N →ₗ[R] M) _).mpr hv
    rw [LinearMap.ker_eq_bot]
    rw [← mono_iff_injective]
    exact hse.mono
  · rw [← huw] at hw
    refine' LinearIndependent.of_comp g _
    exact hw
  · rw [huv]
    have he := hse.exact
    rw [exact_iff] at he
    rw [Submodule.disjoint_def]
    intro m hml hmr
    have hm : m ∈ Submodule.span R (Set.range f) :=
      Submodule.span_mono (Set.range_comp_subset_range v f) hml
    have h₁ : Set.range f ⊆ LinearMap.range f
    · rw [LinearMap.range_coe]
    have h₂ : LinearMap.range f ≤ Submodule.span R (Set.range f)
    · intro x hx
      exact Submodule.subset_span hx
    rw [Submodule.span_eq_of_le (LinearMap.range f) h₁ h₂, he] at hm
    simp only [LinearMap.mem_ker] at hm
    rw [mem_span_set] at hmr
    obtain ⟨c, ⟨hc, hsum⟩⟩ := hmr
    rw [← hsum, map_finsupp_sum] at hm
    simp only [map_smul] at hm
    rw [linearIndependent_iff'] at hw
    have hui : Function.Injective (u ∘ Sum.inr) := Function.Injective.comp hu Sum.inr_injective
    specialize hw (Finset.preimage c.support (u ∘ Sum.inr) (Set.injOn_of_injective hui _))
    dsimp [Finsupp.sum] at hm
    rw [← Finset.sum_preimage (u ∘ Sum.inr) c.support (Set.injOn_of_injective hui _) _ _] at hm
    · rw [← huw] at hw
      specialize hw (c ∘ u ∘ Sum.inr) hm
      dsimp [Finsupp.sum] at hsum
      rw [← hsum]
      apply Finset.sum_eq_zero
      intro x hx
      obtain ⟨y,hy⟩ := hc hx
      specialize hw y
      rw [← hy]
      suffices : (c ∘ u ∘ Sum.inr) y = 0
      · dsimp at this ⊢
        rw [this]
        simp only [zero_smul]
      apply hw
      simp only [Finset.mem_preimage, Function.comp_apply]
      dsimp at hy
      rwa [hy]
    · intro x hx hnx
      exfalso
      exact hnx (hc hx)

end ModuleCat

namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {Z : Type _}

noncomputable
def equiv (e : X ≃ₜ Y) : LocallyConstant X Z ≃ LocallyConstant Y Z :=
{ toFun := comap e.invFun
  invFun := comap e.toFun
  left_inv := by
    intro x
    rw [comap_comp_apply _ _ e.continuous_toFun e.continuous_invFun]
    simp
  right_inv := by
    intro x
    rw [comap_comp_apply _ _ e.continuous_invFun e.continuous_toFun]
    simp }

@[simp]
theorem coe_comap_apply (f : X → Y) (g : LocallyConstant Y Z) (hf : Continuous f) :
    ∀ x, comap f g x = g (f x) := by
  intro x
  rw [← @Function.comp_apply _ _ _ g f x]
  rw [← coe_comap _ _ hf]

lemma comap_injective (f : X → Y) (hf: Continuous f)
    (hfs : Function.Surjective f) : Function.Injective
    ((LocallyConstant.comap f) : (LocallyConstant Y Z) → (LocallyConstant X Z)) := by
  intro a b h
  rw [LocallyConstant.ext_iff] at h
  ext y
  obtain ⟨x, hx⟩ := hfs y
  specialize h x
  rw [coe_comap_apply _ _ hf] at h
  rw [coe_comap_apply _ _ hf] at h
  rw [← hx]
  assumption

lemma isLocallyConstant_sum_elim {f : X → Z} {g : Y → Z} (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) : IsLocallyConstant (Sum.elim f g) := by
  let dZ : TopologicalSpace Z := ⊥
  haveI : DiscreteTopology Z := discreteTopology_bot Z
  rw [IsLocallyConstant.iff_continuous]
  rw [continuous_sum_elim, ← IsLocallyConstant.iff_continuous, ← IsLocallyConstant.iff_continuous]
  exact ⟨hf,hg⟩

def Sum (f : LocallyConstant X Z) (g : LocallyConstant Y Z) : LocallyConstant (X ⊕ Y) Z :=
{ toFun := Sum.elim f.toFun g.toFun
  isLocallyConstant := isLocallyConstant_sum_elim f.isLocallyConstant g.isLocallyConstant }

noncomputable
def SumEquivProd : LocallyConstant (X ⊕ Y) Z ≃ LocallyConstant X Z × LocallyConstant Y Z :=
{ toFun := fun f ↦ (f.comap Sum.inl, f.comap Sum.inr)
  invFun := fun f ↦ LocallyConstant.Sum f.1 f.2
  left_inv := by
    intro _
    ext x
    dsimp [Sum]
    rw [coe_comap _ _ continuous_inl, coe_comap _ _ continuous_inr]
    cases x
    · dsimp
    · dsimp
  right_inv := by
    intro _
    ext
    · dsimp
      rw [coe_comap_apply _ _ continuous_inl]
      rfl
    · dsimp
      rw [coe_comap_apply _ _ continuous_inr]
      rfl }

lemma closure_compl_subset {C₁ C₂ : Set X} (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ) : closure (C₁ᶜ) ⊆ C₂ := by
  have h' := Set.compl_subset_iff_union.mpr h
  rwa [← h₂.closure_subset_iff] at h'

lemma frontier_subset_inter {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ) : (C₁ ∪ C₂) ∩ (frontier C₁) ⊆ C₁ ∩ C₂ := by
  intro x hx
  rw [h] at hx
  simp only [Set.univ_inter] at hx
  rw [h₁.frontier_eq, Set.diff_eq_compl_inter] at hx
  rw [← @closure_compl _ _ C₁] at hx
  have h' := Set.compl_subset_iff_union.mpr h
  rw [← h₂.closure_subset_iff] at h'
  exact ⟨hx.2, h' hx.1⟩

open Classical

lemma isLocallyConstant_piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ)
    (f : LocallyConstant {i // i ∈ C₁} Z)
    (g : LocallyConstant {i // i ∈ C₂} Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f.toFun ⟨x, hx.1⟩ = g.toFun ⟨x, hx.2⟩)
    (junk : Z) : IsLocallyConstant (C₁.piecewise' f.toFun g.toFun junk) := by
  let dZ : TopologicalSpace Z := ⊥
  haveI : DiscreteTopology Z := discreteTopology_bot Z
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  rw [IsLocallyConstant.iff_continuous] at hf hg ⊢
  dsimp
  rw [continuous_iff_continuousOn_univ]
  rw [← h]
  dsimp [Set.piecewise']
  apply ContinuousOn.piecewise
  · intro x hx
    specialize hfg x (frontier_subset_inter h₁ h₂ h hx)
    dsimp [Function.ExtendBy]
    split_ifs with hh₁ hh₂
    · exact hfg
    · exfalso
      exact hh₂ (frontier_subset_inter h₁ h₂ h hx).2
    · exfalso
      exact hh₁ (frontier_subset_inter h₁ h₂ h hx).1
    · rfl
  · rw [h₁.closure_eq, h]
    simp only [Set.univ_inter]
    rw [continuousOn_iff_continuous_restrict]
    rwa [f.restrict_extendBy_eq_self junk]
  · rw [h]
    simp only [Set.univ_inter]
    apply ContinuousOn.mono _ (closure_compl_subset h₂ h)
    rw [continuousOn_iff_continuous_restrict]
    rwa [g.restrict_extendBy_eq_self junk]

noncomputable
def piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ)
    (f : LocallyConstant {i // i ∈ C₁} Z)
    (g : LocallyConstant {i // i ∈ C₂} Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f.toFun ⟨x, hx.1⟩ = g.toFun ⟨x, hx.2⟩)
    (junk : Z) : LocallyConstant X Z :=
{ toFun := C₁.piecewise' f.toFun g.toFun junk
  isLocallyConstant := isLocallyConstant_piecewise h₁ h₂ h f g hfg junk}

noncomputable
def ExtendBy {C : Set X} (hC : IsClopen C) (f : LocallyConstant {i // i ∈ C} Z) (junk : Z) :
    LocallyConstant X Z :=
{ toFun := f.toFun.ExtendBy junk
  isLocallyConstant := by
    intro s
    by_cases hj : junk ∈ s
    · rw [Function.extendBy_preimage_of_junk_mem _ _ _ hj]
      refine' IsOpen.union _ hC.compl.1
      exact IsOpen.isOpenMap_subtype_val hC.1 (f.toFun ⁻¹' s) (f.isLocallyConstant s)
    · rw [Function.extendBy_preimage_of_junk_ne_mem _ _ _ hj]
      exact IsOpen.isOpenMap_subtype_val hC.1 (f.toFun ⁻¹' s) (f.isLocallyConstant s)   }

variable {R : Type _} [Ring R] [AddCommMonoid Z] [Module R Z]

noncomputable
def comapLinear (f : X → Y) (hf : Continuous f) : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z :=
{ toFun := comap f
  map_add' := by
    intro r s
    ext x
    simp
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rfl
  map_smul' := by
    intro r s
    dsimp
    ext x
    simp
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rfl }

lemma comapLinear_injective (f : X → Y) (hf : Continuous f) (hfs : Function.Surjective f) :
    LinearMap.ker (comapLinear f hf : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z) = ⊥ := by
  apply LinearMap.ker_eq_bot_of_injective
  dsimp [comapLinear]
  exact comap_injective _ hf hfs

noncomputable
def equivLinear (e : X ≃ₜ Y) : LocallyConstant X Z ≃ₗ[R] LocallyConstant Y Z :=
{ toFun := (equiv e).toFun
  map_smul' := (comapLinear _ e.continuous_invFun).map_smul'
  map_add' := by -- why doesn't (comapLinear _ e.continuous_invFun).map_add' work?
    intro r s
    ext x
    dsimp [equiv]
    have hf : Continuous ↑(e.symm) := e.continuous_invFun
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rfl
  invFun := (equiv e).invFun
  left_inv := (equiv e).left_inv
  right_inv := (equiv e).right_inv }

noncomputable
def LinearSumEquivProd : LocallyConstant (X ⊕ Y) Z ≃ₗ[R] LocallyConstant X Z × LocallyConstant Y Z :=
{ toFun := SumEquivProd.toFun
  map_smul' := by
    intro r f
    ext x
    · dsimp [SumEquivProd]
      rw [coe_comap _ _ continuous_inl, coe_comap_apply _ _ continuous_inl]
      dsimp
    · dsimp [SumEquivProd]
      rw [coe_comap _ _ continuous_inr, coe_comap_apply _ _ continuous_inr]
      dsimp
  map_add' := by
    intro f g
    ext x
    · dsimp [SumEquivProd]
      rw [coe_comap _ _ continuous_inl, coe_comap_apply _ _ continuous_inl,
        coe_comap_apply _ _ continuous_inl]
      dsimp
    · dsimp [SumEquivProd]
      rw [coe_comap _ _ continuous_inr, coe_comap_apply _ _ continuous_inr,
        coe_comap_apply _ _ continuous_inr]
      dsimp
  invFun := SumEquivProd.invFun
  left_inv := SumEquivProd.left_inv
  right_inv := SumEquivProd.right_inv }

end LocallyConstant

namespace List
namespace Lex

variable {α : Type u} {r : α → α → Prop}

lemma singleton_iff (a b : α) : r a b ↔ List.Lex r [a] [b] := by
  refine' ⟨List.Lex.rel,_⟩
  intro h
  by_contra h'
  cases h
  · apply not_nil_right r []
    assumption
  · apply h'
    assumption

lemma nil_le (l : List α) : List.Lex r [] l ∨ [] = l := by
  induction l with
  | nil =>
    right
    rfl
  | cons a as _ =>
    left
    apply nil

end Lex
end List

namespace NobelingProof

variable {I : Type u} [LinearOrder I] [IsWellOrder I (·<·)] (C : Set ((WithTop I) → Bool))

def BoolToZ : Bool → ℤ := (if · then 1 else 0)

variable (I)

def r : (I → Bool) → (WithTop I) → Bool := fun f i ↦ if let some a := i then f a else false

lemma r.embedding : ClosedEmbedding (r I) := by
  apply Continuous.closedEmbedding
  · apply continuous_pi
    intro i
    dsimp [r]
    cases i
    · exact continuous_const
    · exact continuous_apply _
  · intros f g hfg
    ext i
    exact congr_fun hfg i

variable {I}

def e (μ : WithTop I) : LocallyConstant {i // i ∈ C} ℤ :=
{ toFun := fun f ↦ BoolToZ (f.1 μ)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_continuous]
    refine' @Continuous.comp _ _ _ _ _ _ BoolToZ _ continuous_of_discreteTopology _
    refine' Continuous.comp (continuous_apply μ) _
    exact continuous_induced_dom }

def Products (I : Type _) [LinearOrder I] := {l : List I // l.Chain' (·>·)}

noncomputable
instance : LinearOrder (Products (WithTop I)) :=
  inferInstanceAs (LinearOrder {l : List (WithTop I) // l.Chain' (·>·)})

lemma ltIffLex (l m : Products (WithTop I)) : l < m ↔ List.Lex (·<·) l.val m.val := by
  cases l
  cases m
  rw [Subtype.mk_lt_mk]
  simp
  exact Iff.rfl

lemma transLex (l m k : List (WithTop I)) (hlm : List.Lex (·<·) l m) (hmk : List.Lex (·<·) m k) :
    List.Lex (·<·) l k :=
  (inferInstance : IsTrans (List (WithTop I)) (List.Lex (·<·))).trans _ _ _ hlm hmk

def Products.eval (l : Products (WithTop I)) := (l.1.map (e C)).prod

def Products.isGood (l : Products (WithTop I)) : Prop :=
  l.eval C ∉ Submodule.span ℤ ((Products.eval C) '' {m | m < l})

def GoodProducts := {l : Products (WithTop I) | l.isGood C}

def GoodProducts.eval (l : {l : Products (WithTop I) // l.isGood C}) :
  LocallyConstant {i // i ∈ C} ℤ := Products.eval C l.1

lemma GoodProducts.injective : Function.Injective (eval C) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  dsimp [eval] at h
  have hab : a < b ∨ a = b ∨ b < a := trichotomous_of (·<·) a b
  apply Or.elim3 hab
  · intro h'
    exfalso
    apply hb
    rw [← h]
    apply Submodule.subset_span
    use a
    exact ⟨h',rfl⟩
  · exact fun h ↦ Subtype.eq h
  · intro h'
    exfalso
    apply ha
    rw [h]
    apply Submodule.subset_span
    use b
    exact ⟨h',rfl⟩

def ModProducts := Set.range (GoodProducts.eval C)

noncomputable
def GoodProducts.equiv_modProducts : GoodProducts C ≃ ModProducts C :=
Equiv.ofInjective (eval C) (injective C)

lemma GoodProducts.equiv_toFun_eq_eval : (equiv_modProducts C).toFun =
  Set.rangeFactorization (eval C) := by rfl

lemma GoodProducts.linear_independent_iff : LinearIndependent ℤ (GoodProducts.eval C) ↔
    LinearIndependent ℤ (fun (p : ModProducts C) ↦ p.1) := by
  rw [← @Set.rangeFactorization_eq _ _ (GoodProducts.eval C), ← equiv_toFun_eq_eval C]
  exact linearIndependent_equiv (equiv_modProducts C)

def Support : Set (WithTop I) := {i : WithTop I | ∃ f ∈ C, f i}

def P (i : WithTop I) : Prop :=
∀ C, IsClosed C → Support C ⊆ {j | j < i} → LinearIndependent ℤ (GoodProducts.eval C)

def Q (i : WithTop I) : Prop :=
∀ C, IsClosed C → Support C ⊆ {j | j < i} → ⊤ ≤ Submodule.span ℤ (Set.range (GoodProducts.eval C))

variable (I)

def ord (i : WithTop I) : Ordinal := Ordinal.typein ((·<·) : WithTop I → WithTop I → Prop) i

noncomputable
def term {o : Ordinal} (ho : o < Ordinal.type ((·<·) : WithTop I → WithTop I → Prop)) :
    WithTop I := Ordinal.enum ((·<·) : WithTop I → WithTop I → Prop) o ho

def P' (o : Ordinal) : Prop :=
∀ C, IsClosed C → Support C ⊆ {j : WithTop I | ord I j < o} →
  LinearIndependent ℤ (GoodProducts.eval C)

def Q' (o : Ordinal) : Prop :=
o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop) →
  ∀ C, IsClosed C → Support C ⊆ {j : WithTop I | ord I j < o} →
  ⊤ ≤ Submodule.span ℤ (Set.range (GoodProducts.eval C))

lemma PsetEq (i : WithTop I) : {j : WithTop I | ord I j < ord I i} = {j : WithTop I | j < i} := by
  ext x
  dsimp [ord]
  simp only [Ordinal.typein_lt_typein]

lemma PIffP (i : WithTop I) : P i ↔ P' I (ord I i) := by
  dsimp [P, P']
  rw [PsetEq]

lemma ord_le_type (i : WithTop I) :
    ord I i ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop) := by
  dsimp [ord]
  exact le_of_lt (Ordinal.typein_lt_type _ _)

lemma QIffQ (i : WithTop I) :
    Q i ↔ Q' I (ord I i) := by
  dsimp [Q, Q']
  rw [PsetEq]
  refine' ⟨_,_⟩
  · intro h _
    exact h
  · intro h
    exact h (ord_le_type _ _)

variable {I}

instance : IsWellFounded (WithTop I) (·<·) := inferInstance

instance : IsEmpty { i // i ∈ (∅ : Set (WithTop I → Bool)) } := by
  simp only [Set.mem_empty_iff_false, isEmpty_subtype, forall_const]

instance : ¬ Nontrivial (LocallyConstant { i // i ∈ (∅ : Set (WithTop I → Bool)) } ℤ) := by
  rw [nontrivial_iff]
  push_neg
  intros f g
  ext x
  exact isEmptyElim x

instance : Subsingleton (LocallyConstant { i // i ∈ (∅ : Set (WithTop I → Bool)) } ℤ) := by
  rw [subsingleton_iff]
  intros f g
  ext x
  exact isEmptyElim x

instance GoodProducts.emptyEmpty :
    IsEmpty { l // Products.isGood (∅ : Set (WithTop I → Bool)) l } := by
  rw [isEmpty_iff]
  rintro ⟨l, hl⟩
  dsimp [Products.isGood] at hl
  apply hl
  have h : Products.eval ∅ l = 0 := subsingleton_iff.mp inferInstance _ 0
  rw [h]
  exact Submodule.zero_mem _

lemma GoodProducts.linearIndependentEmpty :
    LinearIndependent ℤ (eval (∅ : Set (WithTop I → Bool))) := by
  exact linearIndependent_empty_type

lemma GoodProducts.spanEmpty :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval (∅ : Set (WithTop I → Bool)))) := by
  rw [top_le_iff]
  rw [Submodule.eq_bot_of_subsingleton ⊤]
  rw [Submodule.eq_bot_of_subsingleton (Submodule.span ℤ (Set.range (eval ∅)))]


noncomputable
def el (o : Ordinal) : WithTop I := if h : o < Ordinal.type ((·<·) : WithTop I → WithTop I → Prop)
  then Ordinal.enum _ o h else ⊤

lemma zeroLTTop : 0 < Ordinal.type ((·<·) : WithTop I → WithTop I → Prop) := by
  rw [Ordinal.pos_iff_ne_zero]
  intro h
  simp only [Ordinal.type_eq_zero_iff_isEmpty, not_isEmpty_of_nonempty] at h

noncomputable
def ezero: Products (WithTop I) := ⟨[el 0], by simp only [List.chain'_singleton]⟩

def enil : Products (WithTop I) := ⟨[], by simp only [List.chain'_nil]⟩

lemma elZeroIsBot (i : WithTop I) : el 0 ≤ i := by
  have h₁ : 0 < Ordinal.type ((·<·) : WithTop I → WithTop I → Prop)
  · rw [Ordinal.pos_iff_ne_zero]
    intro h
    rw [Ordinal.type_eq_zero_iff_isEmpty] at h
    simp only [not_isEmpty_of_nonempty] at h
  have : el 0 = Ordinal.enum ((·<·) : WithTop I → WithTop I → Prop) 0 h₁
  · dsimp [el]
    rw [dite_eq_iff]
    left
    use h₁
  · rw [this]
    have h := Ordinal.enum_zero_le h₁ i
    simp only [not_lt] at h
    assumption

lemma leEzeroSingleton : { m : Products (WithTop I) | m < ezero} = {⟨[], List.chain'_nil⟩ } := by
  ext ⟨m, hm⟩
  refine' ⟨_,_⟩
  · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [ltIffLex]
    dsimp [ezero]
    intro h
    apply Subtype.eq
    dsimp
    induction m with
    | nil => rfl
    | cons i m _ =>
      simp
      by_cases hi : el 0 = i
      · rw [hi, List.Lex.cons_iff] at h
        exact List.Lex.not_nil_right _ _ h
      · have : List.Lex (·<·) [el 0] [i]
        · rw [← List.Lex.singleton_iff]
          rw [lt_iff_le_and_ne]
          exact ⟨elZeroIsBot i, hi⟩
        · have ht : List.Lex (·<·) (i :: m) [i] := transLex _ _ _ h this
          rw [List.Lex.cons_iff] at ht
          exact List.Lex.not_nil_right _ _ ht
  · simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [ltIffLex]
    dsimp [ezero]
    intro h
    cases h
    exact List.nil_lt_cons _ _

lemma leEnilEmpty : { m : Products (WithTop I) | m < enil } = ∅ := by
  ext ⟨m, hm⟩
  refine' ⟨_,(by tauto)⟩
  rintro h
  · simp at h
    rw [ltIffLex] at h
    dsimp [enil] at h
    simp only [Set.mem_empty_iff_false]
    apply List.Lex.not_nil_right _ _ h

instance {α : Type _} [TopologicalSpace α] [Inhabited α] : Nontrivial (LocallyConstant α ℤ) := by
  use 0
  use 1
  intro h
  rw [LocallyConstant.ext_iff] at h
  apply @zero_ne_one ℤ
  exact h default

lemma evalEnilNeZero : Products.eval ({fun _ ↦ false} : Set (WithTop I → Bool)) enil ≠ 0 := by
  dsimp [Products.eval]
  exact one_ne_zero

lemma nilIsGood : Products.isGood ({fun _ ↦ false} : Set (WithTop I → Bool)) enil:= by
  intro h
  rw [leEnilEmpty] at h
  simp at h
  apply evalEnilNeZero h

lemma nilSpanTop :
    Submodule.span ℤ (Products.eval ({fun _ ↦ false} : Set (WithTop I → Bool)) '' {enil}) = ⊤ := by
  simp only [Set.image_singleton]
  dsimp [enil, Products.eval]
  rw [eq_top_iff]
  rintro f _
  rw [Submodule.mem_span]
  intro p h₁
  simp at h₁
  have : f = (f default) • (1 : LocallyConstant _ ℤ)
  · ext x
    have hd : x = default := by simp only [Set.default_coe_singleton, eq_iff_true_of_subsingleton]
    rw [hd]
    simp
    rfl
  rw [this]
  apply Submodule.smul_mem
  exact h₁

noncomputable
instance GoodProducts.singletonUnique :
  Unique { l // Products.isGood ({fun _ ↦ false} : Set (WithTop I → Bool)) l } :=
{ default := ⟨enil, nilIsGood⟩
  uniq := by
    rintro ⟨⟨l, hl⟩, hll⟩
    dsimp [default]
    ext
    dsimp [enil]
    apply Subtype.eq
    dsimp
    have : [] < l ∨ [] = l  := List.Lex.nil_le l
    cases this
    · exfalso
      apply hll
      have he : {enil} ⊆ {m | m < ⟨l,hl⟩ }
      · simp
        dsimp [enil]
        rw [Subtype.mk_lt_mk]
        assumption
      have hpe : Products.eval ({fun _ ↦ false} : Set (WithTop I → Bool)) '' {enil} ⊆
        Products.eval _ '' {m | m < ⟨l,hl⟩ } := Set.image_subset _ he
      apply Submodule.span_mono hpe
      rw [nilSpanTop]
      exact Submodule.mem_top
    · exact Eq.symm (by assumption) }

instance (α : Type _) [TopologicalSpace α] : NoZeroSMulDivisors ℤ (LocallyConstant α ℤ) := by
  constructor
  intro c f h
  by_cases hc : c = 0
  · left
    assumption
  · right
    ext x
    rw [LocallyConstant.ext_iff] at h
    apply_fun fun (y : ℤ) ↦ c * y
    · simp at h
      simp
      exact h x
    · exact mul_right_injective₀ hc

lemma GoodProducts.linearIndependentSingleton :
    LinearIndependent ℤ (eval ({fun _ ↦ false} : Set (WithTop I → Bool))) :=
  linearIndependent_unique (eval ({fun _ ↦ false} : Set (WithTop I → Bool))) evalEnilNeZero

lemma GoodProducts.spanSingleton :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval ({fun _ ↦ false} : Set (WithTop I → Bool)))) := by
  have hpe : Products.eval ({fun _ ↦ false} : Set (WithTop I → Bool)) '' {enil} ⊆
    (Set.range (eval ({fun _ ↦ false} : Set (WithTop I → Bool))))
  · dsimp [eval]
    simp only [Set.image_singleton, Set.singleton_subset_iff, Set.mem_range,
      Subtype.exists, exists_prop]
    use enil
    exact ⟨nilIsGood, rfl⟩
  refine' le_trans _ (Submodule.span_mono hpe)
  rw [nilSpanTop]

noncomputable
def SwapTrue (o : Ordinal) : (WithTop I → Bool) → WithTop I → Bool :=
fun f i ↦ if ord I i = o then true else f i

lemma continuous_swapTrue (o : Ordinal) :
    Continuous (SwapTrue o : (WithTop I → Bool) → WithTop I → Bool) := by
  refine' continuous_pi _
  intro i
  dsimp [SwapTrue]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

noncomputable
def SwapFalse (o : Ordinal) : (WithTop I → Bool) → WithTop I → Bool :=
fun f i ↦ if ord I i = o then false else f i

lemma continuous_swapFalse (o : Ordinal) :
    Continuous (SwapTrue o : (WithTop I → Bool) → WithTop I → Bool) := by
  refine' continuous_pi _
  intro i
  dsimp [SwapTrue]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

noncomputable
def ProjOrd (o : Ordinal) : (WithTop I → Bool) → (WithTop I → Bool) :=
  fun c i ↦ if ord I i < o then c i else false

lemma continuous_ProjOrd (o : Ordinal) :
    Continuous (ProjOrd o : (WithTop I → Bool) → (WithTop I → Bool)) := by
  refine' continuous_pi _
  intro i
  dsimp [ProjOrd]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma isClosedMap_projOrd (o : Ordinal) :
    IsClosedMap (ProjOrd o : (WithTop I → Bool) → (WithTop I → Bool)) :=
  fun _ hF ↦ (IsCompact.isClosed (hF.isCompact.image (continuous_ProjOrd o)))

def Res (o : Ordinal) : Set (WithTop I → Bool) := (ProjOrd o) '' C

lemma projOrdC {o : Ordinal} (h : Support C ⊆ {i | ord I i < o}) (f : WithTop I → Bool)
    (hf : f ∈ C) : f = ProjOrd o f := by
  dsimp [ProjOrd]
  ext x
  split_ifs with ho
  · rfl
  · dsimp [Support] at h
    simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp] at h
    specialize h x f hf
    rw [← not_imp_not] at h
    simp only [not_lt, Bool.not_eq_true] at h
    simp only [not_lt] at ho
    exact (h ho)

lemma supportResEq (o : Ordinal) (h : Support C ⊆ {i | ord I i < o}) : C = Res C o := by
  ext f
  constructor <;>
  rintro hf
  · use f
    exact ⟨hf, (projOrdC C h f hf).symm⟩
  · obtain ⟨g, hg⟩ := hf
    rw [← projOrdC C h g hg.1] at hg
    rw [← hg.2]
    exact hg.1

lemma isClosed_Res (o : Ordinal) (hC : IsClosed C) : IsClosed (Res C o) :=
  isClosedMap_projOrd o C hC

lemma support_Res_le_o (o : Ordinal) : Support (Res C o) ⊆ {j | ord I j < o} := by
  intro j hj
  dsimp [Support, Res, ProjOrd] at hj
  simp only [Set.mem_image, exists_exists_and_eq_and, Bool.ite_eq_true_distrib] at hj
  simp only [Set.mem_setOf_eq]
  obtain ⟨_, ⟨_, h⟩⟩ := hj
  split_ifs at h
  assumption

noncomputable
def ResOnSubset (o : Ordinal) : {i // i ∈ C} → {i // i ∈ Res C o} :=
fun ⟨i, h⟩ ↦ ⟨ProjOrd o i, Set.mem_image_of_mem _ h⟩

lemma resOnSubset_eq (o : Ordinal) : Subtype.val ∘ ResOnSubset C o =
    (ProjOrd o : (WithTop I → Bool) → _) ∘ Subtype.val := by
  rfl

lemma continuous_val_comp_ResOnSubset (o : Ordinal) :
    Continuous (Subtype.val ∘ ResOnSubset C o) := by
  rw [resOnSubset_eq _]
  exact Continuous.comp (continuous_ProjOrd o) continuous_subtype_val

lemma continuous_ResOnSubset (o : Ordinal) : Continuous (ResOnSubset C o) := by
  rw [continuous_induced_rng]
  exact continuous_val_comp_ResOnSubset _ _

lemma surjective_ResOnSubset (o : Ordinal) : Function.Surjective (ResOnSubset C o) := by
  rintro ⟨i, h⟩
  obtain ⟨b, hb⟩ := h
  dsimp [ResOnSubset]
  use ⟨b, hb.1⟩
  simp_rw [← hb.2]

lemma ResMono {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) {f : WithTop I → Bool}
    (hf : ProjOrd o₂ f ∈ Res C o₂) : ProjOrd o₁ f ∈ Res C o₁ := by
  obtain ⟨c,⟨_,hc⟩⟩  := hf
  dsimp [ProjOrd] at hc
  dsimp [Res, ProjOrd]
  use c
  refine' ⟨(by assumption),_⟩
  ext i
  dsimp
  have hc' := congr_fun hc i
  split_ifs
  · split_ifs at hc' with h₁
    · exact hc'
    · exfalso
      apply h₁ (lt_of_lt_of_le (by assumption) h)
  · rfl

-- noncomputable
-- def ResOnSubsetsLift (o : Ordinal) : {i // i ∈ Res C o} → {i // i ∈ C} :=
-- Function.surjInv (surjective_ResOnSubset C o)

-- noncomputable
-- def ProjOrdLift (o : Ordinal) (e : {i // i ∈ Res C o}) : (WithTop I → Bool) :=
-- Function.surjInv (surjective_ResOnSubset C o)

lemma ProjOrdSelf (o : Ordinal) {f : WithTop I → Bool} (hf : f ∈ Res C o) :
    ProjOrd o f = f := by
  dsimp [ProjOrd]
  ext i
  split_ifs
  · rfl
  · obtain ⟨c,hc⟩ := hf
    rw [←congr_fun hc.2 i]
    dsimp [ProjOrd]
    rw [eq_ite_iff]
    right
    exact ⟨(by assumption), (by rfl)⟩

lemma ResMono' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) {f : WithTop I → Bool}
    (hf : f ∈ Res C o₂) : ProjOrd o₁ f ∈ Res C o₁ := by
  rw [← ProjOrdSelf C o₂ hf] at hf
  exact ResMono C h hf

noncomputable
def ResOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : {i // i ∈ Res C o₂} → {i // i ∈ Res C o₁} :=
  fun e ↦ ⟨ProjOrd o₁ e.val, ResMono' C h e.property⟩

lemma resOnSubsets_eq {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : ResOnSubset C o₁ =
    ResOnSubsets C h ∘ ResOnSubset C o₂  := by
  ext e i
  dsimp [ResOnSubsets, ResOnSubset]
  dsimp [ProjOrd]
  split_ifs with h₁ h₂
  · rfl
  · exfalso
    apply h₂ (lt_of_lt_of_le h₁ h)
  · rfl

lemma continuous_ResOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : Continuous (ResOnSubsets C h) := by
  rw [continuous_induced_rng]
  exact continuous_val_comp_ResOnSubset (Res C o₂) o₁

lemma surjective_ResOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) :
    Function.Surjective (ResOnSubsets C h) := by
  apply @Function.Surjective.of_comp _ _ _ _ (ResOnSubset C o₂)
  rw [← resOnSubsets_eq C h]
  exact surjective_ResOnSubset _ _

lemma Products.evalCons {l : List (WithTop I)} {a : WithTop I}
    (hla : (a::l).Chain' (·>·)) : Products.eval C ⟨a::l,hla⟩ =
    (e C a) * Products.eval C ⟨l,List.Chain'.sublist hla (List.tail_sublist (a::l))⟩ := by
  dsimp [eval]
  simp only [List.prod_cons]

lemma chain'_cons_of_chain'_and_chain'_cons {l m : List (WithTop I)} {a : WithTop I} (hml : m < l)
    (hl : (a::l).Chain' (·>·)) (hm : m.Chain' (·>·)) : (a::m).Chain' (·>·) := by
  induction hml with
  | nil =>
    · simp only [List.chain'_singleton]
  | cons _ _ =>
    · simp only [List.chain'_cons]
      simp only [List.chain'_cons] at hl
      exact ⟨hl.1, by assumption⟩
  | rel h =>
    · simp only [gt_iff_lt, List.chain'_cons]
      simp only [gt_iff_lt, List.chain'_cons]  at hl
      exact ⟨lt_trans h hl.1, hm⟩

lemma Products.isGood_cons {l : List (WithTop I)} {a : WithTop I}
    (hla : (a::l).Chain' (·>·)) : isGood C ⟨a::l,hla⟩ →
    isGood C ⟨l,List.Chain'.sublist hla (List.tail_sublist (a::l))⟩ := by
  rw [← not_imp_not]
  intro h
  dsimp [isGood] at *
  simp only [not_not] at *
  rw [evalCons]
  rw [mem_span_set] at h
  obtain ⟨c, ⟨hc, hsum⟩⟩ := h
  rw [← hsum, Finsupp.mul_sum]
  simp_rw [mul_smul_comm]
  apply Submodule.finsupp_sum_mem
  intro f hf
  apply Submodule.smul_mem
  simp only [← Finsupp.mem_support_iff] at hf
  have := hc hf
  obtain ⟨⟨m,cm⟩,hm⟩ := this
  have hma : List.Chain' (·>·) (a :: m) := chain'_cons_of_chain'_and_chain'_cons hm.1 hla cm
  rw [← hm.2, ← evalCons C hma]
  apply Submodule.subset_span
  use ⟨a :: m, hma⟩
  refine' ⟨_,rfl⟩
  simp only [Set.mem_setOf_eq]
  apply List.Lex.cons
  exact hm.1

lemma eEqe {o₁ o₂ : Ordinal} {a : WithTop I} (ha : ord I a < o₁) (h : o₁ ≤ o₂) :
    e (Res C o₁) a ∘ ResOnSubsets C h = e (Res C o₂) a := by
  ext ⟨f,hf⟩
  dsimp [e, ResOnSubsets, BoolToZ, ProjOrd]
  split_ifs
  · rfl
  · rfl

lemma eEqeC {o : Ordinal} {a : WithTop I} (ha : ord I a < o) :
    e (Res C o) a ∘ ResOnSubset C o = e C a := by
  ext ⟨f,hf⟩
  dsimp [e, ResOnSubset, BoolToZ, ProjOrd]
  split_ifs
  · rfl
  · rfl

lemma eEqe_apply {o₁ o₂ : Ordinal} {a : WithTop I} (ha : ord I a < o₁) (h : o₁ ≤ o₂) :
    ∀ x, (e (Res C o₁) a) ((ResOnSubsets C h) x) = e (Res C o₂) a x := by
  intro x
  exact congr_fun (eEqe C ha h) x

lemma eEqe_applyC {o : Ordinal} {a : WithTop I} (ha : ord I a < o) :
    ∀ x, (e (Res C o) a) ((ResOnSubset C o) x) = e C a x := by
  intro x
  exact congr_fun (eEqeC C ha) x

lemma Products.evalFac {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o₁) :
    l.eval (Res C o₁) ∘ ResOnSubsets C h = l.eval (Res C o₂) := by
  obtain ⟨l, hl⟩ := l
  induction l with
  | nil => rfl
  | cons a as ih =>
    · ext ⟨f, hf⟩
      rw [evalCons (Res C o₁) hl]
      rw [evalCons (Res C o₂) hl]
      dsimp
      specialize hlhead (List.cons_ne_nil a as)
      dsimp at hlhead
      rw [eEqe_apply C hlhead h _]
      specialize ih (List.Chain'.sublist hl (List.tail_sublist (a::as)))
      dsimp at ih
      congr! 1
      by_cases has : as = []
      · simp_rw [has]
        rfl
      · have : ord I (List.head! as) < o₁
        · rw [← List.cons_head!_tail has] at hl
          refine' lt_trans _ hlhead
          dsimp [ord]
          simp only [Ordinal.typein_lt_typein]
          have := List.Chain'.rel_head hl
          simp only [gt_iff_lt] at this
          exact this
        exact congr_fun (ih (fun _ ↦ this)) _

lemma Products.evalFacC {l : Products (WithTop I)} {o : Ordinal}
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o) :
    l.eval (Res C o) ∘ ResOnSubset C o = l.eval C := by
  obtain ⟨l, hl⟩ := l
  induction l with
  | nil => rfl
  | cons a as ih =>
    · ext ⟨f, hf⟩
      rw [evalCons (Res C o) hl]
      rw [evalCons C hl]
      dsimp
      specialize hlhead (List.cons_ne_nil a as)
      dsimp at hlhead
      rw [eEqe_applyC C hlhead]
      specialize ih (List.Chain'.sublist hl (List.tail_sublist (a::as)))
      dsimp at ih
      congr! 1
      by_cases has : as = []
      · simp_rw [has]
        rfl
      · have : ord I (List.head! as) < o
        · rw [← List.cons_head!_tail has] at hl
          refine' lt_trans _ hlhead
          dsimp [ord]
          simp only [Ordinal.typein_lt_typein]
          have := List.Chain'.rel_head hl
          simp only [gt_iff_lt] at this
          exact this
        exact congr_fun (ih (fun _ ↦ this)) _


lemma Products.head_lt_ord_of_isGood {l : Products (WithTop I)} {o : Ordinal}
    (h : l.isGood (Res C o)) : l.val ≠ [] → ord I (l.val.head!) < o := by
  intro hn
  by_contra h'
  apply h
  obtain ⟨l,hl⟩ := l
  dsimp at hn
  have hl' : List.Chain' (·>·) (l.head! :: l.tail)
  · rw [List.cons_head!_tail hn]
    exact hl
  have : (⟨l,hl⟩ : Products (WithTop I)) = ⟨l.head! :: l.tail, hl'⟩
  · simp_rw [List.cons_head!_tail hn]
  rw [this, evalCons (Res C o) hl']
  have eZero : e (Res C o) (List.head! l) = 0
  · dsimp [e]
    ext ⟨f,hf⟩
    dsimp [BoolToZ]
    dsimp [Res, ProjOrd] at hf
    obtain ⟨g, hg⟩ := hf
    rw [← hg.2]
    split_ifs
    · exfalso
      assumption
    · rfl
    · exfalso
      assumption
    · rfl
  rw [eZero]
  simp only [zero_mul, Submodule.zero_mem]

lemma Products.goodEvalFac {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) : l.eval (Res C o₁) ∘ ResOnSubsets C h = l.eval (Res C o₂) :=
  evalFac C h (head_lt_ord_of_isGood C hl)

lemma Products.goodEvalFacC {l : Products (WithTop I)} {o : Ordinal}
    (hl : l.isGood (Res C o)) : l.eval (Res C o) ∘ ResOnSubset C o = l.eval C :=
  evalFacC C (head_lt_ord_of_isGood C hl)

lemma Products.eval_comapFac {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) :
    LocallyConstant.comap (ResOnSubsets C h) (l.eval (Res C o₁)) = l.eval (Res C o₂) := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _)]
  exact congr_fun (goodEvalFac C h hl) _

lemma Products.eval_comapFacC {l : Products (WithTop I)} {o : Ordinal}
    (hl : l.isGood (Res C o)) :
    LocallyConstant.comap (ResOnSubset C o) (l.eval (Res C o)) = l.eval C := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
  exact congr_fun (goodEvalFacC C hl) _

lemma Products.eval_comapFac' {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o₁) :
    LocallyConstant.comap (ResOnSubsets C h) (l.eval (Res C o₁)) = l.eval (Res C o₂) := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _)]
  exact congr_fun (evalFac C h hlhead) _

lemma Products.eval_comapFac'C {l : Products (WithTop I)} {o : Ordinal}
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o) :
    LocallyConstant.comap (ResOnSubset C o) (l.eval (Res C o)) = l.eval C := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
  exact congr_fun (evalFacC C hlhead) _

-- lemma Products.eval_comapFac'_set {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
--     (hlhead : l.val ≠ [] → ord I (l.val.head!) < o₁) :
--     ∀ s, (LocallyConstant.comap (ResOnSubsets C h) (eval (Res C o₁))) '' s =
--     eval (Res C o₂) '' s := by
--   intro s
--   rw [eval_comapFac' _ _ hlhead]

lemma Products.lt_ord {l m : Products (WithTop I)} {o : Ordinal} (hmltl : m < l)
    (hlhead : l.val ≠ [] → ord I l.val.head! < o) : m.val ≠ [] → ord I m.val.head! < o := by
  intro hm
  rw [ltIffLex] at hmltl
  by_cases hl : l.val = []
  · exfalso
    rw [hl] at hmltl
    exact List.Lex.not_nil_right _ _ hmltl
  · suffices hml : m.val.head! ≤ l.val.head!
    · refine' lt_of_le_of_lt _ (hlhead hl)
      dsimp [ord]
      simp only [Ordinal.typein_le_typein, not_lt]
      exact hml
    rw [← List.cons_head!_tail hl] at hmltl
    rw [← List.cons_head!_tail hm] at hmltl
    by_contra hn
    simp only [not_le] at hn
    have hml : List.Lex (·<·) (l.val.head! :: l.val.tail) (m.val.head! :: m.val.tail) :=
      List.Lex.rel hn
    exact List.Lex.isAsymm.aux _ _ _ hml hmltl

lemma Products.eval_comapFacImage {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) : eval (Res C o₂) '' { m | m < l } =
    (LocallyConstant.comapLinear (ResOnSubsets C h) (continuous_ResOnSubsets _ _) :
    LocallyConstant {i // i ∈ Res C o₁} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ Res C o₂} ℤ) ''
    (eval (Res C o₁) '' { m | m < l }) := by
  dsimp [LocallyConstant.comapLinear]
  ext f
  constructor <;>
  rintro hf
  · obtain ⟨m,hm⟩ := hf
    rw [← eval_comapFac' C h (lt_ord hm.1 (head_lt_ord_of_isGood C hl))] at hm
    rw [← hm.2]
    simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
    use m
    exact ⟨hm.1, by rfl⟩
  · rw [← Set.image_comp] at hf
    obtain ⟨m,hm⟩ := hf
    dsimp at hm
    rw [eval_comapFac' C h (Products.lt_ord hm.1 (head_lt_ord_of_isGood C hl))] at hm
    rw [← hm.2]
    simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
    use m
    exact ⟨hm.1, by rfl⟩

lemma Products.isGoodMono {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) : l.isGood (Res C o₂) := by
  dsimp [isGood] at *
  intro h'
  apply hl
  rw [eval_comapFacImage C h hl] at h'
  simp only [Submodule.span_image, Submodule.mem_map] at h'
  obtain ⟨y, ⟨hy₁,hy₂⟩ ⟩ := h'
  dsimp [LocallyConstant.comapLinear] at hy₂
  rw [← eval_comapFac C h hl] at hy₂
  have hy := LocallyConstant.comap_injective _ (continuous_ResOnSubsets C h)
    (surjective_ResOnSubsets C h) hy₂
  subst hy
  assumption

lemma GoodProducts.evalFac {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) : eval (Res C o₂) ⟨l, (Products.isGoodMono C h hl)⟩ =
    eval (Res C o₁) ⟨l, hl⟩ ∘ ResOnSubsets C h :=
  (Products.goodEvalFac C h hl).symm

lemma GoodProducts.lin_smaller (o : Ordinal) : LinearIndependent ℤ (eval (Res C o)) ↔
    LinearIndependent ℤ ((LocallyConstant.comapLinear
    (ResOnSubset C o) (continuous_ResOnSubset C o) : LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ]
    LocallyConstant {i // i ∈ C} ℤ) ∘ (eval (Res C o))) :=
  (LinearMap.linearIndependent_iff (LocallyConstant.comapLinear
    (ResOnSubset C o) (continuous_ResOnSubset C o))
    (LocallyConstant.comapLinear_injective _ _ (surjective_ResOnSubset C o))).symm

def ModProducts.smaller (o : Ordinal) : Set (LocallyConstant {i // i ∈ C} ℤ) :=
  (LocallyConstant.comapLinear
    (ResOnSubset C o) (continuous_ResOnSubset C o) : LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ]
    LocallyConstant {i // i ∈ C} ℤ) '' (ModProducts (Res C o))

instance [Nonempty C] : Inhabited (Res C 0) := by
  use (fun _ ↦ false)
  dsimp [Res]
  have : C.Nonempty
  · rw [← Set.nonempty_coe_sort]
    assumption
  obtain ⟨x,hx⟩ := this
  use x
  refine' ⟨hx,_⟩
  dsimp [ProjOrd]
  ext i
  split_ifs with h
  · exfalso
    exact Ordinal.not_lt_zero _ h
  · rfl

instance [Nonempty C] : Nontrivial (LocallyConstant {i // i ∈ C} ℤ) := by
  use 0
  use 1
  intro h
  rw [LocallyConstant.ext_iff] at h
  apply @zero_ne_one ℤ
  have : C.Nonempty
  · rw [← Set.nonempty_coe_sort]
    assumption
  obtain ⟨x,hx⟩ := this
  exact h ⟨x,hx⟩

lemma evalEnilNeZeroAny [Nonempty C] : enil.eval C ≠ 0 := by
  dsimp [Products.eval]
  exact one_ne_zero

lemma nilIsGoodAny [Nonempty C] : Products.isGood C enil := by
  intro h
  rw [leEnilEmpty] at h
  simp at h
  apply evalEnilNeZeroAny C h

instance [Nonempty C] (o : Ordinal) : Nonempty (Res C o) := by
  have : C.Nonempty
  · rw [← Set.nonempty_coe_sort]
    assumption
  rw [Set.nonempty_coe_sort]
  obtain ⟨x,hx⟩ := this
  use ProjOrd o x
  dsimp [Res]
  use x
  exact ⟨hx, by rfl⟩

open Classical

lemma Products.limitOrdinal [Nonempty C] {o : Ordinal} (ho : o.IsLimit) (l : Products (WithTop I)) :
    l.isGood (Res C o) ↔ ∃ (o' : Ordinal), o' < o ∧ l.isGood (Res C o') := by
  constructor <;>
  rintro h
  · dsimp [Ordinal.IsLimit] at ho
    obtain ⟨l, hl⟩ := l
    induction l with
    | nil =>
      · have ho' : o ≠ 0 := ho.1
        rw [← Ordinal.pos_iff_ne_zero] at ho'
        use 0
        exact ⟨ho', nilIsGoodAny _⟩
    | cons a as _ =>
      · have := Products.head_lt_ord_of_isGood C h (List.cons_ne_nil a as)
        simp only [List.head!_cons] at this
        let o₁ := Order.succ (ord I a)
        use o₁
        refine' ⟨ho.2 _ this,_⟩
        dsimp [isGood]
        dsimp [isGood] at h
        intro he
        apply h
        have hlhead : (⟨a :: as,hl⟩ : Products (WithTop I)).val ≠ [] →
            ord I (List.head! (⟨a :: as,hl⟩ : Products (WithTop I)).val) < Order.succ (ord I a)
        · intro
          simp only [List.head!_cons, Order.lt_succ_iff_not_isMax, not_isMax, not_false_eq_true]
        rw [← eval_comapFac' C (le_of_lt (ho.2 (ord I a) this)) hlhead]
        rw [mem_span_set] at he
        obtain ⟨c, ⟨hc, hsum⟩⟩ := he
        rw [mem_span_set]
        use Finsupp.mapDomain (LocallyConstant.comap
          (ResOnSubsets C (le_of_lt (ho.2 (ord I a) this))) :
          LocallyConstant {i // i ∈ Res C o₁} ℤ → LocallyConstant {i // i ∈ Res C o} ℤ) c
        refine' ⟨_,_⟩
        · refine' (subset_trans Finsupp.mapDomain_support _) -- need "Classical" for decidability
          intro p hp
          simp only [Finset.image_val, Multiset.mem_dedup, Multiset.mem_map, Finset.mem_val] at hp
          obtain ⟨t,ht⟩ := hp
          have ht' := hc ht.1
          obtain ⟨y, hy⟩ := ht'
          rw [← hy.2] at ht
          rw [← ht.2]
          use y
          refine' ⟨hy.1,_⟩
          rw [← eval_comapFac']
          intro hnil
          obtain ⟨b, l', hbl⟩ := List.exists_cons_of_ne_nil hnil
          rw [hbl]
          simp only [List.head!_cons, Order.lt_succ_iff]
          dsimp [ord]
          simp only [Ordinal.typein_le_typein, not_lt]
          have hya : y.val < a :: as := hy.1
          rw [hbl] at hya
          cases hya
          · exact le_refl _
          · exact le_of_lt (by assumption)
        · rw [Finsupp.sum_mapDomain_index_inj
            (LocallyConstant.comap_injective _ (continuous_ResOnSubsets _ _)
            (surjective_ResOnSubsets _ _))]
          rw [← hsum]
          have hlin : LocallyConstant.comap (ResOnSubsets C (le_of_lt (ho.2 (ord I a) this))) =
              ↑(LocallyConstant.comapLinear (ResOnSubsets C (le_of_lt (ho.2 (ord I a) this)))
              (continuous_ResOnSubsets _ _) :
              LocallyConstant {i // i ∈ Res C o₁} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ Res C o} ℤ) :=
            rfl
          rw [hlin, map_finsupp_sum]
          apply Finsupp.sum_congr
          intro f _
          dsimp [LocallyConstant.comapLinear]
          ext a'
          dsimp
          rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _)]
          rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _)]
          rfl
  · obtain ⟨o',⟨ho',hl⟩⟩ := h
    exact isGoodMono C (le_of_lt ho') hl

lemma ModProducts.union {o : Ordinal} (ho : o.IsLimit) (hsC : Support C ⊆ {i | ord I i < o}) :
    ModProducts C = ⋃ (e : {o' // o' < o}), (smaller C e.val) := by
  by_cases hC : Nonempty C
  · ext p
    constructor <;>
    rintro hp
    · dsimp [smaller]
      dsimp [ModProducts] at *
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
      dsimp
      obtain ⟨⟨l,hl⟩,hp⟩ := hp
      rw [supportResEq C o hsC, Products.limitOrdinal C ho] at hl
      obtain ⟨o',ho'⟩ := hl
      use o'
      use ho'.1
      use GoodProducts.eval (Res C o') ⟨l,ho'.2⟩
      refine' ⟨_,_⟩
      · use l
        use ho'.2
      · dsimp [LocallyConstant.comapLinear]
        rw [← hp]
        dsimp [GoodProducts.eval]
        exact Products.eval_comapFacC C ho'.2
    · dsimp [ModProducts]
      simp at *
      obtain ⟨o', h⟩ := hp
      obtain ⟨f, hf⟩ := h.2
      obtain ⟨⟨⟨l, lc⟩, hl⟩, hlf⟩ := hf.1
      rw [← hlf] at hf
      rw [← hf.2]
      dsimp [LocallyConstant.comapLinear]
      use ⟨l,lc⟩
      constructor
      exact (Products.eval_comapFacC C hl).symm
      rw [supportResEq C o hsC]
      exact Products.isGoodMono C (le_of_lt h.1) hl
  · have : C = ∅
    · rw [Set.nonempty_coe_sort, Set.not_nonempty_iff_eq_empty] at hC
      assumption
    dsimp [ModProducts, smaller, LocallyConstant.comapLinear, Res]
    rw [this]
    haveI he : IsEmpty { l // Products.isGood (∅ : Set (WithTop I → Bool)) l } := inferInstance
    rw [@Set.range_eq_empty _ _ he (GoodProducts.eval ∅)]
    refine' Eq.symm _
    simp only [Set.iUnion_eq_empty, Set.image_eq_empty, Set.image_empty]
    intro e
    have hP : ProjOrd e.val '' (∅ : Set (WithTop I → Bool)) = ∅
    · simp only [Set.image_empty]
    rw [hP, @Set.range_eq_empty _ _ he (GoodProducts.eval ∅)]

def ModProducts.equiv {o : Ordinal} (ho : o.IsLimit) (hsC : Support C ⊆ {i | ord I i < o}) :
    ModProducts C ≃ ⋃ (e : {o' // o' < o}), (smaller C e.val) :=
  Equiv.Set.ofEq (union C ho hsC)

lemma ModProducts.equivFactorization {o : Ordinal} (ho : o.IsLimit)
    (hsC : Support C ⊆ {i | ord I i < o}) :
    (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) ∘ (equiv C ho hsC).toFun =
    (fun (p : ModProducts C) ↦ (p.1 : LocallyConstant {i // i ∈ C} ℤ)) := by
  rfl

lemma ModProducts.linear_independent_iff {o : Ordinal} (ho : o.IsLimit)
    (hsC : Support C ⊆ {i | ord I i < o}) : LinearIndependent ℤ (GoodProducts.eval C) ↔
    LinearIndependent ℤ (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) := by
  rw [GoodProducts.linear_independent_iff]
  rw [← equivFactorization C ho hsC]
  exact linearIndependent_equiv (equiv C ho hsC)

noncomputable
def ModProducts.equiv_smaller_toFun (o : Ordinal) : ModProducts (Res C o) → smaller C o :=
fun x ↦ ⟨(↑(LocallyConstant.comapLinear (ResOnSubset C o) (continuous_ResOnSubset _ _) :
    LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ) :
    LocallyConstant {i // i ∈ Res C o} ℤ → LocallyConstant {i // i ∈ C} ℤ) ↑x,
    by { dsimp [smaller] ; use x.val ; exact ⟨x.property, rfl⟩  } ⟩

lemma ModProducts.equiv_smaller_toFun_bijective (o : Ordinal) :
    Function.Bijective (equiv_smaller_toFun C o) := by
  refine' ⟨_,_⟩
  · intro a b hab
    dsimp [equiv_smaller_toFun, LocallyConstant.comapLinear] at hab
    ext1
    simp only [Subtype.mk.injEq] at hab
    exact LocallyConstant.comap_injective _ (continuous_ResOnSubset _ _)
      (surjective_ResOnSubset _ _) hab
  · rintro ⟨a,ha⟩
    obtain ⟨b,hb⟩ := ha
    use ⟨b,hb.1⟩
    dsimp [equiv_smaller_toFun]
    simp only [Subtype.mk.injEq]
    exact hb.2

noncomputable
def ModProducts.equiv_smaller (o : Ordinal) : ModProducts (Res C o) ≃ smaller C o :=
Equiv.ofBijective (equiv_smaller_toFun C o) (equiv_smaller_toFun_bijective C o)

lemma ModProducts.smaller_factorization (o : Ordinal) :
    (fun (p : smaller C o) ↦ p.1) ∘ (equiv_smaller C o).toFun =
    ↑(LocallyConstant.comapLinear (ResOnSubset C o) (continuous_ResOnSubset _ _) :
    LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ) ∘
    (fun (p : ModProducts (Res C o)) ↦ p.1) := by rfl

lemma ModProducts.smaller_linear_independent_iff (o : Ordinal) :
    LinearIndependent ℤ (GoodProducts.eval (Res C o)) ↔
    LinearIndependent ℤ (fun (p : smaller C o) ↦ p.1) := by
  rw [GoodProducts.linear_independent_iff]
  rw [← LinearMap.linearIndependent_iff (LocallyConstant.comapLinear (ResOnSubset C o)
        (continuous_ResOnSubset _ _) : LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ]
        LocallyConstant {i // i ∈ C} ℤ) (LocallyConstant.comapLinear_injective _
        (continuous_ResOnSubset _ _) (surjective_ResOnSubset _ _))]
  rw [← smaller_factorization C o]
  exact linearIndependent_equiv _

lemma ModProducts.smaller_mono {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : smaller C o₁ ⊆ smaller C o₂ := by
  intro f hf
  dsimp [smaller, LocallyConstant.comapLinear] at *
  obtain ⟨g, hg⟩ := hf
  simp only [Set.mem_image]
  use LocallyConstant.comap (ResOnSubsets C h) g
  refine' ⟨_,_⟩
  · dsimp [ModProducts]
    dsimp [ModProducts] at hg
    obtain ⟨⟨l,gl⟩, hl⟩ := hg.1
    use ⟨l, Products.isGoodMono C h gl⟩
    ext x
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _), ← hl]
    exact congr_fun (GoodProducts.evalFac _ _ _) x
  · rw [← hg.2]
    ext x
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _)]
    congr
    exact congr_fun (resOnSubsets_eq C h).symm x

lemma DirectedS (o : Ordinal) : Directed (· ⊆ ·) (fun e ↦ ModProducts.smaller C
    e.val : {o' // o' < o} → Set (LocallyConstant { i // i ∈ C } ℤ)) := by
  rintro ⟨o₁,h₁⟩ ⟨o₂,h₂⟩
  dsimp
  have h : o₁ ≤ o₂ ∨ o₂ ≤ o₁ :=
    (inferInstance : IsTotal Ordinal ((·≤·) : Ordinal → Ordinal → Prop)).total o₁ o₂
  cases h
  · use ⟨o₂,h₂⟩ -- ⟨(Order.succ o₂), ho.2 o₂ h₂⟩
    exact ⟨ModProducts.smaller_mono C (by assumption), ModProducts.smaller_mono C (le_refl o₂)⟩
  · use ⟨o₁,h₁⟩ -- ⟨(Order.succ o₁), ho.2 o₁ h₁⟩
    exact ⟨ModProducts.smaller_mono C (le_refl o₁), ModProducts.smaller_mono C (by assumption)⟩

lemma DirectedSubmodules (o : Ordinal) : Directed (· ≤ ·) (fun e ↦
    Submodule.span ℤ (ModProducts.smaller C e.val) :
    {o' // o' < o} → Submodule ℤ (LocallyConstant { i // i ∈ C } ℤ)) := by
  let f : {o' // o' < o} → Set (LocallyConstant { i // i ∈ C } ℤ) :=
    fun e ↦ ModProducts.smaller C e.val
  let g : Set (LocallyConstant {i // i ∈ C} ℤ) → Submodule ℤ (LocallyConstant {i // i ∈ C} ℤ) :=
    fun s ↦ Submodule.span ℤ s
  suffices : Directed (· ≤ ·) (g ∘ f)
  · exact this
  have : Directed (· ⊆ ·) f := DirectedS C o
  refine' Directed.mono_comp _ _ this
  intro _ _ h
  exact Submodule.span_mono h

instance nonempty_downset {o : Ordinal} (ho : Ordinal.IsLimit o) : Nonempty {o' // o' < o} := by
  use 0
  simp only [Ordinal.pos_iff_ne_zero]
  exact ho.1

section JointlySurjective

open CategoryTheory
open CategoryTheory.Limits

lemma IzeroLTTop : 0 < Ordinal.type ((·<·) : (WithTop I) → (WithTop I) → Prop) := by
  rw [Ordinal.pos_iff_ne_zero, Ordinal.type_ne_zero_iff_nonempty]
  exact inferInstance

instance ICofiltered {o : Ordinal} (ho : o.IsLimit) :
    IsCofiltered {i : WithTop I // ord I i < o}ᵒᵖ :=
{ Nonempty := by
    use Ordinal.enum _ 0 IzeroLTTop
    dsimp [ord]
    simp only [Ordinal.typein_enum]
    rw [Ordinal.pos_iff_ne_zero]
    exact ho.1
  cone_objs := by
    intro i j
    cases (le_total i.unop j.unop)
    · use j
      use (homOfLE (by assumption : i.unop ≤ j.unop)).op
      use (homOfLE (le_refl j.unop)).op
      trivial
    · use i
      use (homOfLE (le_refl i.unop)).op
      use (homOfLE (by assumption : j.unop ≤ i.unop)).op
      trivial
  cone_maps := by
    intro i j f g
    suffices : f = g
    · rw [this]
      use i
      use 𝟙 i
    simp only [eq_iff_true_of_subsingleton]  }

instance ResCompact (o : Ordinal) (hC : IsClosed C) : CompactSpace (Res C o) := by
  rw [← isCompact_iff_compactSpace]
  exact (isClosed_Res C o hC).isCompact

instance CCompact (hC : IsClosed C) :
    CompactSpace C := by
  rw [← isCompact_iff_compactSpace]
  exact hC.isCompact

lemma ResOnSubsetsId (o : Ordinal) : ResOnSubsets C (le_refl o) = id := by
  ext ⟨f,hf⟩ i
  dsimp [ResOnSubsets, ProjOrd]
  split_ifs
  · rfl
  · obtain ⟨g, ⟨_,hg⟩⟩ := hf
    dsimp [ProjOrd] at hg
    rw [← congr_fun hg i]
    split_ifs
    rfl

lemma ResOnSubsetsComp {o₁ o₂ o₃ : Ordinal} (h₁₂ : o₁ ≤ o₂) (h₂₃ : o₂ ≤ o₃) :
    ResOnSubsets C h₁₂ ∘ ResOnSubsets C h₂₃ = ResOnSubsets C (le_trans h₁₂ h₂₃) := by
  ext ⟨f,hf⟩ i
  dsimp [ResOnSubsets, ProjOrd]
  split_ifs with h₁ h₂
  · rfl
  · obtain ⟨g, ⟨_,hg⟩⟩ := hf
    dsimp [ProjOrd] at hg
    rw [← congr_fun hg i]
    split_ifs
    · exfalso
      apply h₂
      exact lt_of_lt_of_le h₁ h₁₂
    · rfl
  · rfl

lemma ordILE {i j : WithTop I} (h : i ≤ j) : ord I i ≤ ord I j := by
  dsimp [ord]
  rwa [Ordinal.typein_le_typein, not_lt]

noncomputable
def OrdToProfinite (o : Ordinal) (hC : IsClosed C) :
    {i : WithTop I // ord I i < o}ᵒᵖ ⥤ Profinite.{u} :=
{ obj := fun i ↦ @Profinite.of (Res C (ord I i.unop)) _ (ResCompact _ _ hC) _ _
  map := fun h ↦ ⟨ResOnSubsets C (ordILE (leOfHom h.unop)), (continuous_ResOnSubsets _ _)⟩
  map_id := by
    intro e
    dsimp
    simp_rw [ResOnSubsetsId]
    rfl
  map_comp := by
    intro e₁ e₂ e₃ h₁₂ h₂₃
    dsimp
    congr
    simp only [ContinuousMap.coe_mk]
    rw [ResOnSubsetsComp] }

noncomputable
def OrdCone (o : Ordinal) (hC : IsClosed C) :
    Cone (OrdToProfinite C o hC) :=
{ pt := @Profinite.of {i // i ∈ C} _ (CCompact C hC) _ _
  π :=
  { app := fun i ↦ ⟨ResOnSubset C (ord I i.unop), continuous_ResOnSubset _ _⟩
    naturality := by
      intro e₁ e₂ h
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      congr
      simp only [ContinuousMap.coe_mk]
      dsimp [OrdToProfinite]
      rw [resOnSubsets_eq] } }

lemma succ_le_type {o o' : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop)) (ho' : o' < o) :
    Order.succ o' < Ordinal.type (·<· : WithTop I → WithTop I → Prop) :=
lt_of_lt_of_le (ho.2 o' ho') hto

noncomputable
def ISucc {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    {i : WithTop I} (hi : ord I i < o) : {i // ord I i < o} :=
{ val := Ordinal.enum (·<·) (Order.succ (ord I i)) (succ_le_type ho hto hi)
  property := by
    dsimp [ord] at *
    simp only [Ordinal.typein_enum]
    exact ho.2 _ hi }

lemma ord_lt_succ {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    {i : WithTop I} (hi : ord I i < o) : ord I i < ord I (ISucc ho hto hi).val := by
  dsimp [ord, ISucc]
  simp only [Ordinal.typein_enum, Order.lt_succ_iff_not_isMax, gt_iff_lt, not_isMax,
    not_false_eq_true]

noncomputable
def OrdConeIsLimitLiftFunAux {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (s : Cone (OrdToProfinite C o hC)) : s.pt → ((WithTop I) → Bool) :=
fun x i ↦ if h : ord I i < o then (s.π.app (Opposite.op (ISucc ho hto h)) x).val i
  else false

lemma le_of_leOrd {o : Ordinal} {i j : {i // ord I i < o}} (h : ord I i.val ≤ ord I j.val) :
    i ≤ j := by
  dsimp [ord] at h
  simp only [Ordinal.typein_le_typein, not_lt] at h
  exact h

def HomOfLEOrd {o : Ordinal} {i j : {i // ord I i < o}} (h : ord I i.val ≤ ord I j.val) : i ⟶ j :=
homOfLE (le_of_leOrd h)

lemma ordConeIsLimitLiftFunAux_mem {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s : Cone (OrdToProfinite C o hC)) (x : s.pt) :
    OrdConeIsLimitLiftFunAux C ho hto hC s x ∈ C := by
  dsimp [OrdConeIsLimitLiftFunAux]
  have : C = Res C o := supportResEq C o hsC
  rw [Set.ext_iff] at this
  rw [this]
  dsimp [Res, ProjOrd]
  simp only [Set.mem_image]
  have hs := fun i ↦ (s.π.app i x).prop
  dsimp [Res] at hs
  simp only [Set.mem_image] at hs
  let f' := fun i ↦ (hs (Opposite.op i)).choose
  have hf' := fun i ↦ (hs (Opposite.op i)).choose_spec
  let f : WithTop I → Bool :=
    fun i ↦ if h : ord I i < o then f' (ISucc ho hto h) i else false
  use f
  refine' ⟨_,_⟩
  · let S : {i // ord I i < o} → Set {i // ord I i < o} := fun i ↦ {j | ord I i.val ≤ ord I j.val}
    have h0 : ord I (Ordinal.enum _ 0 IzeroLTTop) < o
    · dsimp [ord]
      simp only [Ordinal.typein_enum, Ordinal.pos_iff_ne_zero]
      exact ho.1
    let b : Filter {i // ord I i < o} := Filter.generate (Set.range S)
    have hb : b.NeBot
    · rw [Filter.generate_neBot_iff]
      intro t hts ht
      simp only [Set.nonempty_sInter]
      rw [Set.subset_range_iff_exists_image_eq] at hts
      obtain ⟨r,hr⟩ := hts
      rw [← hr, Set.finite_image_iff] at ht
      · by_cases hre : Set.Nonempty r
        · have hmax := Set.exists_max_image r id ht hre
          obtain ⟨a, ha⟩ := hmax
          use a
          intro w hw
          rw [← hr] at hw
          obtain ⟨w',hw⟩ := hw
          rw [← hw.2]
          dsimp [ord]
          simp only [Ordinal.typein_le_typein, Subtype.coe_lt_coe, not_lt]
          exact ha.2 w' hw.1
        · use ⟨(Ordinal.enum _ 0 IzeroLTTop), h0⟩
          intro w hw
          rw [Set.not_nonempty_iff_eq_empty] at hre
          rw [hre] at hr
          simp only [ge_iff_le, Set.image_empty] at hr
          rw [← hr] at hw
          exfalso
          exact Set.not_mem_empty w hw
      · intro i _ j _ hsij
        dsimp at hsij
        rw [Set.ext_iff] at hsij
        have hsi := hsij i
        have hsj := hsij j
        simp at hsi hsj
        have hij := le_antisymm hsj hsi
        dsimp [ord] at hij
        simp [Ordinal.typein_inj] at hij
        exact Subtype.ext hij
    have hf : Filter.Tendsto f' b (nhds f)
    · rw [nhds_pi, Filter.tendsto_pi]
      intro i
      rw [Filter.tendsto_def]
      intro U hU
      have hf := mem_of_mem_nhds hU
      dsimp at hf
      split_ifs at hf with h
      · dsimp
        rw [Filter.mem_generate_iff]
        simp only [exists_and_left, exists_prop]
        use {S (ISucc ho hto h)}
        refine' ⟨Set.finite_singleton _,_,_⟩
        · intro W hW
          use (ISucc ho hto h)
          simp only [Set.mem_singleton_iff] at hW
          rw [hW]
        · simp only [Set.sInter_singleton]
          intro j hj
          simp only [Set.mem_preimage]
          simp only [Set.mem_setOf_eq] at hj
          suffices : f' j i ∈ U
          · exact this
          suffices : f' (ISucc ho hto h) i = f' j i
          · rw [← this]
            exact hf
          suffices : ∀ y,
            ((y ∈ C ∧ (ProjOrd (ord I (ISucc ho hto h).val) y =
            ((forget Profinite).map (s.π.app (Opposite.op (ISucc ho hto h))) x).val)) →
            y i = f' j i)
          · specialize this (f' (ISucc ho hto h))
            exact this (hf' (ISucc ho hto h))
          rintro y ⟨_, hy⟩
          suffices : ∀ z,
            ((z ∈ C ∧ (ProjOrd (ord I j.val) z =
            ((forget Profinite).map (s.π.app (Opposite.op j)) x).val)) →
            y i = z i)
          · specialize this (f' j)
            exact this (hf' j)
          rintro z ⟨_, hz⟩
          have hy' := congr_fun hy i
          have hz' := congr_fun hz i
          dsimp [ProjOrd] at hy' hz'
          split_ifs at hy' hz' with h₁ h₂
          · rw [hy', hz']
            have hsw := Cone.w s (HomOfLEOrd hj).op
            rw [← hsw]
            dsimp [OrdToProfinite, ResOnSubsets, ProjOrd]
            simp only [FunctorToTypes.map_comp_apply, Profinite.forget_ContinuousMap_mk,
              ite_eq_left_iff, not_lt]
            intro hord
            exfalso
            simp only [← not_lt] at hord
            exact hord (ord_lt_succ _ _ _)
          · exfalso
            apply h₂
            exact lt_of_lt_of_le (ord_lt_succ _ _ _) hj
          · exfalso
            exact h₁ (ord_lt_succ _ _ _)
          · exfalso
            exact h₁ (ord_lt_succ _ _ _)
      · dsimp
        rw [Filter.mem_generate_iff]
        simp only [exists_and_left, exists_prop]
        use {S ⟨(Ordinal.enum _ 0 IzeroLTTop), h0⟩}
        refine' ⟨Set.finite_singleton _,_,_⟩
        · intro W hW
          use ⟨(Ordinal.enum _ 0 IzeroLTTop), h0⟩
          simp only [Set.mem_singleton_iff] at hW
          rw [hW]
        · simp only [Set.sInter_singleton]
          intro j hj
          simp only [Set.mem_preimage]
          simp only [Set.mem_setOf_eq] at hj
          suffices : f' j i ∈ U
          · exact this
          suffices : f' j i = false
          · rw [this]
            exact hf
          suffices : ∀ z,
            ((z ∈ C ∧ (ProjOrd (ord I j.val) z =
            ((forget Profinite).map (s.π.app (Opposite.op j)) x).val)) →
            z i = false)
          · specialize this (f' j)
            exact this (hf' j)
          rintro z ⟨hzC, hz⟩
          have hz' := congr_fun hz i
          dsimp [ProjOrd] at hz'
          split_ifs at hz' with h₁
          · exfalso
            apply h
            exact lt_trans h₁ j.prop
          · dsimp [Support] at hsC
            simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp] at hsC
            specialize hsC i z hzC
            rw [← not_imp_not] at hsC
            simp only [Bool.not_eq_true] at hsC
            exact hsC h
    exact IsClosed.mem_of_tendsto hC hf (Filter.eventually_of_forall (fun i ↦ (hf' i).1))
  · ext i
    by_cases h : ord I i < o
    · rw [ite_eq_iff]
      left
      refine' ⟨h,_⟩
      apply Eq.symm
      rw [dite_eq_iff]
      left
      use h
      rw [← (hf' (ISucc ho hto h)).2]
      dsimp [ProjOrd]
      split_ifs with h'
      · rfl
      · exfalso
        exact h' (ord_lt_succ _ _ _)
    · rw [ite_eq_iff]
      right
      refine' ⟨h,_⟩
      apply Eq.symm
      rw [dite_eq_iff]
      right
      use h

noncomputable
def OrdConeIsLimitLiftFun {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s : Cone (OrdToProfinite C o hC)) : s.pt → {i // i ∈ C} :=
  fun x ↦ ⟨OrdConeIsLimitLiftFunAux C ho hto hC s x, ordConeIsLimitLiftFunAux_mem _ _ _ _ hsC _ x⟩

lemma continuous_ordConeIsLimitLiftFun {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s : Cone (OrdToProfinite C o hC)) : Continuous (OrdConeIsLimitLiftFun C ho hto hC hsC s) := by
  rw [continuous_induced_rng]
  have : (Subtype.val ∘ OrdConeIsLimitLiftFun C ho hto hC hsC s) =
      OrdConeIsLimitLiftFunAux C ho hto hC s
  · ext
    rfl
  rw [this]
  refine' continuous_pi _
  intro i
  dsimp [OrdConeIsLimitLiftFunAux]
  split_ifs with h
  · refine' Continuous.comp (continuous_apply _) _
    exact Continuous.comp continuous_subtype_val
      (s.π.app (Opposite.op (ISucc ho hto h))).continuous
  · exact continuous_const

noncomputable
def OrdConeIsLimitLift {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s : Cone (OrdToProfinite C o hC)) : s.pt ⟶ (OrdCone C o hC).pt :=
  ⟨OrdConeIsLimitLiftFun C ho hto hC hsC s, continuous_ordConeIsLimitLiftFun C ho hto hC hsC s⟩

lemma OrdToProfinite_aux {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (s: Cone (OrdToProfinite C o hC))
    (x : s.pt) (i j : WithTop I) (hi : ord I i < o)
    (hj : ord I j < o)
    (hs : ord I (ISucc ho hto hj) ≤ ord I i) :
    ((s.π.app { unop := { val := i, property := hi } } ≫ (OrdToProfinite C o hC).map
    (@HomOfLEOrd I _ _ o (ISucc ho hto hj) ⟨i,hi⟩
    hs).op).1 x).1 j =
    ((s.π.app { unop := { val := i, property := hi } }).1 x).1 j := by
  dsimp [OrdToProfinite]
  have : (ResOnSubsets C hs ((s.π.app { unop := { val := i, property := hi } }).1 x)).val j =
      ((s.π.app { unop := { val := i, property := hi } }).1 x).val j
  · dsimp [ResOnSubsets, ProjOrd]
    split_ifs with hjs
    · rfl
    · exfalso
      exact hjs (ord_lt_succ _ _ _)
  exact this

lemma OrdConeIsLimitLiftFun_aux {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s: Cone (OrdToProfinite C o hC))
    (x : s.pt) (i j : WithTop I) (hi : ord I i < o) (h : ord I j < ord I i) :
    ((OrdConeIsLimitLiftFun C ho hto hC hsC s) x).val j =
    ((s.π.app { unop := { val := i, property := hi } }).1 x).1 j := by
  dsimp [OrdConeIsLimitLiftFun, OrdConeIsLimitLiftFunAux]
  split_ifs with hj
  · have hs : ord I (ISucc ho hto hj) ≤ ord I i
    · dsimp [ord, ISucc]
      dsimp [ord] at h
      simp only [Ordinal.typein_lt_typein] at h
      simpa only [Ordinal.typein_enum, Order.succ_le_iff, Ordinal.typein_lt_typein]
    let f := (@HomOfLEOrd I _ _ o (ISucc ho hto hj) ⟨i,hi⟩ hs)
    have := Cone.w s f.op
    rw [← this]
    exact OrdToProfinite_aux C ho hto hC s x i j hi hj hs
  · exfalso
    exact hj (lt_trans h hi)

lemma OrdConeIsLimit_fac_aux {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s: Cone (OrdToProfinite C o hC))
    (x : s.pt) (i : WithTop I) (hi : ord I i < o) :
    (ResOnSubset C (ord I i)) ((OrdConeIsLimitLift C ho hto hC hsC s) x) =
    (s.π.app { unop := { val := i, property := hi } }) x := by
  ext j
  dsimp [ResOnSubset, ProjOrd]
  split_ifs with h
  · dsimp [OrdConeIsLimitLift]
    exact OrdConeIsLimitLiftFun_aux C ho hto hC hsC s x i j hi h
  · have hR := (s.π.app ⟨i,hi⟩ x).prop
    dsimp [Res] at hR
    obtain ⟨g,⟨_,hg⟩⟩ := hR
    dsimp [ProjOrd] at hg
    have hgj := congr_fun hg j
    split_ifs at hgj
    rw [hgj]

lemma OrdConeIsLimit {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o }) : IsLimit (OrdCone C o hC) :=
{ lift := fun s ↦ OrdConeIsLimitLift C ho hto hC hsC s
  fac := by
    rintro s ⟨⟨i,hi⟩⟩
    ext x
    simp only [comp_apply]
    dsimp [OrdCone]
    exact OrdConeIsLimit_fac_aux C ho hto hC hsC s x i hi
  uniq := by
    rintro s ⟨m,hm⟩ h
    dsimp [OrdCone] at m
    congr
    dsimp [OrdConeIsLimitLift, OrdConeIsLimitLiftFun, OrdConeIsLimitLiftFunAux]
    ext x
    apply Subtype.ext_val
    ext i
    dsimp
    split_ifs with hi
    · rw [← h (Opposite.op (ISucc ho hto hi) : {i // ord I i < o}ᵒᵖ)]
      simp only [FunctorToTypes.map_comp_apply]
      dsimp [OrdCone]
      have : (ResOnSubset C (ord I (ISucc ho hto hi)) (m x)).val i = (m x).val i
      · dsimp [ResOnSubset, ProjOrd]
        split_ifs with hi'
        · rfl
        · exfalso
          exact hi' (ord_lt_succ _ _ _)
      exact this.symm
    · have := (m x).prop
      dsimp [Support] at hsC
      simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp] at hsC
      specialize hsC i (m x).val this
      rw [← not_imp_not] at hsC
      simp only [Bool.not_eq_true] at hsC
      exact hsC hi }

lemma comapJointlySurjectiveAuxSubtype {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (f : LocallyConstant {i // i ∈ C} ℤ) : ∃ (e : {o' // o' < o})
    (g : LocallyConstant {i // i ∈ Res C e.val} ℤ), g.comap (ResOnSubset C e.val) = f := by
  obtain ⟨i, g, h⟩ := @Profinite.exists_locallyConstant {i : WithTop I // ord I i < o}ᵒᵖ _
    (ICofiltered ho) _ (OrdCone C o hC) _
    (OrdConeIsLimit C ho hto hC hsC) f
  use ⟨ord I i.unop.val, i.unop.prop⟩
  use g
  rw [h]
  congr

lemma comapJointlySurjective {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (f : LocallyConstant {i // i ∈ C} ℤ) : ∃ o', o' < o ∧
    ∃ (g : LocallyConstant {i // i ∈ Res C o'} ℤ), g.comap (ResOnSubset C o') = f := by
  obtain ⟨e, g, h⟩ := comapJointlySurjectiveAuxSubtype C ho hto hC hsC f
  exact ⟨e.val, e.prop,⟨g,h⟩⟩

lemma comapLinearJointlySurjective {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (f : LocallyConstant {i // i ∈ C} ℤ) : ∃ o', o' < o ∧
    ∃ (g : LocallyConstant {i // i ∈ Res C o'} ℤ),
    (LocallyConstant.comapLinear (ResOnSubset C o') (continuous_ResOnSubset _ _) :
    LocallyConstant {i // i ∈ Res C o'} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ) g = f :=
  comapJointlySurjective C ho hto hC hsC f

end JointlySurjective

section Successor

variable (o : Ordinal)

variable (hC : IsClosed C) (hsC : Support C ⊆ {j | ord I j < Order.succ o}) [Nonempty C]

def GoodProducts.StartingWithMax : Set (Products (WithTop I)) :=
{l | l.isGood C ∧ l.val ≠ [] ∧ ord I l.val.head! = o}

lemma GoodProducts.union_succ : GoodProducts C = GoodProducts (Res C o) ∪ StartingWithMax C o := by
  ext ⟨l,hl⟩
  dsimp [GoodProducts, StartingWithMax]
  simp only [Set.mem_union, Set.mem_setOf_eq]
  refine' ⟨_,_⟩
  <;> intro h
  · by_cases hln : l = []
    · left
      simp_rw [hln]
      exact nilIsGoodAny (Res C o)
    · by_cases hh : ord I l.head! = o
      · right
        exact ⟨h,hln,hh⟩
      · left
        intro he
        apply h
        rw [supportResEq C (Order.succ o) hsC] at h
        have hls := Products.head_lt_ord_of_isGood C h hln
        simp only [Order.lt_succ_iff] at hls
        have hlhead : ord I (⟨l,hl⟩ : Products (WithTop I)).val.head! < o := lt_of_le_of_ne hls hh
        rw [mem_span_set]
        rw [mem_span_set] at he
        obtain ⟨c,⟨hcs,hcsum⟩⟩ := he
        use Finsupp.mapDomain (LocallyConstant.comap
          (ResOnSubset C o) :
          LocallyConstant {i // i ∈ Res C o} ℤ → LocallyConstant {i // i ∈ C} ℤ) c
        refine' ⟨_,_⟩
        · refine' (subset_trans Finsupp.mapDomain_support _) -- need "Classical" for decidability
          intro p hp
          simp only [Finset.image_val, Multiset.mem_dedup, Multiset.mem_map, Finset.mem_val] at hp
          obtain ⟨t,ht⟩ := hp
          have ht' := hcs ht.1
          obtain ⟨y, hy⟩ := ht'
          rw [← hy.2] at ht
          rw [← ht.2]
          use y
          refine' ⟨hy.1,_⟩
          rw [← Products.eval_comapFac'C]
          intro hnil
          obtain ⟨b, l', hbl⟩ := List.exists_cons_of_ne_nil hnil
          rw [hbl]
          simp only [List.head!_cons, Order.lt_succ_iff]
          dsimp [ord]
          simp only [Ordinal.typein_le_typein, not_lt]
          have hya : y.val < l := hy.1
          rw [hbl] at hya
          cases hya
          · assumption
          · refine' lt_trans _ hlhead
            dsimp [ord]
            simpa only [Ordinal.typein_lt_typein]
        · ext f
          rw [← Products.evalFacC C (fun _ ↦ hlhead)]
          rw [Finsupp.sum_mapDomain_index_inj
            (LocallyConstant.comap_injective _ (continuous_ResOnSubset _ _)
            (surjective_ResOnSubset _ _))]
          rw [← hcsum]
          congr! 1
          rw [← LocallyConstant.coe_comap _ _ (continuous_ResOnSubset _ _)]
          have hlin : LocallyConstant.comap (ResOnSubset C o) =
              ↑(LocallyConstant.comapLinear (ResOnSubset C o)
              (continuous_ResOnSubset _ _) :
              LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ) :=
            rfl
          rw [hlin, map_finsupp_sum]
          congr! 1
          apply Finsupp.sum_congr
          intro f _
          dsimp [LocallyConstant.comapLinear]
          ext a'
          dsimp
          rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
          rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
          rfl
  · refine' Or.elim h _ _
    <;> intro hh
    · have := Products.isGoodMono C (le_of_lt (Order.lt_succ o)) hh
      rwa [supportResEq C (Order.succ o) hsC]
    · exact hh.1

def GoodProducts.sum_to :
    (GoodProducts (Res C o)) ⊕ (StartingWithMax C o) → Products (WithTop I) :=
  Sum.elim Subtype.val Subtype.val

lemma GoodProducts.injective_sum_to : Function.Injective (sum_to C o) := by
  apply Function.Injective.sum_elim
  · exact Subtype.val_injective
  · exact Subtype.val_injective
  rintro ⟨a,ha⟩ ⟨b,hb⟩
  dsimp
  dsimp [GoodProducts] at ha
  dsimp [StartingWithMax] at hb
  by_cases hanil : a.val = []
  · rw [← hanil] at hb
    apply Ne.symm
    exact Subtype.ne_of_val_ne hb.2.1
  · have ha' := Products.head_lt_ord_of_isGood C ha hanil
    rw [← hb.2.2] at ha'
    dsimp [ord] at ha'
    simp only [Ordinal.typein_lt_typein] at ha'
    have := ne_of_lt ha'
    intro hab
    apply this
    rw [hab]

noncomputable
def GoodProducts.sum_to_equiv := Equiv.ofInjective (sum_to C o) (injective_sum_to C o)

lemma GoodProducts.sum_to_range :
    Set.range (sum_to C o) = GoodProducts (Res C o) ∪ StartingWithMax C o := by
  have h : Set.range (sum_to C o) = _ ∪ _ := Set.Sum.elim_range _ _
  rw [h]
  congr
  <;> ext l
  · constructor <;>
    intro hl
    · obtain ⟨m,hm⟩ := hl
      rw [← hm]
      exact m.prop
    · use ⟨l,hl⟩
  · constructor <;>
    intro hl
    · obtain ⟨m,hm⟩ := hl
      rw [← hm]
      exact m.prop
    · use ⟨l,hl⟩

noncomputable
def GoodProducts.sum_equiv : GoodProducts (Res C o) ⊕ (StartingWithMax C o) ≃ GoodProducts C :=
Equiv.trans (Equiv.trans (sum_to_equiv C o) (Equiv.Set.ofEq (sum_to_range C o)))
  (Equiv.Set.ofEq (union_succ C o hsC).symm)

lemma GoodProducts.sum_equiv_comp_eval_eq_elim : eval C ∘ (sum_equiv C o hsC).toFun =
    (Sum.elim (fun (l : GoodProducts (Res C o)) ↦ Products.eval C l.1)
    (fun (l : StartingWithMax C o) ↦ Products.eval C l.1)) := by
  ext ⟨_,_⟩
  · rfl
  · rfl

lemma GoodProducts.linearIndependent_iff_sum :
    LinearIndependent ℤ (eval C) ↔ LinearIndependent ℤ (Sum.elim
    (fun (l : GoodProducts (Res C o)) ↦ Products.eval C l.1)
    (fun (l : StartingWithMax C o) ↦ Products.eval C l.1)) := by
  rw [← linearIndependent_equiv (sum_equiv C o hsC), ← sum_equiv_comp_eval_eq_elim C o hsC]
  exact Iff.rfl

noncomputable
def GoodProducts.equiv_smaller : GoodProducts (Res C o) ≃ ModProducts.smaller C o :=
Equiv.trans (equiv_modProducts (Res C o)) (ModProducts.equiv_smaller C o)

lemma GoodProducts.eval_eq_comp_equiv : (fun (l : GoodProducts (Res C o)) ↦ Products.eval C l.1) =
    (fun p ↦ ↑p) ∘ ↑(equiv_smaller C o) := by
  ext p f
  dsimp [equiv_smaller, ModProducts.equiv_smaller, ModProducts.equiv_smaller_toFun,
    equiv_modProducts, eval, LocallyConstant.comapLinear]
  rw [congr_fun (Products.goodEvalFacC C p.2).symm f,
    LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
  rfl

lemma GoodProducts.linearIndependent_succ_iff :
    LinearIndependent ℤ (eval (Res C o)) ↔ LinearIndependent ℤ
    (fun (l : GoodProducts (Res C o)) ↦ Products.eval C l.1) := by
  rw [ModProducts.smaller_linear_independent_iff, ← linearIndependent_equiv (equiv_smaller C o),
    eval_eq_comp_equiv]

variable {o} (ho : o < Ordinal.type (·<· : WithTop I → WithTop I → Prop))

def C0 := C ∩ {f | f (term I ho) = false}

def C1 := C ∩ {f | f (term I ho) = true}

lemma isClosed_C0 : IsClosed (C0 C ho) := by
  refine' IsClosed.inter hC _
  have h : Continuous ((fun f ↦ f (term I ho) : ((WithTop I) → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact (continuous_iff_isClosed.mp h) {false} (isClosed_discrete _)

lemma isClosed_C1 : IsClosed (C1 C ho) := by
  refine' IsClosed.inter hC _
  have h : Continuous ((fun f ↦ f (term I ho) : ((WithTop I) → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact (continuous_iff_isClosed.mp h) {true} (isClosed_discrete _)

lemma support_C0 : Support (C0 C ho) ⊆ {j | ord I j < o} := by
  intro i hi
  dsimp [Support] at hi hsC
  simp only [Set.mem_setOf_eq]
  simp only [Order.lt_succ_iff, Set.setOf_subset_setOf, forall_exists_index, and_imp] at hsC
  obtain ⟨f, hf⟩ := hi
  dsimp [C0] at hf
  specialize hsC i f hf.1.1 hf.2
  refine' lt_of_le_of_ne hsC _
  have hf' := hf.1.2
  simp only [Set.mem_setOf_eq] at hf'
  have : i ≠ term I ho
  · refine' ne_of_apply_ne f _
    rw [hf.2, hf']
    simp
  have ht : ord I (term I ho) = o
  · dsimp [ord, term]
    simp only [Ordinal.typein_enum]
  rw [← ht]
  dsimp [ord]
  simpa only [Ordinal.typein_inj]

lemma support_C1 : Support (Res (C1 C ho) o) ⊆ {j | ord I j < o} :=
  support_Res_le_o _ _

lemma UnionEq : (C0 C ho) ∪ (C1 C ho) = C := by
  ext x
  constructor
  <;> intro hx
  · dsimp [C0, C1] at hx
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    rw [← and_or_left] at hx
    exact hx.1
  · dsimp [C0, C1]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [← and_or_left]
    refine' ⟨hx,_⟩
    by_cases h : x (term I ho) = false
    · left
      assumption
    · right
      simpa only [← Bool.not_eq_false]

def C0' : Set {i // i ∈ C} := {f | f.val ∈ C0 C ho}

def C1' : Set {i // i ∈ C} := {f | f.val ∈ C1 C ho}

lemma isOpen_false : IsOpen {f : WithTop I → Bool | f (term I ho) = false} := by
  have h : Continuous ((fun f ↦ f (term I ho) : ((WithTop I) → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact IsOpen.preimage h (isOpen_discrete {false})

lemma isOpen_true : IsOpen {f : WithTop I → Bool | f (term I ho) = true} := by
  have h : Continuous ((fun f ↦ f (term I ho) : ((WithTop I) → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact IsOpen.preimage h (isOpen_discrete {true})

lemma isClopen_C0' : IsClopen (C0' C ho) := by
  constructor
  · have := IsOpen.preimage (continuous_subtype_val : Continuous (fun (i : {i // i ∈ C}) ↦ i.val))
      (isOpen_false ho)
    suffices h : C0' C ho = Subtype.val ⁻¹' {f | f (term I ho) = false}
    · rw [h]
      exact this
    ext x
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨x.prop, hx⟩⟩
  · have := IsClosed.preimage (continuous_subtype_val : Continuous (fun (i : {i // i ∈ C}) ↦ i.val))
      (isClosed_C0 C hC ho)
    suffices h : C0' C ho = Subtype.val ⁻¹' (C0 C ho)
    · rw [h]
      exact this
    rfl

lemma isClopen_C1' : IsClopen (C1' C ho) := by
  constructor
  · have := IsOpen.preimage (continuous_subtype_val : Continuous (fun (i : {i // i ∈ C}) ↦ i.val))
      (isOpen_true ho)
    suffices h : C1' C ho = Subtype.val ⁻¹' {f | f (term I ho) = true}
    · rw [h]
      exact this
    ext x
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨x.prop, hx⟩⟩
  · have := IsClosed.preimage (continuous_subtype_val : Continuous (fun (i : {i // i ∈ C}) ↦ i.val))
      (isClosed_C1 C hC ho)
    suffices h : C1' C ho = Subtype.val ⁻¹' (C1 C ho)
    · rw [h]
      exact this
    rfl

lemma union_C0'C1'_eq_univ : (C0' C ho) ∪ (C1' C ho) = Set.univ := by
  rw [(by rfl : C0' C ho = Subtype.val ⁻¹' (C0 C ho)),
    (by rfl : C1' C ho = Subtype.val ⁻¹' (C1 C ho)),
    (by simp only [← Subtype.coe_preimage_self] :
    (Set.univ : Set {i // i ∈ C}) = Subtype.val ⁻¹' C)]
  simp only [← Set.preimage_union]
  rw [UnionEq]

def rC1' : Set {i // i ∈ C} := {f | f.val ∈ Res (C1 C ho) o}

lemma rC1_subset_C0 : rC1' C ho ⊆ C0' C ho := by
  intro x hx
  refine ⟨Subtype.mem x, ?_⟩
  obtain ⟨y, hy⟩ := hx
  rw [← hy.2]
  dsimp [ProjOrd]
  simp only [ite_eq_right_iff]
  intro h
  dsimp [ord, term] at h
  simp only [Ordinal.typein_enum, lt_self_iff_false] at h

lemma isClosed_rC1' : IsClosed (rC1' C ho) := by
  have := IsClosed.preimage (continuous_subtype_val : Continuous (fun (i : {i // i ∈ C}) ↦ i.val))
    (isClosed_Res _ o (isClosed_C1 C hC ho))
  suffices h : rC1' C ho = Subtype.val ⁻¹' (Res (C1 C ho) o)
  · rw [h]
    exact this
  rfl

def C' := C0 C ho ∩ Res (C1 C ho) o

lemma isClosed_C' : IsClosed (C' C ho) :=
IsClosed.inter (isClosed_C0 _ hC _) (isClosed_Res (C1 C ho) o (isClosed_C1 _ hC _))

lemma support_C' : Support (C' C ho) ⊆ {j | ord I j < o} := by
  dsimp [Support]
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  obtain ⟨f,hf⟩ := hi
  dsimp [C'] at hf
  have hC1 := support_C1 C ho
  dsimp [Support] at hC1
  simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp] at hC1
  exact hC1 i f hf.1.2 hf.2

def CC'₀ : {i // i ∈ C' C ho} → {i // i ∈ C} := fun g ↦ ⟨g.val,g.prop.1.1⟩

lemma continuous_CC'₀ : Continuous (CC'₀ C ho) :=
Continuous.subtype_mk continuous_subtype_val _

lemma swapTrue_mem_C1 (f : {i // i ∈ Res (C1 C ho) o}) : SwapTrue o f.val ∈ C1 C ho := by
  obtain ⟨f,hf⟩ := f
  obtain ⟨g,hg⟩ := hf
  suffices : SwapTrue o f = g
  · rw [this]
    exact hg.1
  dsimp [SwapTrue]
  ext i
  split_ifs with h
  · dsimp [C1, term] at hg
    simp_rw [← h] at hg
    dsimp [ord] at hg
    simp only [Ordinal.enum_typein, Set.mem_inter_iff, Set.mem_setOf_eq] at hg
    exact hg.1.2.symm
  · dsimp [ProjOrd] at hg
    have := congr_fun hg.2 i
    split_ifs at this with h'
    · exact this.symm
    · simp only [not_lt] at h'
      have hh := Order.succ_le_of_lt (lt_of_le_of_ne h' (Ne.symm h))
      dsimp [Support] at hsC
      simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp] at hsC
      specialize hsC i g hg.1.1
      rw [← not_imp_not] at hsC
      simp only [not_lt, Bool.not_eq_true] at hsC
      rw [← this]
      exact (hsC hh).symm

lemma swapTrue_mem_C (f : {i // i ∈ C' C ho}) : SwapTrue o f.val ∈ C := by
  suffices : SwapTrue o f.val ∈ C1 C ho
  · exact this.1
  exact (swapTrue_mem_C1 C hsC ho ⟨f.val,f.prop.2⟩)

-- noncomputable
-- def ResC1C1 : {i // i ∈ Res (C1 C ho) o} → {i // i ∈ C1 C ho} :=
-- fun f ↦ ⟨SwapTrue o f.val, swapTrue_mem_C1 C ho f⟩

noncomputable
def CC'₁ : {i // i ∈ C' C ho} → {i // i ∈ C} :=
fun g ↦ ⟨SwapTrue o g.val, swapTrue_mem_C C hsC ho g⟩

lemma continuous_CC'₁ : Continuous (CC'₁ C hsC ho) :=
Continuous.subtype_mk (Continuous.comp (continuous_swapTrue o) continuous_subtype_val) _

noncomputable
def Linear_CC'₀ : LocallyConstant {i // i ∈ C} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C' C ho} ℤ :=
LocallyConstant.comapLinear (CC'₀ C ho) (continuous_CC'₀ C ho)

noncomputable
def Linear_CC'₁ : LocallyConstant {i // i ∈ C} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C' C ho} ℤ :=
LocallyConstant.comapLinear (CC'₁ C hsC ho) (continuous_CC'₁ C hsC ho)

noncomputable
def Linear_CC' : LocallyConstant {i // i ∈ C} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C' C ho} ℤ :=
Linear_CC'₁ C hsC ho - Linear_CC'₀ C ho

variable (o)

noncomputable
def Linear_ResC : LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ :=
LocallyConstant.comapLinear _ (continuous_ResOnSubset C o)

def GoodProducts.v : GoodProducts (Res C o) → LocallyConstant {i // i ∈ Res C o} ℤ :=
eval (Res C o)

def GoodProducts.v' : GoodProducts (Res C o) → LocallyConstant {i // i ∈ C} ℤ :=
fun l ↦ l.1.eval C

def GoodProducts.w' : StartingWithMax C o → LocallyConstant {i // i ∈ C} ℤ :=
fun l ↦ l.1.eval C

def GoodProducts.u : GoodProducts (Res C o) ⊕ StartingWithMax C o →
    LocallyConstant {i // i ∈ C} ℤ :=
Sum.elim (v' C o) (w' C o)

lemma GoodProducts.injective_u : Function.Injective (u C o) := by
  have := injective C
  have hu := union_succ C o hsC
  have hr : GoodProducts (Res C o) ⊆ GoodProducts C
  · rw [hu]
    exact Set.subset_union_left _ _
  have hs : StartingWithMax C o ⊆ GoodProducts C
  · rw [hu]
    exact Set.subset_union_right _ _
  dsimp [eval] at this
  apply Function.Injective.sum_elim
  <;> dsimp [v', w']
  · intro a b h
    have hra : (⟨a.val, hr a.prop⟩ : GoodProducts C).val = a.val := by rfl
    have hrb : (⟨b.val, hr b.prop⟩ : GoodProducts C).val = b.val := by rfl
    dsimp at h
    rw [← hra, ← hrb] at h
    ext
    specialize this h
    apply_fun fun f ↦ f.val at this
    rwa [hra, hrb] at this
  · intro a b h
    have hsa : (⟨a.val, hs a.prop⟩ : GoodProducts C).val = a.val := by rfl
    have hsb : (⟨b.val, hs b.prop⟩ : GoodProducts C).val = b.val := by rfl
    dsimp at h
    rw [← hsa, ← hsb] at h
    ext
    specialize this h
    apply_fun fun f ↦ f.val at this
    rwa [hsa, hsb] at this
  · intro a b h
    have hra : (⟨a.val, hr a.prop⟩ : GoodProducts C).val = a.val := by rfl
    have hsb : (⟨b.val, hs b.prop⟩ : GoodProducts C).val = b.val := by rfl
    rw [← hra, ← hsb] at h
    specialize this h
    apply_fun fun f ↦ f.val at this
    rw [hra, hsb] at this
    by_cases hanil : a.val.val = []
    · apply b.prop.2.1
      rwa [← this]
    · have ha' := Products.head_lt_ord_of_isGood C a.prop hanil
      simp_rw [← b.prop.2.2] at ha'
      dsimp [ord] at ha'
      simp only [Ordinal.typein_lt_typein] at ha'
      apply ne_of_lt ha'
      rw [this]

lemma GoodProducts.huv : u C o ∘ Sum.inl = Linear_ResC C o ∘ v C o := by
  dsimp [u, v, v', Linear_ResC, LocallyConstant.comapLinear, eval]
  ext1 l
  rw [← Products.eval_comapFacC C l.prop]
  rfl

variable {o}

noncomputable
def GoodProducts.w : StartingWithMax C o → LocallyConstant {i // i ∈ C' C ho} ℤ :=
Linear_CC' C hsC ho ∘ u C o ∘ Sum.inr

lemma GoodProducts.huw : Linear_CC' C hsC ho ∘ u C o ∘ Sum.inr = w C hsC ho := by rfl

def C'' : Set {i // i ∈ C} := {f | f.val ∈ C' C ho}

lemma isOpen_resOnSubset_C0' : IsOpen ((ResOnSubset C o) '' (C0' C ho)) := by
  have h : C0' C ho = Subtype.val ⁻¹' {f | f (term I ho) = false}
  · ext x
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨x.prop, hx⟩⟩
  rw [h]
  sorry

lemma isOpenMap_swapFalse : IsOpenMap (SwapFalse o : (WithTop I → Bool) → (WithTop I → Bool)) := by
  sorry

lemma swapFalse_mem_res {x : WithTop I → Bool} (hx : x ∈ C) : SwapFalse o x ∈ Res C o := sorry

lemma isOpenMap_resOnSubset : IsOpenMap (ResOnSubset C o) := by
  intro U hU
  rw [isOpen_induced_iff] at hU
  obtain ⟨t,ht⟩ := hU
  rw [← ht.2]
  rw [isOpen_induced_iff]
  have h : ResOnSubset C o = fun x ↦ ⟨SwapFalse o x.val, swapFalse_mem_res C x.prop⟩ := sorry
  rw [h]
  sorry
  -- have : Subtype.val ∘ ResOnSubset C o = SwapFalse o ∘ Subtype.val := sorry
  -- refine' ⟨SwapTrue o ⁻¹' t, ⟨IsOpen.preimage (continuous_swapTrue _) ht.1, _⟩⟩
  -- refine' ⟨SwapFalse o '' t, ⟨isOpenMap_swapFalse t ht.1, _⟩⟩
  -- ext f
  -- constructor
  -- <;> intro hf
  -- · simp only [Set.mem_preimage] at hf
  --   suffices : f.val ∈ Subtype.val '' ((ResOnSubset C o) '' (Subtype.val ⁻¹' t))
  --   · obtain ⟨f', hf'⟩ := this
  --     suffices ff' : f = f'
  --     · rw [ff']
  --       exact hf'.1
  --     rw [Subtype.ext_iff]
  --     exact hf'.2.symm
  --   convert hf
  --   have : Subtype.val ∘ ResOnSubset C o = SwapFalse o ∘ Subtype.val := sorry
  --   rw [← Set.image_comp, this, Set.image_comp]

  --   -- obtain ⟨x, ⟨hxt, hxf⟩⟩ := hf
  --   -- use ⟨x, ?_⟩
  --   -- ·
  --   -- · simp only [Set.mem_preimage]
  --   --   refine' ⟨hxt, _⟩
  --   --   apply Subtype.ext
  --   --   rw [← hxf]
  --   --   ext i
  --   --   dsimp [ResOnSubset, ProjOrd, SwapFalse]
  --   --   split_ifs with hi
  --   --   · sorry
  --   --   · sorry
  --   --   · sorry
  --   --   · sorry
  -- · sorry

lemma isClopen_rC1' : IsClopen (rC1' C ho) := by
  let V : Set (Res C o) := ResOnSubset C o '' (rC1' C ho) -- {f | f.val ∈ C' C ho}
  have hV : IsClopen V
  · constructor
    · have : V = ResOnSubset C o '' (C0' C ho) ∩ ResOnSubset C o '' (C1' C ho)
      · ext f
        dsimp
        constructor
        <;> intro hf
        · obtain ⟨g, hg⟩ := hf
          have hg' : g.val ∈ C' C ho
          · dsimp [C']
            exact ⟨rC1_subset_C0 C ho hg.1, hg.1⟩
          refine' ⟨⟨g, ⟨rC1_subset_C0 C ho hg.1, hg.2⟩⟩ ,⟨⟨SwapTrue o g.val, swapTrue_mem_C C hsC ho
            ⟨g, hg'⟩⟩,⟨_, _⟩⟩⟩
          · dsimp [C1', C1]
            refine' ⟨swapTrue_mem_C C hsC ho ⟨g, hg'⟩, _⟩
            dsimp [SwapTrue]
            simp only [ite_eq_left_iff]
            intro hfalse
            dsimp [ord, term] at hfalse
            simp only [Ordinal.typein_enum, not_true] at hfalse
          · ext i
            dsimp [ResOnSubset, SwapTrue, ProjOrd]
            split_ifs with hi hi'
            · exfalso
              exact ne_of_lt hi hi'
            · rw [← hg.2]
              dsimp [ResOnSubset, ProjOrd]
              apply Eq.symm
              simp only [ite_eq_left_iff, not_lt]
              intro hfalse
              simp only [← not_lt] at hfalse
              exfalso
              exact hfalse hi
            · rw [← hg.2]
              dsimp [ResOnSubset, ProjOrd]
              apply Eq.symm
              simp only [ite_eq_right_iff]
              intro hfalse
              exfalso
              exact hi hfalse
        · obtain ⟨g, hg⟩ := hf.1
          obtain ⟨r, hr⟩ := hf.2
          dsimp [rC1', Res]
          dsimp [C1'] at hr
          use ⟨ProjOrd o r.val, ?_⟩
          · dsimp [ResOnSubset] at hr
            have hr' : ProjOrd o r.val = f.val
            · rw [Subtype.ext_iff] at hr
              exact hr.2
            rw [hr']
            have hg' : ProjOrd o g.val = f.val
            · rw [Subtype.ext_iff] at hg
              exact hg.2
            rw [← hg']
            suffices : g.val = ProjOrd o g.val
            · rw [← this]
              exact g.prop
            ext i
            dsimp [ProjOrd]
            split_ifs with hi
            · rfl
            · simp only [not_lt] at hi
              by_cases hi' : i = term I ho
              · rw [hi']
                exact hg.1.2
              · dsimp [Support] at hsC
                simp only [Order.lt_succ_iff, Set.setOf_subset_setOf, forall_exists_index, and_imp]
                    at hsC
                specialize hsC i g.val g.prop
                rw [← not_imp_not] at hsC
                simp only [not_le, Bool.not_eq_true] at hsC
                apply hsC
                refine' lt_of_le_of_ne hi _
                intro hoi
                apply hi'
                dsimp [term]
                simp_rw [hoi]
                dsimp [ord]
                simp only [Ordinal.enum_typein]
          · simp only [Set.mem_image, Set.mem_setOf_eq]
            refine' ⟨⟨r.val, ⟨hr.1, rfl⟩⟩, _⟩
            simp_rw [← hr.2]
            dsimp [ResOnSubset]
            simp only [Subtype.mk.injEq]
            set r' := ProjOrd o r.val with hr'
            ext i
            unfold ProjOrd
            split_ifs with hi
            · rfl
            · rw [hr']
              dsimp [ProjOrd]
              apply Eq.symm
              simp only [ite_eq_right_iff]
              intro hfalse
              exfalso
              exact hi hfalse
      rw [this]
      apply IsOpen.inter
      · sorry
      · sorry
    · apply IsCompact.isClosed
      refine' IsCompact.image _ (continuous_ResOnSubset _ _)
      have CsC : CompactSpace {i // i ∈ C}
      · rw [← isCompact_iff_compactSpace]
        exact hC.isCompact
      apply IsClosed.isCompact
      exact isClosed_rC1' _ hC _
  suffices : rC1' C ho = ((ResOnSubset C o) ⁻¹' V) ∩ (C0' C ho)
  · rw [this]
    exact IsClopen.inter (IsClopen.preimage hV (continuous_ResOnSubset _ _)) (isClopen_C0' C hC ho)
  dsimp
  have hf : Set.InjOn (ResOnSubset C o) (C0' C ho)
  · intro a ha b hb h
    dsimp [C0', C0] at ha hb
    ext i
    dsimp [ResOnSubset] at h
    simp only [Subtype.mk.injEq] at h
    have ht := @trichotomous _ (·<·) inferInstance (ord I i) o
    cases' ht with ht ht
    · dsimp [ProjOrd] at h
      have h' := congr_fun h i
      split_ifs at h' with h''
      · exact h'
      · exfalso
        exact h'' ht
    cases' ht with ht ht
    · have hi : i = term I ho
      · dsimp [term]
        simp_rw [← ht]
        dsimp [ord]
        simp only [Ordinal.enum_typein]
      rw [hi, ha.2, hb.2]
    · dsimp [Support] at hsC
      simp only [Order.lt_succ_iff, Set.setOf_subset_setOf, forall_exists_index, and_imp] at hsC
      have ha' := hsC i a.val a.prop
      have hb' := hsC i b.val b.prop
      rw [← not_imp_not] at ha' hb'
      simp only [not_le, Bool.not_eq_true] at ha' hb'
      rw [ha' ht, hb' ht]
  exact (Set.InjOn.preimage_image_inter hf (rC1_subset_C0 C ho)).symm
  -- ext f
  -- constructor
  -- <;> intro hf
  -- · dsimp [ResOnSubset]
  --   dsimp [C0]
  --   have : (ProjOrd o f.val) (term I ho) = false
  --   · dsimp [ProjOrd, ord, term]
  --     simp only [Ordinal.typein_enum, lt_self_iff_false, ite_false]
  --   have hs : ProjOrd o f.val = f.val
  --   · dsimp [ProjOrd]
  --     ext i
  --     split_ifs with hi
  --     · rfl
  --     · by_cases hi' : i = term I ho
  --       · rw [hi']
  --         exact (rC1_subset_C0 C ho hf).2.symm
  --       · have gt_succ : ¬(ord I i < Order.succ o)
  --         · simp only [Order.lt_succ_iff, not_le]
  --           simp only [not_lt] at hi
  --           refine' lt_of_le_of_ne hi _
  --           intro hoi
  --           apply hi'
  --           dsimp [term]
  --           simp_rw [hoi]
  --           dsimp [ord]
  --           simp only [Ordinal.enum_typein]
  --         dsimp [Support] at hsC
  --         simp only [Order.lt_succ_iff, Set.setOf_subset_setOf, forall_exists_index, and_imp] at hsC
  --         specialize hsC i f.val f.prop
  --         rw [← not_imp_not] at hsC
  --         simp only [Order.lt_succ_iff] at gt_succ
  --         convert hsC gt_succ
  --         simp only [Bool.not_eq_true]
  --         tauto
  --   refine' ⟨⟨_, this⟩ , _⟩
  --   · rw [hs]
  --     exact Subtype.mem f
  --   · rw [hs]
  --     dsimp [Res]
  --     use (SwapTrue o f)
  --     refine' ⟨swapTrue_mem_C1 C hsC ho ⟨f,hf⟩, _⟩
  --     dsimp [ProjOrd ,SwapTrue]
  --     ext i
  --     split_ifs with hi hi'
  --     · exfalso
  --       exact ne_of_lt hi hi'
  --     · rfl
  --     · rw [← hs]
  --       dsimp [ProjOrd]
  --       apply Eq.symm
  --       simp only [ite_eq_right_iff]
  --       intro hi'
  --       exfalso
  --       exact hi hi'
  -- · simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq] at hf
  --   dsimp [rC1']
  --   dsimp [C'] at hf
  --   dsimp [Res]
  --   dsimp [ResOnSubset, Res] at hf
  --   obtain ⟨g,hg⟩ := hf.2
  --   use SwapTrue o (ProjOrd o f)
  --   sorry
  -- suffices : rC1' C ho = p ⁻¹' (C1' C ho)
  -- · rw [this]
  --   refine' IsClopen.preimage (isClopen_C1' C hC ho) _
  --   sorry
  -- sorry
  -- ext x
  -- constructor
  -- · sorry
  -- · have := IsClosed.preimage (continuous_subtype_val : Continuous (fun (i : {i // i ∈ C}) ↦ i.val))
  --     (isClosed_Res _ o (isClosed_C1 C hC ho))
  --   suffices h : rC1' C ho = Subtype.val ⁻¹' (Res (C1 C ho) o)
  --   · rw [h]
  --     exact this
  --   rfl

lemma isClopen_C'' : IsClopen (C'' C ho) := by sorry
  -- suffices : C'' C ho = C0' C ho ∩ rC1' C ho
  -- · rw [this]
  --   exact IsClopen.inter (isClopen_C0' _ hC _) (isClopen_rC1' _ hC _)
  -- dsimp [C'', C', C0', rC1']
  -- rfl

lemma CC_surjective : Function.Surjective (Linear_CC' C hsC ho) := by
  intro f
  have : {i // i ∈ C' C ho} = ↑(C' C ho) := by rfl
  simp_rw [this] at f
  use LocallyConstant.piecewise (isClopen_C0' C hC ho).2 (isClopen_C1' C hC ho).2
    (union_C0'C1'_eq_univ C ho) ?_ ?_ ?_ 0
  · sorry
    -- let f' : LocallyConstant (C'' C ho) ℤ := sorry
    -- use f'.ExtendBy (isClopen_C'' _ hC _) (0 : ℤ)
    -- let g := ((LocallyConstant.equiv (setHomeoSubtype (C'' C ho))).toFun f).ExtendBy (isClopen_C'' _ hC _) (0 : ℤ)
  · sorry
  · sorry
  · sorry
  -- constructor
  -- · ext x
  --   dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁, LocallyConstant.comapLinear]
  --   rw [LocallyConstant.sub_apply]
  --   · sorry
  --   · sorry

lemma CC_comp_zero : ∀ y, (Linear_CC' C hsC ho) ((Linear_ResC C o) y) = 0 := by
  intro y
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁]
  ext x
  rw [LocallyConstant.sub_apply]
  dsimp [Linear_ResC, LocallyConstant.comapLinear]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
  suffices : ResOnSubset C o (CC'₁ C hsC ho x) = ResOnSubset C o (CC'₀ C ho x)
  · rw [this]
    simp only [sub_self]
  dsimp [CC'₀, CC'₁, ResOnSubset, ProjOrd]
  ext i
  dsimp
  split_ifs with h
  · dsimp [SwapTrue]
    split_ifs with h'
    · exfalso
      exact (ne_of_lt h) h'
    · rfl
  · rfl

lemma CC_exact {f : LocallyConstant {i // i ∈ C} ℤ} (hf : Linear_CC' C hsC ho f = 0) :
    ∃ y, Linear_ResC C o y = f := by
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁] at hf
  rw [sub_eq_zero] at hf
  dsimp [LocallyConstant.comapLinear] at hf
  sorry
  -- constructor
  -- · ext x
  --   rw [LocallyConstant.ext_iff] at hf
  --   by_cases hx : x.val ∈ C' C ho
  --   · specialize hf ⟨x,hx⟩
  --     rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)] at hf
  --     rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)] at hf
  --     dsimp [CC'₀, CC'₁] at hf
  --     sorry
  --   · sorry
  -- · sorry


lemma LocallyConstant.ShortExact : CategoryTheory.ShortExact
    (ModuleCat.ofHom (Linear_ResC C o))
    (ModuleCat.ofHom (Linear_CC' C hsC ho)) :=
{ mono := by
    rw [ModuleCat.mono_iff_injective]
    exact LocallyConstant.comap_injective (ResOnSubset C o)
      (continuous_ResOnSubset C o) (surjective_ResOnSubset C o)
  epi := by
    rw [ModuleCat.epi_iff_surjective]
    exact CC_surjective _ hC _ _
  exact := by
    rw [ModuleCat.exact_iff]
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    <;> intro hf
    · obtain ⟨y,hy⟩ := hf
      rw [← hy]
      dsimp [ModuleCat.ofHom]
      exact CC_comp_zero _ _ _ y
    · exact CC_exact _ _ _ hf }

lemma swapTrue_eq_true : ∀ x, SwapTrue o x (term I ho) = true := by
  intro x
  dsimp [SwapTrue]
  split_ifs with h
  · rfl
  · dsimp [ord, term] at h
    simp only [Ordinal.typein_enum, not_true] at h

lemma mem_C'_eq_false : ∀ x, x ∈ C' C ho → x (term I ho) = false := by
  rintro x ⟨_,⟨y,⟨_,hy⟩⟩⟩
  rw [← hy]
  dsimp [ProjOrd]
  split_ifs with h
  · dsimp [ord, term] at h
    simp only [Ordinal.typein_enum, lt_self_iff_false] at h
  · rfl

lemma eo_eq_one : Linear_CC' C hsC ho (e C (term I ho)) = 1 := by
  ext x
  dsimp [Linear_CC', Linear_CC'₁, Linear_CC'₀, LocallyConstant.comapLinear]
  rw [LocallyConstant.sub_apply]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)]
  dsimp [CC'₀, CC'₁, e, BoolToZ]
  split_ifs with h₀ h₁
  · exfalso
    rwa [mem_C'_eq_false C ho x x.prop, Bool.coe_false] at h₁
  · rfl
  · exfalso
    exact h₀ (swapTrue_eq_true ho x)
  · exfalso
    exact h₀ (swapTrue_eq_true ho x)

def LC_eval (x : {i // i ∈ C}) : (LocallyConstant {i // i ∈ C} ℤ) → ℤ :=
fun f ↦ f x

def Products.Apply (l : Products (WithTop I)) (x : {i // i ∈ C}) : List ℤ :=
List.map ((LC_eval C x) ∘ (e C)) l.val

lemma Products.eval_apply (l : Products (WithTop I)) (x : {i // i ∈ C}) :
    l.eval C x = List.prod (Apply C l x) := by
  dsimp [eval, Apply, LC_eval]
  obtain ⟨l,hl⟩ := l
  induction l with
  | nil => rfl
  | cons a as ih =>
    · simp only [List.map, List.prod_cons, LocallyConstant.coe_mul, Pi.mul_apply,
        Function.comp_apply, mul_eq_mul_left_iff]
      specialize ih (List.Chain'.sublist hl (List.tail_sublist (a::as)))
      left
      exact ih

lemma Products.eval_eq (l : Products (WithTop I)) (x : {i // i ∈ C}) :
    l.eval C x = if ∀ i, i ∈ l.val → (x.val i = true) then 1 else 0 := by
  rw [eval_apply]
  split_ifs with h
  · dsimp [Apply]
    suffices : ∀ y, y ∈ List.map (LC_eval C x ∘ e C) l.val → y = 1
    · exact List.prod_eq_one this
    intro y hy
    simp only [List.mem_map, Function.comp_apply] at hy
    obtain ⟨i,hi⟩ := hy
    specialize h i hi.1
    dsimp [LC_eval, e, BoolToZ] at hi
    rw [← hi.2]
    simp only [ite_eq_left_iff]
    exact fun hx ↦ hx h
  · simp only [List.prod_eq_zero_iff]
    dsimp [Apply]
    simp only [List.mem_map, Function.comp_apply]
    push_neg at h
    obtain ⟨i,hi⟩ := h
    use i
    refine' ⟨hi.1,_⟩
    dsimp [LC_eval, e, BoolToZ]
    simp only [ite_eq_right_iff]
    exact hi.2

def GoodProducts.MaxTail (l : StartingWithMax C o) : Products (WithTop I) :=
⟨l.val.val.tail, List.Chain'.tail l.val.prop⟩

lemma GoodProducts.max_eq_o_cons_tail (l : StartingWithMax C o) :
    l.val.val = (term I ho) :: (MaxTail C l).val := by
  rw [← List.cons_head!_tail l.prop.2.1]
  dsimp [MaxTail]
  congr
  dsimp [term]
  simp_rw [← l.prop.2.2]
  dsimp [ord]
  simp only [Ordinal.enum_typein]

lemma GoodProducts.max_eq_eval (l : StartingWithMax C o) :
    Linear_CC' C hsC ho (l.val.eval C) = (MaxTail C l).eval (C' C ho) := by
  have hl' : l.val.val = (term I ho) :: (MaxTail C l).val := max_eq_o_cons_tail C ho l
  have hlc : ((term I ho) :: (MaxTail C l).val).Chain' (·>·)
  · rw [← hl']
    exact l.val.prop
  have hl : l.val = ⟨(term I ho) :: (MaxTail C l).val, hlc⟩
  · simp_rw [← hl']
    rfl
  rw [hl]
  rw [Products.evalCons]
  ext x
  dsimp [Linear_CC', Linear_CC'₁, Linear_CC'₀, LocallyConstant.comapLinear]
  rw [LocallyConstant.sub_apply]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)]
  dsimp [CC'₀, CC'₁]
  rw [Products.eval_eq]
  rw [Products.eval_eq]
  rw [Products.eval_eq]
  simp only [mul_ite, mul_one, mul_zero]
  have hi' : ∀ i, i ∈ (MaxTail C l).val → (x.val i = SwapTrue o x.val i)
  · intro i hi
    dsimp [SwapTrue]
    split_ifs with h₁
    · exfalso
      suffices : i < term I ho
      · dsimp [term] at this
        simp_rw [← h₁] at this
        dsimp [ord] at this
        simp only [Ordinal.enum_typein, lt_self_iff_false] at this
      rw [← gt_iff_lt]
      apply List.Chain.rel _ hi
      exact hlc
    · rfl
  split_ifs with h₁ h₂ h₂
  <;> dsimp [e, BoolToZ]
  · split_ifs with hh₁ hh₂
    · exfalso
      rwa [mem_C'_eq_false C ho x x.prop, Bool.coe_false] at hh₂
    · rfl
    · exfalso
      exact hh₁ (swapTrue_eq_true _ _)
    · exfalso
      exact hh₁ (swapTrue_eq_true _ _)
  · push_neg at h₂
    obtain ⟨i, hi⟩ := h₂
    specialize h₁ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [hi']
  · push_neg at h₁
    obtain ⟨i, hi⟩ := h₁
    specialize h₂ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [← hi']
  · rfl

lemma GoodProducts.max_eq_eval_unapply :
    (Linear_CC' C hsC ho) ∘ (fun (l : StartingWithMax C o) ↦ Products.eval C l.val) =
    (fun l ↦ (MaxTail C l).eval (C' C ho)) := by
  ext1 l
  exact max_eq_eval _ _ _ _

lemma GoodProducts.maxTail_isGood (l : StartingWithMax C o) : (MaxTail C l).isGood (C' C ho) := by
  sorry

lemma Products.head_lt_ord_of_isGood' {l : Products (WithTop I)}
    (h : l.isGood (C' C ho)) : l.val ≠ [] → ord I (l.val.head!) < o := by
  intro hn
  by_contra h'
  apply h
  obtain ⟨l,hl⟩ := l
  dsimp at hn
  have hl' : List.Chain' (·>·) (l.head! :: l.tail)
  · rw [List.cons_head!_tail hn]
    exact hl
  have : (⟨l,hl⟩ : Products (WithTop I)) = ⟨l.head! :: l.tail, hl'⟩
  · simp_rw [List.cons_head!_tail hn]
  rw [this, evalCons (C' C ho) hl']
  have eZero : e (C' C ho) (List.head! l) = 0
  · dsimp [e]
    ext ⟨f,hf⟩
    dsimp [BoolToZ]
    dsimp [C',Res, ProjOrd] at hf
    obtain ⟨g, hg⟩ := hf.2
    rw [← hg.2]
    split_ifs
    · exfalso
      assumption
    · rfl
    · exfalso
      assumption
    · rfl
  rw [eZero]
  simp only [zero_mul, Submodule.zero_mem]

lemma GoodProducts.cons_o_chain' (l : GoodProducts (C' C ho)) :
    (term I ho :: l.val.val).Chain' (·>·) := by
  by_cases hl : l.val.val = []
  · rw [hl]
    simp only [List.chain'_singleton]
  · rw [List.chain'_cons']
    refine' ⟨_,l.val.prop⟩
    intro y hy
    have hy' := List.eq_cons_of_mem_head? hy
    have h := Products.head_lt_ord_of_isGood' C ho l.prop hl
    rw [hy'] at h
    dsimp [term]
    rw [← List.head!_cons y (List.tail l.val.val)]
    simp only [gt_iff_lt]
    rw [← Ordinal.typein_lt_typein (·<·)]
    dsimp [ord] at h
    simpa only [List.head!_cons, Ordinal.typein_enum]


lemma GoodProducts.cons_o_mem_startingWithMax (l : GoodProducts (C' C ho)) :
    ⟨(term I ho :: l.val.val), cons_o_chain' C ho l⟩ ∈ StartingWithMax C o := by
  dsimp [StartingWithMax]
  refine' ⟨_,_,_⟩
  · sorry
  · simp only [not_false_eq_true]
  · dsimp [ord, term]
    simp only [Ordinal.typein_enum]

noncomputable
def GoodProducts.StartingWithMaxEquivGood' : StartingWithMax C o ≃ GoodProducts (C' C ho) :=
{ toFun := fun l ↦ ⟨MaxTail C l, maxTail_isGood C ho l⟩
  invFun := fun l ↦ ⟨⟨(term I ho :: l.val.val), cons_o_chain' C ho l⟩,
    cons_o_mem_startingWithMax C ho l⟩
  left_inv := by
    intro l
    dsimp
    congr
    exact (max_eq_o_cons_tail _ _ _).symm
  right_inv := by
    intro l
    rfl }

lemma GoodProducts.hw :
    LinearIndependent ℤ (eval (C' C ho)) ↔ LinearIndependent ℤ (w C hsC ho) := by
  dsimp [w, u, w']
  rw [max_eq_eval_unapply C hsC ho]
  exact (linearIndependent_equiv (StartingWithMaxEquivGood' C ho)).symm

end Successor

lemma GoodProducts.linearIndependentAux (i : WithTop I) : P i := by
  rw [PIffP I i]
  apply Ordinal.limitRecOn
  · dsimp [P']
    intro C _ hsC
    dsimp [Support] at hsC
    have : C ⊆ {(fun _ ↦ false)}
    · intro c hc
      simp
      ext x
      simp at hsC
      specialize hsC x c hc
      rw [Bool.eq_false_iff]
      intro ht
      apply Ordinal.not_lt_zero (ord I x)
      exact hsC ht
    rw [Set.subset_singleton_iff_eq] at this
    rcases this
    · subst C
      exact linearIndependentEmpty
    · subst C
      exact linearIndependentSingleton
  · intro o h
    dsimp [P'] at *
    intro C hC hsC
    by_cases hnC : Nonempty C
    · by_cases ho : o < Ordinal.type (·<· : WithTop I → WithTop I → Prop)
      · rw [linearIndependent_iff_sum C o hsC]
        suffices : LinearIndependent ℤ (u C o)
        · exact this
        -- Why so slow?
        refine' ModuleCat.linearIndependent_shortExact _ _ _
            (LocallyConstant.ShortExact C hC hsC ho) (huv C o) (huw C hsC ho)
        · exact h (Res C o) (isClosed_Res C o hC) (support_Res_le_o C o)
        · rw [← hw C hsC ho]
          exact h (C' C ho) (isClosed_C' C hC ho) (support_C' C ho)
        · exact injective_u C o hsC
        -- (LocallyConstant.ShortExact C ho)
        -- (injective_u C o)
        -- New approach -/
        -- apply linearIndependent_of_sums_aux C hsC ho
        -- · exact h (C0 C ho) (isClosed_C0 _ hC _) (support_C0 _ hsC _)
        -- · rw [linearIndependent_iff_res]
        --   exact h (Res (C1 C ho) o) (isClosed_Res _ _ (isClosed_C1 _ hC _)) (support_C1 _ _)

        -- Old approach -/
        -- by_cases hnsC : Support C ⊆ {j | ord I j < o}
        -- · exact h C hC hnsC
        -- · rw [linearIndependent_iff_sum C o hsC]
        --   apply LinearIndependent.sum_type
        --   · rw [← linearIndependent_succ_iff]
        --     exact h (Res C o) (isClosed_Res C o hC) (support_Res_le_o C o)
        --   · apply linearIndependent_max_of
        --     exact h (Res C o) (isClosed_Res C o hC) (support_Res_le_o C o)
        --   · exact sum_spans_disjoint C o ho hnsC
      · have hsC' : Support C ⊆ {j | ord I j < o}
        · dsimp [Support]
          simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp]
          intro _ _ _ _
          simp only [not_lt] at ho
          refine' lt_of_lt_of_le _ ho
          dsimp [ord]
          exact Ordinal.typein_lt_type _ _
        exact h C hC hsC'
    · rw [Set.nonempty_coe_sort, Set.not_nonempty_iff_eq_empty] at hnC
      subst hnC
      specialize h ∅ hC
      apply h
      dsimp [Support]
      intro i hi
      simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false] at hi
  · intro o ho h
    dsimp [P'] at *
    intro C hC hsC
    rw [ModProducts.linear_independent_iff C ho hsC]
    refine' linearIndependent_iUnion_of_directed (DirectedS C o) _
    rintro ⟨o', ho'⟩
    specialize h o' ho' (Res C o') (isClosed_Res C o' hC) (support_Res_le_o C o')
    rw [ModProducts.smaller_linear_independent_iff] at h
    exact h

lemma GoodProducts.spanAux (i : WithTop I) : Q i := by
  rw [QIffQ I i]
  have hto : ord I i ≤ Ordinal.type (·<· : (WithTop I) → (WithTop I) → Prop)
  · dsimp [ord]
    exact le_of_lt (Ordinal.typein_lt_type _ _)
  apply Ordinal.limitRecOn
  · dsimp [Q']
    intro _ C _ hsC
    dsimp [Support] at hsC
    have : C ⊆ {(fun a ↦ false)}
    · intro c hc
      simp
      ext x
      simp at hsC
      specialize hsC x c hc
      rw [Bool.eq_false_iff]
      intro ht
      apply Ordinal.not_lt_zero (ord I x)
      exact hsC ht
    rw [Set.subset_singleton_iff_eq] at this
    rcases this
    · subst C
      exact spanEmpty
    · subst C
      exact spanSingleton
  · sorry
  · intro o ho h
    dsimp [Q'] at *
    intro hto C hC hsC
    have hr : ∀ (s : Set (WithTop I → Bool)), Set.range (eval s) = ModProducts s
    · intro
      rfl
    rw [hr C, ModProducts.union C ho hsC, Submodule.span_iUnion]
    intro f _
    haveI : Nonempty {o' // o' < o} := nonempty_downset ho
    simp only [Submodule.mem_iSup_of_directed _ (DirectedSubmodules C o)]
    dsimp [ModProducts.smaller]
    simp only [Submodule.span_image, Submodule.mem_map, Subtype.exists]
    obtain ⟨o',⟨ho',⟨g, hg⟩⟩⟩ := comapLinearJointlySurjective C ho hto hC hsC f
    use o'
    use ho'
    use g
    refine' ⟨_,hg⟩
    specialize h o' ho' (le_of_lt (lt_of_lt_of_le ho' hto)) (Res C o') (isClosed_Res C o' hC)
      (support_Res_le_o C o')
    rw [hr (Res C o'), top_le_iff] at h
    rw [h]
    exact Submodule.mem_top

variable {C₁ : Set (I → Bool)}

lemma isClosedInWithTop (hC₁ : IsClosed C₁) : IsClosed ((r I) '' C₁) :=
(r.embedding I).toEmbedding.toInducing.isClosedMap (r.embedding I).closed_range C₁ hC₁

lemma supportTop (C₁ : Set (I → Bool)) : Support ((r I) '' C₁) ⊆ {j | j < ⊤} := by
  dsimp [Support]
  intro i hi
  obtain ⟨f, hf⟩ := hi
  obtain ⟨c, hc⟩ := hf.1
  rw [← hc.2] at hf
  dsimp [r] at hf
  cases i
  · dsimp at hf
    exfalso
    exact Bool.not_false' hf.2
  · dsimp at hf
    dsimp
    rw [← WithTop.none_eq_top]
    exact WithTop.some_lt_none _

lemma GoodProducts.linearIndependent (hC₁ : IsClosed C₁) :
  LinearIndependent ℤ (GoodProducts.eval ((r I) '' C₁)) :=
GoodProducts.linearIndependentAux ⊤ ((r I) '' C₁) (isClosedInWithTop hC₁) (supportTop C₁)

lemma GoodProducts.span (hC₁ : IsClosed C₁) :
  ⊤ ≤ Submodule.span ℤ (Set.range (GoodProducts.eval ((r I) '' C₁))) :=
GoodProducts.spanAux ⊤ ((r I) '' C₁) (isClosedInWithTop hC₁) (supportTop C₁)

noncomputable
def GoodProducts.Basis (hC₁ : IsClosed C₁) : Basis (GoodProducts ((r I) '' C₁)) ℤ
  (LocallyConstant {i // i ∈ ((r I) '' C₁)} ℤ) :=
Basis.mk (GoodProducts.linearIndependent hC₁) (GoodProducts.span hC₁)

lemma closedFree (hC₁ : IsClosed C₁) : Module.Free ℤ (LocallyConstant {i // i ∈ ((r I) '' C₁)} ℤ) :=
Module.Free.of_basis $ GoodProducts.Basis hC₁

variable {S : Profinite} {ι : S → I → Bool} (hι : ClosedEmbedding ι)

noncomputable
def homeoClosed₁ : S ≃ₜ Set.range ι := Homeomorph.ofEmbedding ι hι.toEmbedding

def rι.embedding : ClosedEmbedding (r I ∘ ι) := ClosedEmbedding.comp (r.embedding I) hι

noncomputable
def homeoClosed₂ : S ≃ₜ Set.range (r I ∘ ι) :=
Homeomorph.ofEmbedding (r I ∘ ι) (rι.embedding hι).toEmbedding

def homeoRange : Set.range (r I ∘ ι) ≃ₜ r I '' Set.range ι := by
  rw [Set.range_comp]
  exact Homeomorph.refl _

def setHomeoSubtype {X : Type _} [TopologicalSpace X] (s : Set X) : s ≃ₜ {x // x ∈ s} :=
{ toFun := fun x ↦ ⟨x.val, x.prop⟩
  invFun := fun x ↦ x
  left_inv := by
    intro x
    dsimp
  right_inv := by
    intro x
    dsimp }

noncomputable
def homeoClosed : S ≃ₜ { i // i ∈ r I '' Set.range ι } :=
(homeoClosed₂ hι).trans (homeoRange.trans (setHomeoSubtype (r I '' Set.range ι)))

noncomputable
def locConstIso (hι : ClosedEmbedding ι) :
  (LocallyConstant S ℤ) ≃ₗ[ℤ] (LocallyConstant { i // i ∈ r I '' Set.range ι } ℤ) :=
LocallyConstant.equivLinear (homeoClosed hι)

lemma Nobeling : Module.Free ℤ (LocallyConstant S ℤ) := Module.Free.of_equiv'
  (closedFree hι.closed_range) (locConstIso hι).symm

end NobelingProof

variable (S : Profinite)

open Classical

noncomputable
def Nobeling.ι : S → ({C : Set S // IsClopen C} → Bool) := fun s C => decide (s ∈ C.1)

instance totally_separated_of_totally_disconnected_compact_hausdorff (α : Type _)
    [TopologicalSpace α] [CompactSpace α] [TotallyDisconnectedSpace α] [T2Space α] :
    TotallySeparatedSpace α := by
  rwa [← compact_t2_tot_disc_iff_tot_sep]

lemma Nobeling.embedding : ClosedEmbedding (Nobeling.ι S) := by
  apply Continuous.closedEmbedding
  · dsimp [ι]
    refine' continuous_pi _
    intro C
    rw [← IsLocallyConstant.iff_continuous]
    refine' ((IsLocallyConstant.tfae _).out 0 3).mpr _
    rintro ⟨⟩
    · have : (fun a ↦ decide (a ∈ C.1)) ⁻¹' {false} = C.1ᶜ
      · ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff,
          decide_eq_false_iff_not, Set.mem_compl_iff]
      · rw [this]
        refine' IsClopen.isOpen _
        simp only [isClopen_compl_iff]
        exact C.2
    · have : (fun a ↦ decide (a ∈ C.1)) ⁻¹' {true} = C.1
      · ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
      · rw [this]
        refine' IsClopen.isOpen _
        exact C.2
  · intro a b hab
    by_contra hnab
    have h' := exists_clopen_of_totally_separated hnab
    obtain ⟨C, hC, h₁⟩ := h'
    apply h₁.2
    have ha : ι S a ⟨C, hC⟩ = decide (a ∈ C) := rfl
    have hb : ι S b ⟨C, hC⟩ = decide (b ∈ C) := rfl
    apply of_decide_eq_true
    rw [← hb, ← hab, ha]
    apply decide_eq_true
    exact h₁.1

theorem Nobeling : Module.Free ℤ (LocallyConstant S ℤ) :=
@NobelingProof.Nobeling {C : Set S // IsClopen C} (IsWellOrder.linearOrder WellOrderingRel)
  WellOrderingRel.isWellOrder S (Nobeling.ι S) (Nobeling.embedding S)
