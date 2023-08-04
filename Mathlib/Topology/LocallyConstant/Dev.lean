import Mathlib.Topology.LocallyConstant.Algebra

namespace Set

def piecewise' {α : Type u} {β : α → Sort v} (s : Set α) (f : ∀ i : s, β i.val)
    (g : ∀ i : (sᶜ : Set α), β i.val) [∀ j, Decidable (j ∈ s)] : ∀ i, β i :=
  fun i ↦ if h : i ∈ s then f ⟨i, h⟩ else g ⟨i, h⟩

lemma restrict_piecewise'_eq_self {α β : Type _} (s : Set α) (f : s → β)
    (g : {i // i ∈ sᶜ} → β) [∀ j, Decidable (j ∈ s)] :
    s.restrict (s.piecewise' f g : α → β) = f := by
  ext x
  dsimp [piecewise']
  split_ifs with h
  · rfl
  · exfalso
    exact h x.prop

lemma restrict_piecewise'_eq_self_compl' {α β : Type _} (s t : Set α) (f : s → β)
    (g : t → β) (hst : sᶜ ⊆ t) (hfg : ∀ x (hx : x ∈ s ∩ t), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩)
    [∀ j, Decidable (j ∈ s)] :
    t.restrict (s.piecewise' f (g ∘ Set.inclusion hst) : α → β) = g := by
  ext x
  dsimp [piecewise']
  split_ifs with h
  · rw [hfg x ⟨h, x.prop⟩]
  · rfl

lemma restrict_piecewise'_eq_self_compl {α β : Type _} (s : Set α) (f : s → β)
    (g : {i // i ∈ sᶜ} → β) [∀ j, Decidable (j ∈ s)] :
    (sᶜ).restrict (s.piecewise' f g : α → β) = g := by
  ext x
  dsimp [piecewise']
  split_ifs with h
  · exfalso
    exact x.prop h
  · rfl

end Set

namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {Z : Type _}

lemma isLocallyConstant_piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ)
    (f : LocallyConstant {i // i ∈ C₁} Z)
    (g : LocallyConstant {i // i ∈ C₂} Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f.toFun ⟨x, hx.1⟩ = g.toFun ⟨x, hx.2⟩)
    [∀ j, Decidable (j ∈ C₁)] :
    IsLocallyConstant (C₁.piecewise' f.toFun
    (g.toFun ∘ Set.inclusion (Set.compl_subset_iff_union.mpr h))) := by
  let dZ : TopologicalSpace Z := ⊥
  haveI : DiscreteTopology Z := discreteTopology_bot Z
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  rw [IsLocallyConstant.iff_continuous] at hf hg ⊢
  dsimp
  rw [Set.union_eq_iUnion] at h
  refine' (locallyFinite_of_finite _).continuous h (fun i ↦ _) (fun i ↦ _)
  · cases i; exact h₂; exact h₁
  · cases i
    <;> rw [continuousOn_iff_continuous_restrict]
    · rw [Set.restrict_piecewise'_eq_self_compl']
      · exact hg
      · exact hfg
    · dsimp
      rw [Set.restrict_piecewise'_eq_self]
      exact hf

noncomputable
def piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ)
    (f : LocallyConstant {i // i ∈ C₁} Z)
    (g : LocallyConstant {i // i ∈ C₂} Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f.toFun ⟨x, hx.1⟩ = g.toFun ⟨x, hx.2⟩)
    [∀ j, Decidable (j ∈ C₁)] : LocallyConstant X Z :=
{ toFun := C₁.piecewise' f.toFun ((g.toFun ∘ Set.inclusion (Set.compl_subset_iff_union.mpr h)))
  isLocallyConstant := isLocallyConstant_piecewise h₁ h₂ h f g hfg}

theorem comap_comp_apply {α : Type _} [TopologicalSpace Z] (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) (x : LocallyConstant Z α) :
    comap f (comap g x) = comap (g ∘ f) x := by
  rw [← comap_comp f g hf hg]; rfl

noncomputable
def equiv (e : X ≃ₜ Y) : LocallyConstant X Z ≃ LocallyConstant Y Z where
  toFun := comap e.invFun
  invFun := comap e.toFun
  left_inv := by
    intro x
    rw [comap_comp_apply _ _ e.continuous_toFun e.continuous_invFun x]
    simp
  right_inv := by
    intro x
    rw [comap_comp_apply _ _ e.continuous_invFun e.continuous_toFun]
    simp

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

noncomputable
def comapMul [MulOneClass Z] (f : X → Y) (hf : Continuous f) :
    LocallyConstant Y Z →* LocallyConstant X Z where
  toFun := comap f
  map_one' := by
    ext x
    rw [coe_comap_apply _ _ hf]
    rfl
  map_mul' := by
    intro r s
    ext x
    simp
    rw [coe_comap_apply _ _ hf, coe_comap_apply _ _ hf, coe_comap_apply _ _ hf]
    simp

variable {R : Type _} [Ring R] [AddCommMonoid Z] [Module R Z]

noncomputable
def comapLinear (f : X → Y) (hf : Continuous f) :
    LocallyConstant Y Z →ₗ[R] LocallyConstant X Z where
  toFun := comap f
  map_add' := by
    intro r s
    ext x
    simp
    rw [coe_comap_apply _ _ hf, coe_comap_apply _ _ hf, coe_comap_apply _ _ hf]
    rfl
  map_smul' := by
    intro r s
    ext x
    simp
    rw [coe_comap_apply _ _ hf, coe_comap_apply _ _ hf]
    rfl

lemma comapLinear_injective (f : X → Y) (hf : Continuous f) (hfs : Function.Surjective f) :
    LinearMap.ker (comapLinear f hf : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z) = ⊥ := by
  apply LinearMap.ker_eq_bot_of_injective
  dsimp [comapLinear]
  exact comap_injective _ hf hfs

noncomputable
def equivLinear (e : X ≃ₜ Y) : LocallyConstant X Z ≃ₗ[R] LocallyConstant Y Z :=
{ toFun := (equiv e).toFun
  map_smul' := (comapLinear _ e.continuous_invFun).map_smul'
  map_add' := by -- note: (comapLinear _ e.continuous_invFun).map_add' doesn't work.
    intro r s
    ext x
    dsimp [equiv]
    have hf : Continuous ↑(e.symm) := e.continuous_invFun
    rw [coe_comap_apply _ _ hf, coe_comap_apply _ _ hf, coe_comap_apply _ _ hf]
    rfl
  invFun := (equiv e).invFun
  left_inv := (equiv e).left_inv
  right_inv := (equiv e).right_inv }

end LocallyConstant
