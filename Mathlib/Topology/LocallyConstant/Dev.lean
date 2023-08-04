import Mathlib.Topology.LocallyConstant.Algebra

namespace Function

noncomputable
def extendBy {α β : Type _} {s : Set α} (f : s → β) (junk : β) [∀ j, Decidable (j ∈ s)] :
    α → β := extend Subtype.val f (fun _ ↦ junk)

@[simp]
lemma extendBy_eq {α β : Type _} {s : Set α} (f : s → β) (junk : β)
    [∀ j, Decidable (j ∈ s)] :
    f.extendBy junk = fun x ↦ if hx : x ∈ s then f ⟨x, hx⟩ else junk := by
  ext x
  dsimp [extendBy]
  split_ifs with h
  · rw [← Subtype.coe_injective.extend_apply f (fun _ ↦ junk)]
  · rw [Function.extend_apply']
    rintro ⟨a, ha⟩
    apply h
    convert a.prop
    exact ha.symm

#find_home Function.extendBy

lemma restrict_extendBy_eq_self {α β : Type _} {s : Set α} (f : s → β) (junk : β)
    [∀ j, Decidable (j ∈ s)] : s.restrict (f.extendBy junk) = f := by
  ext x
  simp

lemma extendBy_preimage_of_junk_ne_mem {α β : Type _} {s : Set α} (f : s  → β) (junk : β)
    (t : Set β) (hj : ¬ junk ∈ t) [∀ j, Decidable (j ∈ s)] :
    (f.extendBy junk) ⁻¹' t = Subtype.val '' (f ⁻¹' t) := by
  ext x
  simp
  refine' ⟨fun hx ↦ _, fun hx ↦ _⟩
  · split_ifs at hx with h
    · use h
    · exfalso
      exact hj hx
  · obtain ⟨_,_⟩ := hx
    split_ifs
    assumption

lemma extendBy_preimage_of_junk_mem {α β : Type _} {s : Set α} (f : s  → β) (junk : β)
    (t : Set β) (hj : junk ∈ t) [∀ j, Decidable (j ∈ s)] :
    (f.extendBy junk) ⁻¹' t = Subtype.val '' (f ⁻¹' t) ∪ sᶜ := by
  ext x
  simp
  refine' ⟨fun hx ↦ _, fun hx ↦ _⟩
  · split_ifs at hx with h
    · left
      use h
    · right
      exact h
  · obtain ⟨_,_⟩ := hx
    split_ifs
    · assumption
    · split_ifs
      assumption

end Function

namespace Set

noncomputable
def piecewise' {α β : Type _} {s t : Set α} (f : s → β)
    (g : t → β) (junk : β) [∀ j, Decidable (j ∈ s)] [∀ j, Decidable (j ∈ t)] : α → β :=
  s.piecewise (f.extendBy junk) (g.extendBy junk)

end Set

namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {Z : Type _}

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

lemma isLocallyConstant_piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ)
    (f : LocallyConstant {i // i ∈ C₁} Z)
    (g : LocallyConstant {i // i ∈ C₂} Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f.toFun ⟨x, hx.1⟩ = g.toFun ⟨x, hx.2⟩)
    (junk : Z) [∀ j, Decidable (j ∈ C₁)] [∀ j, Decidable (j ∈ C₂)] :
    IsLocallyConstant (C₁.piecewise' f.toFun g.toFun junk) := by
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
    rw [Function.extendBy_eq, Function.extendBy_eq]
    dsimp
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
    (junk : Z) [∀ j, Decidable (j ∈ C₁)] [∀ j, Decidable (j ∈ C₂)] : LocallyConstant X Z :=
{ toFun := C₁.piecewise' f.toFun g.toFun junk
  isLocallyConstant := isLocallyConstant_piecewise h₁ h₂ h f g hfg junk}

-- noncomputable
-- def extendBy {C : Set X} (hC : IsClopen C) (f : LocallyConstant {i // i ∈ C} Z) (junk : Z) :
--     LocallyConstant X Z :=
-- { toFun := f.toFun.extendBy junk
--   isLocallyConstant := by
--     intro s
--     by_cases hj : junk ∈ s
--     · rw [Function.extendBy_preimage_of_junk_mem _ _ _ hj]
--       refine' IsOpen.union _ hC.compl.1
--       exact IsOpen.isOpenMap_subtype_val hC.1 (f.toFun ⁻¹' s) (f.isLocallyConstant s)
--     · rw [Function.extendBy_preimage_of_junk_ne_mem _ _ _ hj]
--       exact IsOpen.isOpenMap_subtype_val hC.1 (f.toFun ⁻¹' s) (f.isLocallyConstant s) }

-- noncomputable
-- def emb_lift {e : X → Y} (hoe : OpenEmbedding e) (hce : ClosedEmbedding e)
--     (f : LocallyConstant X Z) (junk : Z) : LocallyConstant Y Z :=
--   let E : LocallyConstant X Z ≃ LocallyConstant (Set.range e) Z :=
--     equiv (Homeomorph.ofEmbedding e hoe.toEmbedding)
--   (E f).extendBy ⟨hoe.open_range, hce.closed_range⟩ junk

theorem comap_comp_apply {α : Type _} [TopologicalSpace Z] (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) :
    ∀ (x : LocallyConstant Z α), comap f (comap g x) = comap (g ∘ f) x :=
  fun _ ↦ by rw [← comap_comp f g hf hg]; rfl

noncomputable
def equiv (e : X ≃ₜ Y) : LocallyConstant X Z ≃ LocallyConstant Y Z :=
{ toFun := comap e.invFun
  invFun := comap e.toFun
  left_inv := by
    intro x
    rw [comap_comp_apply _ _ e.continuous_toFun e.continuous_invFun x]
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
    dsimp
    ext x
    simp only [coe_mul, Pi.mul_apply]
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    simp only [coe_mul, Pi.mul_apply]


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
def LinearSumEquivProd :
    LocallyConstant (X ⊕ Y) Z ≃ₗ[R] LocallyConstant X Z × LocallyConstant Y Z :=
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
