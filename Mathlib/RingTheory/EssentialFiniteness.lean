import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.TensorProduct.Basic


variable (R S T) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
variable [IsScalarTower R S T]

class EssFiniteType : Prop where
  cond : ∃ (s : Finset S),
    IsLocalization ((IsUnit.submonoid S).comap (algebraMap (Algebra.adjoin R (s : Set S)) S)) S

lemma essFiniteType_cond_iff (σ : Finset S) :
 IsLocalization ((IsUnit.submonoid S).comap (algebraMap (Algebra.adjoin R (σ : Set S)) S)) S ↔
    (∀ s : S, ∃ t ∈ Algebra.adjoin R (σ : Set S),
      IsUnit t ∧ s * t ∈ Algebra.adjoin R (σ : Set S)) := by
  constructor <;> intro hσ
  · intro s
    obtain ⟨⟨⟨x, hx⟩, ⟨t, ht⟩, ht'⟩, h⟩ := hσ.2 s
    exact ⟨t, ht, ht', h ▸ hx⟩
  · constructor
    · exact fun y ↦ y.prop
    · intro s
      obtain ⟨t, ht, ht', h⟩ := hσ s
      exact ⟨⟨⟨_, h⟩, ⟨t, ht⟩, ht'⟩, rfl⟩
    · intros x y e
      use 1
      simp only [Submonoid.coe_comap, OneMemClass.coe_one, one_mul]
      ext
      exact e

lemma essFiniteType_iff :
  EssFiniteType R S ↔ ∃ (σ : Finset S),
    (∀ s : S, ∃ t ∈ Algebra.adjoin R (σ : Set S),
      IsUnit t ∧ s * t ∈ Algebra.adjoin R (σ : Set S)) := by
  simp_rw [← essFiniteType_cond_iff]
  constructor <;> exact fun ⟨a, b⟩ ↦ ⟨a, b⟩

instance EssFiniteType.of_finiteType [hs : Algebra.FiniteType R S] : EssFiniteType R S := by
  obtain ⟨s, hs⟩ := hs
  rw [essFiniteType_iff]
  use s
  simp only [hs, Algebra.mem_top, true_and]
  intro _
  exact ⟨1, isUnit_one, trivial⟩

variable {R} in
lemma EssFiniteType.of_isLocalization (M : Submonoid R) [IsLocalization M S] :
    EssFiniteType R S := by
  rw [essFiniteType_iff]
  use ∅
  simp only [Finset.coe_empty, Algebra.adjoin_empty, exists_and_left, Algebra.mem_bot,
    Set.mem_range, exists_exists_eq_and]
  intro s
  obtain ⟨⟨x, t⟩, e⟩ := IsLocalization.surj M s
  exact ⟨_, IsLocalization.map_units S t, x, e.symm⟩

lemma EssFiniteType.of_id : EssFiniteType R R := inferInstance

lemma EssFiniteType.aux (σ : Subalgebra R S)
    (hσ : ∀ s : S, ∃ t ∈ σ, IsUnit t ∧ s * t ∈ σ)
    (τ : Set T) (t : T) (ht : t ∈ Algebra.adjoin S τ) :
    ∃ s ∈ σ, IsUnit s ∧ s • t ∈ σ.map (IsScalarTower.toAlgHom R S T) ⊔ Algebra.adjoin R τ := by
  refine' Algebra.adjoin_induction ht _ _ _ _ <;> clear ht t
  · intro t ht
    exact ⟨1, Subalgebra.one_mem _, isUnit_one,
      (one_smul S t).symm ▸ Algebra.mem_sup_right (Algebra.subset_adjoin ht)⟩
  · intro s
    obtain ⟨s', hs₁, hs₂, hs₃⟩ := hσ s
    refine ⟨_, hs₁, hs₂, Algebra.mem_sup_left ?_⟩
    rw [Algebra.smul_def, ← map_mul, mul_comm]
    exact ⟨_, hs₃, rfl⟩
  · rintro x y ⟨sx, hsx, hsx', hsx''⟩ ⟨sy, hsy, hsy', hsy''⟩
    refine ⟨_, σ.mul_mem hsx hsy, hsx'.mul hsy', ?_⟩
    rw [smul_add, mul_smul, mul_smul, Algebra.smul_def sx (sy • y), smul_comm,
      Algebra.smul_def sy (sx • x)]
    apply add_mem (mul_mem _ hsx'') (mul_mem _ hsy'') <;>
      exact Algebra.mem_sup_left ⟨_, ‹_›, rfl⟩
  · rintro x y ⟨sx, hsx, hsx', hsx''⟩ ⟨sy, hsy, hsy', hsy''⟩
    refine ⟨_, σ.mul_mem hsx hsy, hsx'.mul hsy', ?_⟩
    rw [mul_smul, ← smul_eq_mul, smul_comm sy x, ← smul_assoc, smul_eq_mul]
    exact mul_mem hsx'' hsy''

lemma EssFiniteType.comp [h₁ : EssFiniteType R S] [h₂ : EssFiniteType S T] :
    EssFiniteType R T := by
  rw [essFiniteType_iff] at h₁ h₂ ⊢
  classical
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  use s.image (IsScalarTower.toAlgHom R S T) ∪ t
  simp only [Finset.coe_union, Finset.coe_image, Algebra.adjoin_union, Algebra.adjoin_image]
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := ht x
  obtain ⟨t₁, h₁, h₂, h₃⟩ := EssFiniteType.aux _ _ _ _ hs _ y hy₁
  obtain ⟨t₂, h₄, h₅, h₆⟩ := EssFiniteType.aux _ _ _ _ hs _ _ hy₃
  refine ⟨t₂ • t₁ • y, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact mul_mem (Algebra.mem_sup_left ⟨_, h₄, rfl⟩) h₃
  · rw [Algebra.smul_def, Algebra.smul_def]
    exact (h₅.map _).mul ((h₂.map _).mul hy₂)
  · rw [← mul_smul, mul_comm, smul_mul_assoc, mul_comm, mul_comm y, mul_smul, Algebra.smul_def]
    exact mul_mem (Algebra.mem_sup_left ⟨_, h₁, rfl⟩) h₆

noncomputable
def EssFiniteType.finset [h : EssFiniteType R S] : Finset S := h.cond.choose

lemma EssFiniteType.isLocalization [h : EssFiniteType R S] :
    IsLocalization ((IsUnit.submonoid S).comap
      (algebraMap (Algebra.adjoin R (finset R S : Set S)) S)) S :=
  h.cond.choose_spec

lemma EssFiniteType.ext [EssFiniteType R S]
    (f g : S →ₐ[R] T) (H : ∀ s ∈ finset R S, f s = g s) : f = g := by
  have := EssFiniteType.isLocalization R S
  suffices f.toRingHom = g.toRingHom by ext; exact RingHom.congr_fun this _
  apply IsLocalization.ringHom_ext ((IsUnit.submonoid S).comap
      (algebraMap (Algebra.adjoin R (finset R S : Set S)) S))
  suffices f.comp (IsScalarTower.toAlgHom R _ S) = g.comp (IsScalarTower.toAlgHom R _ S) by
    ext; exact AlgHom.congr_fun this _
  apply AlgHom.ext_of_adjoin_eq_top (s := { x | x.1 ∈ finset R S })
  · rw [← top_le_iff]
    rintro x _
    refine' Algebra.adjoin_induction' _ _ _ _ x
    · intro x hx; exact Algebra.subset_adjoin hx
    · intro r; exact Subalgebra.algebraMap_mem _ _
    · intro x y hx hy; exact add_mem hx hy
    · intro x y hx hy; exact mul_mem hx hy
  · rintro ⟨x, hx⟩ hx'; exact H x hx'

open TensorProduct in
instance EssFiniteType.baseChange [h : EssFiniteType R S] : EssFiniteType T (T ⊗[R] S) := by
  classical
  rw [essFiniteType_iff] at h ⊢
  obtain ⟨σ, hσ⟩ := h
  use σ.image Algebra.TensorProduct.includeRight
  intro s
  induction' s using TensorProduct.induction_on with x y x y hx hy
  · exact ⟨1, one_mem _, isUnit_one, by simpa using zero_mem _⟩
  · obtain ⟨t, h₁, h₂, h₃⟩ := hσ y
    have H : ∀ x : S, x ∈ Algebra.adjoin R (σ : Set S) →
        1 ⊗ₜ[R] x ∈ Algebra.adjoin T
          ((σ.image Algebra.TensorProduct.includeRight : Finset (T ⊗[R] S)) : Set (T ⊗[R] S)) := by
      intro x hx
      have : Algebra.TensorProduct.includeRight x ∈
          (Algebra.adjoin R (σ : Set S)).map (Algebra.TensorProduct.includeRight (A := T)) :=
        Subalgebra.mem_map.mpr ⟨_, hx, rfl⟩
      rw [← Algebra.adjoin_adjoin_of_tower R]
      apply Algebra.subset_adjoin
      simpa [← Algebra.adjoin_image] using this
    refine ⟨Algebra.TensorProduct.includeRight t, H _ h₁, h₂.map _, ?_⟩
    simp only [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one]
    rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    apply Subalgebra.smul_mem
    exact H _ h₃
  · obtain ⟨tx, hx₁, hx₂, hx₃⟩ := hx
    obtain ⟨ty, hy₁, hy₂, hy₃⟩ := hy
    refine ⟨_, mul_mem hx₁ hy₁, hx₂.mul hy₂, ?_⟩
    rw [add_mul, ← mul_assoc, mul_comm tx ty, ← mul_assoc]
    exact add_mem (mul_mem hx₃ hy₁) (mul_mem hy₃ hx₁)

lemma EssFiniteType.of_comp [h : EssFiniteType R T] : EssFiniteType S T := by
  rw [essFiniteType_iff] at h ⊢
  classical
  obtain ⟨σ, hσ⟩ := h
  use σ
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := hσ x
  simp_rw [← Algebra.adjoin_adjoin_of_tower R (S := S) (σ : Set T)]
  exact ⟨y, Algebra.subset_adjoin hy₁, hy₂, Algebra.subset_adjoin hy₃⟩
