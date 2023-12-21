import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Finiteness
import Mathlib.Data.Fintype.BigOperators

universe u v

variable {ι : Type u} [DecidableEq ι] [Fintype ι] (f : ι → Type v) [∀ i, Semiring (f i)]

namespace Ideal

variable {f}

def Pi (I : (Π i, Ideal (f i))) : Ideal (Π i, f i) where
  carrier := { f | ∀ i, f i ∈ I i }
  add_mem' h h' i := (I i).add_mem (h i) (h' i)
  zero_mem' i := (I i).zero_mem
  smul_mem' r _ h i := (I i).smul_mem (r i) (h i)

@[simp] lemma mem_Pi (I : (Π i, Ideal (f i))) (x : Π i, f i) : x ∈ Pi I ↔ ∀ i, x i ∈ I i :=
  Iff.rfl

open BigOperators in
lemma Pi_eq (I : Ideal (Π i, f i)) :
    I = Pi fun i ↦ map (Pi.evalRingHom f i) I := by
  classical
  ext x
  fconstructor
  · intro hx i
    rw [mem_map_iff_of_surjective (hf := fun z ↦ ⟨Pi.single i z, by simp⟩)]
    refine ⟨x, hx, rfl⟩
  · intro hx
    change ∀ i, x i ∈ map (Pi.evalRingHom f i) I at hx
    replace hx : ∀ i, ∃ y, y ∈ I ∧ y i = x i
    · intro i
      specialize hx i
      rw [mem_map_iff_of_surjective (hf := fun z ↦ ⟨Pi.single i z, by simp⟩)] at hx
      exact hx
    choose y hy1 hy2 using hx
    replace hy1 : ∀ i, Pi.single i 1 * y i ∈ I := fun i ↦ Ideal.mul_mem_left _ _ (hy1 i)
    rw [show x = ∑ i, Pi.single i 1 * y i by
    · ext j
      simp only [Finset.sum_apply, Pi.mul_apply, ne_eq]
      trans ∑ i, if i = j then y i j else 0
      · simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using (hy2 j).symm
      · exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> aesop]
    exact I.sum_mem fun j _ ↦ hy1 j

def unPi (I : Ideal (Π i, f i)) (i : ι) : Ideal (f i) :=
  map (Pi.evalRingHom f i) I

lemma mem_unPi (I : Ideal (Π i, f i)) {i : ι} (x : f i) :
    x ∈ unPi I i ↔ ∃ y ∈ I, y i = x :=
  mem_map_iff_of_surjective (hf := fun z ↦ ⟨Pi.single i z, by simp⟩)

lemma mem_prod_of_ideals (I : Ideal (Π i, f i)) (x : Π i, f i) :
    x ∈ I ↔ ∀ i, x i ∈ unPi I i := by
  fconstructor
  · intro H i
    rw [mem_unPi]
    exact ⟨_, H, rfl⟩
  · rw [Pi_eq I]
    intro H i
    specialize H i
    rw [mem_unPi] at H
    obtain ⟨y, hy1, hy2⟩ := H
    exact hy2 ▸ hy1 i


def PiEquiv : (Π i, Ideal (f i)) ≃ Ideal (Π i, f i) where
  toFun := Pi
  invFun := unPi
  left_inv I := by
    rw [Pi_eq (Pi I)]
    ext i r
    rw [mem_unPi]
    simp only [mem_Pi, Pi.evalRingHom_apply]
    fconstructor
    · rintro ⟨x, hx1, rfl⟩
      specialize hx1 i
      rw [mem_map_iff_of_surjective (hf := fun z ↦ ⟨Pi.single i z, by simp⟩)] at hx1
      obtain ⟨y, hy1, hy2⟩ := hx1
      simp only [Pi.evalRingHom_apply] at hy2
      rw [← hy2]
      exact hy1 i
    · intro H
      refine ⟨Pi.single i r, ?_, by simp⟩
      intro j
      rw [mem_map_iff_of_surjective (hf := fun z ↦ ⟨Pi.single j z, by simp⟩)]
      refine ⟨Pi.single i r, ?_, rfl⟩
      intro k
      by_cases eq1 : i = k
      · subst eq1; simpa
      · rw [Pi.single_eq_of_ne' eq1]; exact Submodule.zero_mem _
  right_inv I := by
    ext x
    simp only [mem_Pi, mem_unPi]
    rw [Pi_eq I]
    fconstructor
    · intro H i
      specialize H i
      obtain ⟨y, hy1, hy2⟩ := H
      exact hy2 ▸ hy1 i
    · intro H i
      specialize H i
      rw [mem_map_iff_of_surjective (hf := fun z ↦ ⟨Pi.single i z, by simp⟩)] at H
      obtain ⟨y, hy1, hy2⟩ := H
      exact ⟨y, Pi_eq I ▸ hy1, hy2⟩

open BigOperators in
lemma Pi_fg_of_unPi_fg (I : Ideal (Π i, f i)) (H : ∀ i, (unPi I i).FG) : I.FG := by
  choose s hs using H
  classical
  let S : Finset (Π i, f i) := Finset.biUnion (@Finset.univ ι _) <| fun i ↦ s i |>.map
    { toFun := Pi.single _
      inj' := Pi.single_injective _ _ }
  refine ⟨S, ?_⟩
  simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Finset.coe_map,
    Function.Embedding.coeFn_mk, Set.iUnion_true]
  rw [Ideal.span_iUnion]
  refine le_antisymm ?_ ?_
  · simp_rw [iSup_le_iff, Ideal.span_le]
    rintro i - ⟨x, hx, rfl⟩
    rw [show I = Pi (unPi I) from (PiEquiv.apply_symm_apply I).symm]
    intro j
    by_cases eq1 : i = j
    · subst eq1
      simpa using hs i ▸ Ideal.subset_span hx
    · simp [Pi.single_eq_of_ne' eq1]
  · intro x hx
    simp_rw [mem_prod_of_ideals, mem_unPi] at hx
    choose y hy1 hy2 using hx
    replace hy1 : ∀ i, Pi.single i 1 * y i ∈ I := fun i ↦ Ideal.mul_mem_left _ _ (hy1 i)
    rw [show x = ∑ i, Pi.single i 1 * y i by
    · ext j
      simp only [Finset.sum_apply, Pi.mul_apply, ne_eq]
      trans ∑ i, if i = j then y i j else 0
      · simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using (hy2 j).symm
      · exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> aesop]
    refine Ideal.sum_mem _ fun i _ ↦ Ideal.mem_iSup_of_mem i <| ?_
    simp_rw [show ∀ i, Pi.single i 1 * y i = Pi.single i (y i i) by
      intro i
      ext j
      by_cases eq1 : i = j
      · subst eq1; simp
      · simp [Pi.single_eq_of_ne' eq1]] at hy1 ⊢
    specialize hs i
    have mem1 : (y i i) ∈ unPi I i
    · rw [mem_unPi]
      exact ⟨_, hy1 i, by simp⟩
    rw [← hs] at mem1
    refine Submodule.span_induction mem1 ?_ ?_ ?_ ?_
    · intro _ h
      exact Ideal.subset_span <| by simpa using h
    · simp
    · intro _ _ h₁ h₂
      rw [Pi.single_add]
      exact Submodule.add_mem _ h₁ h₂
    · intro _ _ h
      rw [smul_eq_mul, Pi.single_mul]
      exact Ideal.mul_mem_left _ _ h

end Ideal
