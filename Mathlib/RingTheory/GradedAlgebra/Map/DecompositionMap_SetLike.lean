module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Map.auxiliary
public import Mathlib.RingTheory.GradedAlgebra.Map.AddSubmonoidSSup

@[expose] public section


open DirectSum

section toIsup
open DirectSum
variable {M : Type*} [AddCommMonoid M]
variable {ι : Type*} [DecidableEq ι]
variable {σ : Type*} [SetLike σ M] [AddSubmonoidClass σ M]
                     [CompleteLattice σ] [AddSubmonoidClass.IsConcreteSSup σ M]
variable (ℳ : ι → σ)

-- TODO: Some of the following should be private
def codomain_equal :
   ↥(⨆ i, AddSubmonoid.ofClass (ℳ i)) ≃+ ↥(⨆ i, ℳ i : σ)  :=
   (AddEquiv.addSubmonoidCongr (AddSubmonoidClass.iSup_toAddSubmonoid ℳ).symm)

def toIsup_ : (⨁ i, ℳ i) →+ ↥(⨆ i, AddSubmonoid.ofClass (ℳ i)) :=
  DirectSum.toAddMonoid
  (fun i ↦ AddSubmonoid.inclusion (le_iSup (fun i ↦ AddSubmonoid.ofClass (ℳ i)) i))

@[irreducible]
def SetLike.toIsup
  : (⨁ i, ℳ i) →+ ↥(⨆ i, ℳ i : σ)
  := (codomain_equal ℳ).toAddMonoidHom.comp (toIsup_ ℳ)

@[simp]
lemma SetLike.toIsup_of
  (i : ι) (m : ℳ i) :
  (SetLike.toIsup ℳ) (of (fun i ↦ ↥(ℳ i)) i m) = m.val := by
  unfold SetLike.toIsup toIsup_ codomain_equal
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
  Function.comp_apply, toAddMonoid_of]
  rfl

private lemma SetLike.toIsup_surjective : Function.Surjective (toIsup ℳ) := by
  unfold SetLike.toIsup
  apply (codomain_equal ℳ).surjective.comp
  intro ⟨y, hy'⟩
  have ⟨a, ha⟩ : ∃ a, ((toIsup_ ℳ) a : M) = y := by
    unfold toIsup_
    induction hy' using AddSubmonoid.iSup_induction' with
    | mem i x hxS => exact ⟨DirectSum.of _ i ⟨x, hxS⟩,
        by rw [toAddMonoid_of]; rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y u v hx hy =>
      rw [←AddSubmonoidClass.iSup_toAddSubmonoid] at u v
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by simp [ha, hb]⟩
  subst ha
  simp_all only [Subtype.coe_eta, exists_apply_eq_apply]
end toIsup


section Decomposition
/- MAIN PART:  Construction of induced decomposition -/

universe u
variable {M : Type*} [AddCommMonoid M]
variable {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
variable (f : ι₁ → ι₂)
variable {σ : Type*} [SetLike σ M] [CompleteLattice σ]
variable (ℳ : ι₁ → σ)

def DirectSum.Decomposition.map : ι₂ → σ
  := fun j ↦ iSup (fun i : { i : ι₁ // f i = j} ↦ ℳ i)

variable [AddSubmonoidClass σ M] [AddSubmonoidClass.IsConcreteSSup σ M]
variable [DirectSum.Decomposition ℳ]

abbrev Dec' := ⨁ j, (Decomposition.map f ℳ) j
abbrev sigma := (DirectSum.sigmaFiberAddEquiv f (β := fun i ↦ ↥(ℳ i))).toAddMonoidHom
abbrev decomp := (decomposeAddEquiv ℳ).toAddMonoidHom
abbrev decomp' : M →+ (⨁ j, (Decomposition.map f ℳ) j) :=
    (map (fun (j : ι₂)
    ↦ SetLike.toIsup (ℳ := (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i))))).comp
    ((sigma f ℳ).comp (decomp ℳ))


@[implicit_reducible]
def DirectSum.Decomposition.map.decomposition :
  (DirectSum.Decomposition (Decomposition.map f ℳ) )
  :=
  DirectSum.Decomposition.ofAddHom
    (Decomposition.map f ℳ)
    (decomp' f ℳ)
    (by
    -- 2 reduction steps:
      rw [← AddMonoidHom.cancel_right (decomposeAddEquiv ℳ).symm.surjective]
      refine addHom_ext' (fun j ↦ ?_)
    -- now simplify everything:
      unfold Decomposition.map
      ext m
      simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
        Function.comp_apply, coeAddMonoidHom_of, decomposeAddEquiv_apply, decompose_coe,
        sigmaFiberAddEquiv_of, map_of, SetLike.toIsup_of, AddMonoidHom.id_comp]
      ) (by
    -- 3 reduction steps:
      refine addHom_ext' (fun j ↦ ?_)
      unfold Decomposition.map -- needed in v4.29r8, but not in v4.28.0
      rw [← AddMonoidHom.cancel_right
        (SetLike.toIsup_surjective (fun (i : { i : ι₁ // f i = j}) ↦ ((ℳ ↑i)))) ]
      refine addHom_ext' (fun ⟨i, hi⟩ ↦ ?_)
    -- now simplify everything:
      subst hi
      ext m : 1
      simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
        Function.comp_apply, coeAddMonoidHom_of, SetLike.toIsup_of, decomposeAddEquiv_apply,
        decompose_coe, sigmaFiberAddEquiv_of, map_of, AddMonoidHom.id_comp]
      )
end Decomposition

section gradedAlgebra.map
universe u
variable {ι₁ ι₂ : Type u}
variable [DecidableEq ι₁] [AddMonoid ι₁] [AddMonoid ι₂]
variable (f : ι₁ →+ ι₂)
variable {R : Type*} [CommSemiring R]
variable {A : Type*} [Semiring A] [Algebra R A]
variable {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A] [CompleteLattice σ]
  [AddSubmonoidClass.IsConcreteSSup σ A]
variable (𝒜 : ι₁ → σ) [GradedRing 𝒜]

open Pointwise in
lemma one_le_induced_grad_zero : 1 ≤ AddSubmonoid.ofClass (Decomposition.map f 𝒜 0) := by
  unfold Decomposition.map
  rw [AddSubmonoid.one_le, AddSubmonoidClass.iSup_toAddSubmonoid]
  have h : 1 ∈ AddSubmonoid.ofClass (𝒜 0) := SetLike.GradedOne.one_mem
  exact AddSubmonoid.mem_iSup_of_mem ⟨0, map_zero f⟩ h

open Pointwise in
lemma induced_grad_mul_le (i j : ι₂) :
  (AddSubmonoid.ofClass ((Decomposition.map f 𝒜) i))
  * (AddSubmonoid.ofClass ((Decomposition.map f 𝒜) j))
  ≤ AddSubmonoid.ofClass ((Decomposition.map f 𝒜) (i + j))
  := by
  unfold Decomposition.map
  repeat rw [AddSubmonoidClass.iSup_toAddSubmonoid]
  simp_rw [AddSubmonoid.iSup_mul,AddSubmonoid.mul_iSup]
  apply iSup_le
  intro i'
  apply iSup_le
  intro j'
  rw [AddSubmonoid.mul_le]
  intro m hm n hn
  have hsum : f (↑i' + ↑j') = i + j := by
    simp only [map_add,i'.property,j'.property]
  have h : m*n ∈ AddSubmonoid.ofClass (𝒜 (↑i' + ↑j')) := SetLike.GradedMul.mul_mem hm hn
  exact (le_iSup (fun i : { i_ : ι₁ // f i_ = i + j}
    ↦ (AddSubmonoid.ofClass (𝒜 i))) ⟨↑i' + ↑j', hsum⟩) h

@[implicit_reducible]
def DirectSum.Decomposition.map.gradedMonoid
  : SetLike.GradedMonoid (Decomposition.map f 𝒜) where
  one_mem := by
    unfold Decomposition.map
    exact AddSubmonoid.one_le.mp (one_le_induced_grad_zero f 𝒜)
  mul_mem i j a b ha hb := by
    unfold Decomposition.map at *
    exact AddSubmonoid.mul_le.mp (induced_grad_mul_le f 𝒜 _ _) a ha b hb

variable [DecidableEq ι₂]

@[implicit_reducible]
def DirectSum.Decomposition.map.gradedRing
  : GradedRing (Decomposition.map f 𝒜) where
  toGradedMonoid := DirectSum.Decomposition.map.gradedMonoid f 𝒜
  toDecomposition := DirectSum.Decomposition.map.decomposition f 𝒜

end gradedAlgebra.map
