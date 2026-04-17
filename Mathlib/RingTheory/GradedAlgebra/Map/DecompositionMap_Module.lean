import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.GradedAlgebra.Basic

open DirectSum

/-
This file contains:
- a definition of `DirectSum.Decomposition.map`
  for graded R-modules,
- a proof that the induced decomposition of a graded R-module
  is indeed a graded R-module,
- a proof that the induced decomposition of a graded R-algebra
  is indeed a graded R-algebra.
-/


section DirectSum.of
/- additional _of lemmas for isos already present in Mathlib -/
universe u v
variable (R : Type u) [Semiring R]
         {ι : Type v} [DecidableEq ι]

@[simp] lemma DirectSum.sigmaLcurry_of
    {α : ι → Type*} [∀ i : ι, DecidableEq (α i)]
    {M : (i : ι) → α i → Type*} [∀ i : ι, ∀ j : α i, AddCommMonoid (M i j)]
    [∀ i : ι, ∀ j : α i, Module R (M i j)]
    (ij : (i : ι) × α i) (m : M ij.fst ij.snd) :
    (sigmaLcurryEquiv R) ((of (fun ij' ↦ M ij'.fst ij'.snd) ij ) m)
    = (of (fun i' ↦ ⨁ (j' : α i'), M i' j') ij.fst) ((of (fun j' ↦ M ij.fst j') ij.snd ) m)
  := by
  exact DFinsupp.sigmaCurry_single ij m

@[simp] lemma DirectSum.lequivCongrLeft_of
    {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
    {κ : Type*} [DecidableEq κ] (h : ι ≃ κ) (k : κ) (m : M (h.symm k)) :
    (lequivCongrLeft R h) ((of M (h.symm k)) m) = (of (fun k ↦ M (h.symm k)) k) m
  := by
  exact DFinsupp.comapDomain'_single (⇑h.symm) h.right_inv k m
end DirectSum.of


section DirectSum.sigmaFiberLinearEquiv
/-
1. Definition of `sigmaFiberLinearEquiv`
   as composition of two isos:
     iso₁ :=  lequivCongrLeft
     iso₂ := sigmaLcurryEquiv
   Each of (iso₁) and (iso₂) are defined in Mathlib,
   and we prove an …_of lemma for each of these.
2. `sigmaFiberLinearEquiv_of` lemma, proved from the …_of lemmas for iso₁ and iso₂.
   This is all still very messy and probably not done the correct way.
-/
universe u v
variable (R : Type u) [Semiring R]
         {ι₁ ι₂ : Type v} [DecidableEq ι₁] [DecidableEq ι₂]
         (f : ι₁ → ι₂)

def DirectSum.sigmaFiberLinearEquiv
    (M : ι₁ → Type*) [∀ i : ι₁, AddCommMonoid (M i)] [∀ i : ι₁, Module R (M i)] :
    (DirectSum ι₁ fun i ↦ M i)
    ≃ₗ[R] DirectSum ι₂ fun j ↦ (DirectSum { i : ι₁ // f i = j} fun i ↦ M i)
  := lequivCongrLeft R (Equiv.sigmaFiberEquiv f).symm (M := M)
     ≪≫ₗ sigmaLcurryEquiv R (δ := fun (j : ι₂) ↦ (fun (i : { i : ι₁ // f i = j}) ↦ M i))
     /-
     by
     let iso' : (⨁ (k : (j : ι₂) × { i // f i = j }), M ((Equiv.sigmaFiberEquiv f).symm.symm k))
          ≃ₗ[R] (⨁ (k : (j : ι₂) × { i // f i = j }), M ↑k.snd)
                := by exact LinearEquiv.refl R (⨁ (k : (j : ι₂) × { i // f i = j }), M ↑k.snd)
     let iso₁ := lequivCongrLeft R (Equiv.sigmaFiberEquiv f).symm (M := M)
     let iso₂ := sigmaLcurryEquiv R (δ := fun (j : ι₂) ↦ (fun (i : { i : ι₁ // f i = j}) ↦ M i))
     #check iso₂
     #check iso'
     #check iso' ≪≫ₗ iso₂
     #check iso₁
     exact iso₁ ≪≫ₗ iso' ≪≫ₗ iso₂
     -/

lemma DirectSum.sigmaFiberLinearEquiv_of'
  (M : ι₁ → Type*) [∀ i : ι₁, AddCommMonoid (M i)] [∀ i : ι₁, Module R (M i)]
  (k : (i₂ : ι₂) × {i₁ : ι₁ // f i₁ = i₂}) (m : M ↑k.snd) :
  (sigmaFiberLinearEquiv R f M) ((of (fun i ↦ M i) (k.snd)) m)
  = (of _ (k.fst)) ((of (fun (i': { i : ι₁ // f i = k.fst})  ↦ M ↑i') k.snd) m)
  := by
  let h := Equiv.sigmaFiberEquiv f
  have : h.symm.symm k = ↑k.snd := by rfl
  calc (sigmaFiberLinearEquiv R f M) ((of M (k.snd)) m)
     _ = (sigmaLcurryEquiv R) ((lequivCongrLeft R h.symm) ((of M (k.snd)) m))
         := by unfold sigmaFiberLinearEquiv h; rw [LinearEquiv.trans_apply]; rfl
     _ = (sigmaLcurryEquiv R) ((lequivCongrLeft R h.symm) ((of M (h.symm.symm k)) (this ▸ m)))
        := rfl
     _ = (sigmaLcurryEquiv R) ((of (fun (k : ((y : ι₂) × { x // f x = y })) ↦ M (k.snd)) k) m) := by
         rw [lequivCongrLeft_of] ; rfl
     _ = (of _ (k.fst)) ((of (fun (i': { i : ι₁ // f i = k.fst})  ↦ M ↑i') k.snd) m) := by
         rw [sigmaLcurry_of]

@[simp] lemma DirectSum.sigmaFiberLinearEquiv_of
  (M : ι₁ → Type*) [∀ i : ι₁, AddCommMonoid (M i)] [∀ i : ι₁, Module R (M i)]
  (i : ι₁) (m : M i) :
  (sigmaFiberLinearEquiv R f M) ((of _ i) m)
  = (of _ (f i)) ((of _ ⟨i, rfl⟩) m)
  := by
  rw [sigmaFiberLinearEquiv_of' R f M (k := ⟨f i, ⟨i, rfl⟩⟩)]
end DirectSum.sigmaFiberLinearEquiv


section coeLinearMap
/- `coeLinearMap` is the map from the direct sum of some submoduls of M to M.
    We show here that it's restriction to its codomain (the span of those submodules)
    is surjective. -/
variable (R : Type*) [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {ι : Type*}
variable (ℳ : ι → Submodule R M)
variable [DecidableEq ι]

abbrev DirectSum.coeLinearMap.codRestrict :
  (⨁ (i : ι), ℳ i) →ₗ[R] (⨆ (i : ι), ℳ i : Submodule R M)
  := (LinearEquiv.ofEq _ _ range_coeLinearMap).toLinearMap ∘ₗ (coeLinearMap ℳ).rangeRestrict
  -- This is just an `abbrev` so that `simp` and other tactics will unfold it automatically.

lemma DirectSum.coeLinearMap.codRestrict_surjective :
  Function.Surjective (⇑(coeLinearMap.codRestrict R ℳ)) := by
  simp only [codRestrict, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective]
  exact LinearMap.surjective_rangeRestrict _
end coeLinearMap


section Decomposition
/- MAIN PART:  Construction of induced decomposition -/
universe u
variable {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
variable (f : ι₁ → ι₂)
variable {R M : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] (ℳ : ι₁ → Submodule R M)
variable [DirectSum.Decomposition ℳ]


def DirectSum.Decomposition.map : ι₂ → Submodule R M
  := fun j ↦ (⨆ (i : { i : ι₁ // f i = j}), ℳ i : Submodule R M)

/-
There's some tension here between the way the `DirectSum.Decomposition` itself is set up and
my definition of an induced decompositions.  `DirectSum.Decomposition` makes a claim about
the direct sum of some submodules *without reference to the lattice structure on submodules*.
For the induced decomposition, however, I need to view certain partial direct sums as
submodules, and so I *am* using the lattice structure on submodules.
-/

abbrev Dec' := ⨁ j, (Decomposition.map f ℳ) j
abbrev sigma := (DirectSum.sigmaFiberLinearEquiv R f (fun i ↦ ↥(ℳ i))).toLinearMap
abbrev decomp := (decomposeLinearEquiv ℳ).toLinearMap

#check Dec'
#check (sigma f ℳ) ∘ₗ (decomp ℳ)

variable (j : ι₂)
#check @DirectSum.coeLinearMap.codRestrict R _ M _ _ { i : ι₁ // f i = j} (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i)) _
#check DirectSum.coeLinearMap.codRestrict R (ℳ := (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i)))
#check lmap (fun (j : ι₂) ↦
             DirectSum.coeLinearMap.codRestrict R (ℳ := (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i))))

abbrev decomp' : M →ₗ[R] (Dec' f ℳ) :=
    lmap (fun (j : ι₂)
    ↦ DirectSum.coeLinearMap.codRestrict R (ℳ := (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i))))
    ∘ₗ (sigma f ℳ) ∘ₗ (decomp ℳ)

instance DirectSum.Decomposition.map.decomposition :
  (DirectSum.Decomposition (Decomposition.map f ℳ) )
  :=
  DirectSum.Decomposition.ofLinearMap
    (Decomposition.map f ℳ)
    (decomp' f ℳ)
    (by
    -- 2 reduction steps:
      rw [← (decomposeLinearEquiv ℳ).symm.eq_comp_toLinearMap_iff _ _]
      apply linearMap_ext
    -- now simplify everything:
      unfold decomp'
      unfold Dec' Decomposition.map
      intro i
      ext m
      simp only [LinearMap.coe_comp, lmap_comp, LinearEquiv.comp_coe, LinearEquiv.coe_coe,
        Function.comp_apply, lof_eq_of, decomposeLinearEquiv_symm_apply, decompose_symm_of,
        LinearEquiv.trans_apply, decomposeLinearEquiv_apply, decompose_coe,
        sigmaFiberLinearEquiv_of, lmap_of, coeLinearMap_of, LinearEquiv.coe_ofEq_apply,
        LinearMap.codRestrict_apply, LinearMap.id_comp, decomposeLinearEquiv_symm_comp_lof,
        Submodule.subtype_apply]
        -- last step is found by `simp?`
    ) (by
    -- 3 reduction steps:
      apply linearMap_ext
      intro j
      unfold Decomposition.map -- needed in v4.29r8, but not in v4.28.0
      rw [← LinearMap.cancel_right
        (coeLinearMap.codRestrict_surjective R (fun (i : { i : ι₁ // f i = j}) ↦ ((ℳ ↑i))))]
      apply linearMap_ext
    -- now simplify everything:
      unfold decomp' Dec' Decomposition.map
      intro ⟨i, hi⟩
      subst hi
      ext m : 1
      simp only [LinearMap.coe_comp, lmap_comp, LinearEquiv.comp_coe, LinearEquiv.coe_coe,
        Function.comp_apply, lof_eq_of, coeLinearMap_of, LinearEquiv.coe_ofEq_apply,
        LinearMap.codRestrict_apply, LinearEquiv.trans_apply, decomposeLinearEquiv_apply,
        decompose_coe, sigmaFiberLinearEquiv_of, lmap_of, LinearMap.id_comp]
        -- last step is found by `simp?`
    )
end Decomposition

section gradedAlgebra.map
universe u
variable {ι₁ ι₂ : Type u}
variable [DecidableEq ι₁] [AddMonoid ι₁] [AddMonoid ι₂]
variable (f : ι₁ →+ ι₂)
variable {R A : Type*}
variable [CommRing R] [Semiring A] [Algebra R A]
variable (𝒜 : ι₁ → Submodule R A) [GradedAlgebra 𝒜]

lemma one_le_induced_grad_zero : 1 ≤ Decomposition.map f 𝒜 0 := by
  rw [Submodule.one_le]
  exact Submodule.mem_iSup_of_mem ⟨0, AddMonoidHom.map_zero f⟩ (SetLike.GradedOne.one_mem)

lemma induced_grad_mul_le (i j : ι₂) :
  (Decomposition.map f 𝒜) i * (Decomposition.map f 𝒜) j
  ≤ (Decomposition.map f 𝒜) (i + j)
  := by
  unfold Decomposition.map
  simp_rw [Submodule.iSup_mul,Submodule.mul_iSup]
  apply iSup_le
  intro i'
  apply iSup_le
  intro j'
  rw [Submodule.mul_le]
  intro m hm n hn
  have hsum : f (↑i' + ↑j') = i + j := by
    simp only [map_add,i'.property,j'.property]
  exact Submodule.mem_iSup_of_mem ⟨↑i' + ↑j', hsum⟩ (SetLike.GradedMul.mul_mem hm hn)

instance DirectSum.Decomposition.map.gradedMonoid
  : SetLike.GradedMonoid (Decomposition.map f 𝒜) where
  one_mem := Submodule.one_le.mp (one_le_induced_grad_zero f 𝒜)
  mul_mem _i _j _p _q hp hq := Submodule.mul_le.mp (induced_grad_mul_le f 𝒜 _ _) _ hp _ hq

variable [DecidableEq ι₂]

instance DirectSum.Decomposition.map.gradedAlgebra
  : GradedAlgebra (Decomposition.map f 𝒜) where
  toGradedMonoid := inferInstance --ind_gm 𝒜 f
  toDecomposition := inferInstance -- ind_decomp R 𝒜 f

end gradedAlgebra.map
