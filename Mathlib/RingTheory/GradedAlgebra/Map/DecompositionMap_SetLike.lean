import Mathlib
import Mathlib.RingTheory.GradedAlgebra.Map.auxiliary
open DirectSum

section DirectSum.sigmaFiberAddEquiv
/-
1. Definition of `sigmaFiberAddEquiv`< :
   as composition of two isos:
     iso₁ :=  lequivCongrLeft
     iso₂ := sigmaLcurryEquiv
   Each of (iso₁) and (iso₂) are defined in Mathlib,
   and we prove an …_of lemma for each of these.
2. `sigmaFiberLinearAdd_of` lemma, proved from the …_of lemmas for iso₁ and iso₂.
   This is all still very messy and probably not done the correct way.
-/
universe u
variable {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
         (f : ι₁ → ι₂)

def DirectSum.sigmaFiberAddEquiv
    (β : ι₁ → Type*) [∀ i : ι₁, AddCommMonoid (β i)] :
    (DirectSum ι₁ fun i ↦ β i)
    ≃+ DirectSum ι₂ fun j ↦ (DirectSum { i : ι₁ // f i = j} fun i ↦ β i)
  := (equivCongrLeft (Equiv.sigmaFiberEquiv f).symm).trans
     (sigmaCurryEquiv (δ := fun (j : ι₂) ↦ (fun (i : { i : ι₁ // f i = j}) ↦ β i)))
     /-
     by
     let iso' : (⨁ (k : (y : ι₂) × { x // f x = y }), β ((Equiv.sigmaFiberEquiv f).symm.symm k))
                ≃+ (⨁ (i : (x : ι₂) × { i // f i = x }), β ↑i.snd)
                := by exact AddEquiv.refl (⨁ (k : (y : ι₂) × { x // f x = y }), β
                    ((Equiv.sigmaFiberEquiv f).symm.symm k))
     let iso₁ := equivCongrLeft (Equiv.sigmaFiberEquiv f).symm (β := β)
     let iso₂ := sigmaCurryEquiv (δ := fun (j : ι₂) ↦ (fun (i : { i : ι₁ // f i = j}) ↦ β i))
     --let iso' : (⨁ (k : (y : ι₂) × { x // f x = y }), M ((Equiv.sigmaFiberEquiv f).symm.symm k))
     --        ≃+ (⨁ (k : (y : ι₂) × { x // f x = y }), M k.snd) := by exact?
     --exact iso₁.trans (iso'.trans iso₂)
     exact iso₁.trans iso₂
     -/

lemma DirectSum.sigmaFiberAddEquiv_of'
  (β : ι₁ → Type*) [∀ i : ι₁, AddCommMonoid (β i)]
  (k : (i₂ : ι₂) × {i₁ : ι₁ // f i₁ = i₂}) (m : β ↑k.snd) :
  (sigmaFiberAddEquiv f β) ((of (fun i ↦ β i) (k.snd)) m)
  = (of _ (k.fst)) ((of (fun (i': { i : ι₁ // f i = k.fst})  ↦ β ↑i') k.snd) m)
  := by
  let h := Equiv.sigmaFiberEquiv f
  have : h.symm.symm k = ↑k.snd := by rfl
  calc (sigmaFiberAddEquiv f β) ((of β (k.snd)) m)
     _ = (sigmaCurryEquiv) ((equivCongrLeft h.symm) ((of β (k.snd)) m))
         := by unfold sigmaFiberAddEquiv h; rw [AddEquiv.trans_apply]; rfl
     _ = (sigmaCurryEquiv) ((equivCongrLeft h.symm) ((of β (h.symm.symm k)) (this ▸ m)))
        := rfl
     _ = (sigmaCurryEquiv) ((of (fun (k : ((y : ι₂) × { x // f x = y })) ↦ β (k.snd)) k) m) := by
         rw [equivCongrLeft_of] ; rfl
     _ = (of _ (k.fst)) ((of (fun (i': { i : ι₁ // f i = k.fst})  ↦ β ↑i') k.snd) m) := by
         rw [sigmaCurry_of]

@[simp] lemma DirectSum.sigmaFiberAddEquiv_of
  (β : ι₁ → Type*) [∀ i : ι₁, AddCommMonoid (β i)]
  (i : ι₁) (m : β i) :
  (sigmaFiberAddEquiv f β) ((of _ i) m)
  = (of _ (f i)) ((of _ ⟨i, rfl⟩) m)
  := by
  rw [sigmaFiberAddEquiv_of' f β (k := ⟨f i, ⟨i, rfl⟩⟩)]
end DirectSum.sigmaFiberAddEquiv

section TypeClassAssumption

class IsAddSubmonoidSSup (σ : Type*) [CompleteLattice σ]
    (M : outParam Type*) [AddCommMonoid M]
    [SetLike σ M] [AddSubmonoidClass σ M]
    where
    sSup_toAddSubmonoid (S : Set σ) :
    AddSubmonoid.ofClass (sSup S) = sSup (AddSubmonoid.ofClass '' S)

lemma SetLike.iSup_toAddSubmonoid {σ : Type*} [CompleteLattice σ]
    {M : Type*} [AddCommMonoid M] [SetLike σ M] [AddSubmonoidClass σ M]
    [IsAddSubmonoidSSup σ M] {ι : Sort*} (ℳ : ι → σ) :
    AddSubmonoid.ofClass (⨆ i, ℳ i) = ⨆ i, AddSubmonoid.ofClass (ℳ i) := by
  rw [iSup,IsAddSubmonoidSSup.sSup_toAddSubmonoid,← Set.range_comp]
  rfl

instance (M : Type*) [AddCommMonoid M] :
  IsAddSubmonoidSSup (AddSubmonoid M) M where
  sSup_toAddSubmonoid S := by
    -- This is essentially `rfl`, but still 3 lines:
    have h₁ (N : AddSubmonoid M) : AddSubmonoid.ofClass N = N := rfl
    have h₂ (S : Set (AddSubmonoid M)) : AddSubmonoid.ofClass '' S = S :=
      Set.EqOn.image_eq_self fun ⦃x⦄ ↦ congrFun rfl
    rw [h₁,h₂]

instance (M : Type*) [AddCommGroup M] :
  IsAddSubmonoidSSup (AddSubgroup M) M where
  sSup_toAddSubmonoid S := by
    have (N : AddSubgroup M) : AddSubmonoid.ofClass N = N.toAddSubmonoid := by rfl
    simp [this, Subgroup.toAddSubmonoid_sSup]

instance (R : Type*) [Semiring R] (M : Type*) [AddCommMonoid M] [Module R M] :
  IsAddSubmonoidSSup (Submodule R M) M where
  sSup_toAddSubmonoid S := by
    have (N : Submodule R M) : AddSubmonoid.ofClass N = N.toAddSubmonoid := by rfl
    simp only [this, Submodule.toAddSubmonoid_sSup]

end TypeClassAssumption


section toIsup
open DirectSum
variable {M : Type*} [AddCommMonoid M]
variable {ι : Type*} [DecidableEq ι]
variable {σ : Type*} [SetLike σ M] [AddSubmonoidClass σ M] [CompleteLattice σ]
  [h : IsAddSubmonoidSSup σ M]
variable (ℳ : ι → σ)

--@[irreducible]
--def GoodClosure : σ := (⨆ i, ℳ i : σ)

/- To verify that the map `toIsup` is surjective, I introduce the *assumption
   that the iSup in σ is just the usual iSup of additive submonoids.
   For now, I formulate this assumption as a sorried lemma
   that's modelled on the corresponding lemma for modules:

   theorem iSup_toAddSubmonoid {ι : Sort*} (p : ι → Submodule R M) :
     (⨆ i, p i).toAddSubmonoid = ⨆ i, (p i).toAddSubmonoid
-/

omit [DecidableEq ι] in
@[simp] lemma SetLike.mem_iSup_iff_mem_iSup_AddSubmonoid
  (m : M) :
  m ∈ (⨆ i, ℳ i : σ) ↔ m ∈ (⨆ i, AddSubmonoid.ofClass (ℳ i))
  := by
  rw [← SetLike.iSup_toAddSubmonoid ℳ]
  rfl

private def codomain_equal :
   ↥(⨆ i, AddSubmonoid.ofClass (ℳ i)) ≃+ ↥(⨆ i, ℳ i : σ)  :=
   (AddEquiv.addSubmonoidCongr (SetLike.iSup_toAddSubmonoid ℳ).symm)

private def toIsup_ : (⨁ i, ℳ i) →+ ↥(⨆ i, AddSubmonoid.ofClass (ℳ i)) :=
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
  obtain ⟨val, property⟩ := m
  simp_all only
  rfl

lemma SetLike.toIsup_surjective : Function.Surjective (toIsup ℳ) := by
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
      rw [←SetLike.iSup_toAddSubmonoid] at u v
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by simp [ha, hb]⟩
  subst ha
  simp_all only [Subtype.coe_eta, exists_apply_eq_apply]
/-
  TODO:
    Figure out a better proof of toIsup_surjective.
    toIsup seems to work better than DirectSum.coeAddMonoidHom.codRestrict:
       in the construction of the decomposition instance below, the first proof now works with simp
-/
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

variable [AddSubmonoidClass σ M] [h : IsAddSubmonoidSSup σ M]

#check DirectSum.sigmaFiberAddEquiv f (fun i ↦ ↥(ℳ i))
--#check h

variable [DirectSum.Decomposition ℳ]

abbrev Dec' := ⨁ j, (Decomposition.map f ℳ) j
abbrev sigma := (DirectSum.sigmaFiberAddEquiv f (fun i ↦ ↥(ℳ i))).toAddMonoidHom
abbrev decomp := (decomposeAddEquiv ℳ).toAddMonoidHom
abbrev decomp' : M →+ (⨁ j, (Decomposition.map f ℳ) j) :=
    (map (fun (j : ι₂)
    ↦ SetLike.toIsup (ℳ := (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i))))).comp
    ((sigma f ℳ).comp (decomp ℳ))

#check (DirectSum.coeAddMonoidHom (DirectSum.Decomposition.map f ℳ) (M := M)).toFun
#check decomp' f ℳ (M:=M)
#check (decomp' f ℳ) ∘ (DirectSum.coeAddMonoidHom (DirectSum.Decomposition.map f ℳ))
#check (DirectSum.coeAddMonoidHom (DirectSum.Decomposition.map f ℳ)) ∘ (decomp' f ℳ)


instance DirectSum.Decomposition.map.decomposition :
  (DirectSum.Decomposition (Decomposition.map f ℳ) )
  :=
  DirectSum.Decomposition.ofAddHom
    (Decomposition.map f ℳ)
    (decomp' f ℳ)
    (by
    -- 2 reduction steps:
      rw [← AddMonoidHom.cancel_right (decomposeAddEquiv ℳ).symm.surjective]
      apply addHom_ext'
    -- now simplify everything:
      unfold decomp' Decomposition.map
      intro i
      ext m
      simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
        Function.comp_apply, coeAddMonoidHom_of, decomposeAddEquiv_apply, decompose_coe,
        sigmaFiberAddEquiv_of, map_of, SetLike.toIsup_of, AddMonoidHom.id_comp]
      ) (by
    -- 3 reduction steps:
      apply addHom_ext'
      intro j
      unfold Decomposition.map -- needed in v4.29r8, but not in v4.28.0
      rw [← AddMonoidHom.cancel_right
        (SetLike.toIsup_surjective (fun (i : { i : ι₁ // f i = j}) ↦ ((ℳ ↑i)))) ]
      apply addHom_ext'
    -- now simplify everything:
      unfold decomp' --SetLike.toIsup SetLike.inclusion
      intro ⟨i, hi⟩
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
  [IsAddSubmonoidSSup σ A]
variable (𝒜 : ι₁ → σ) [GradedRing 𝒜]

open Pointwise in
lemma one_le_induced_grad_zero : 1 ≤ AddSubmonoid.ofClass (Decomposition.map f 𝒜 0) := by
  unfold Decomposition.map
  rw [AddSubmonoid.one_le, SetLike.iSup_toAddSubmonoid]
  have h : 1 ∈ AddSubmonoid.ofClass (𝒜 0) := SetLike.GradedOne.one_mem
  exact AddSubmonoid.mem_iSup_of_mem ⟨0, map_zero f⟩ h

open Pointwise in
lemma induced_grad_mul_le (i j : ι₂) :
  (AddSubmonoid.ofClass ((Decomposition.map f 𝒜) i))
  * (AddSubmonoid.ofClass ((Decomposition.map f 𝒜) j))
  ≤ AddSubmonoid.ofClass ((Decomposition.map f 𝒜) (i + j))
  := by
  unfold Decomposition.map
  repeat rw [SetLike.iSup_toAddSubmonoid]
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

instance DirectSum.Decomposition.map.gradedMonoid
  : SetLike.GradedMonoid (Decomposition.map f 𝒜) where
  one_mem := by
    unfold Decomposition.map
    exact AddSubmonoid.one_le.mp (one_le_induced_grad_zero f 𝒜)
  mul_mem i j a b ha hb := by
    unfold Decomposition.map at *
    exact AddSubmonoid.mul_le.mp (induced_grad_mul_le f 𝒜 _ _) a ha b hb

variable [DecidableEq ι₂]

instance DirectSum.Decomposition.map.gradedRing
  : GradedRing (Decomposition.map f 𝒜) where
  toGradedMonoid := DirectSum.Decomposition.map.gradedMonoid f 𝒜
  toDecomposition := DirectSum.Decomposition.map.decomposition f 𝒜

end gradedAlgebra.map
