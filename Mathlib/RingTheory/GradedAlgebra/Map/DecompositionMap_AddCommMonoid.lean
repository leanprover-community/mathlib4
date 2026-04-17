import Mathlib
open DirectSum


/-
This file contains:
- a definition of `DirectSum.Decomposition.map`
  for additive commutative monoids,
- a proof that the induced decomposition of a graded additive commutative monoid
  is indeed a graded additive commutative monoid.
It is thus an `AddCommMonoid` version of the first half of the file

    DecompositionMap_Module.lean.

It does not seem easily possible to unify the two files, see notes in

    DecompositionMap_SetLike_Failures.lean.
-/


section DirectSum.of
/- additional _of lemmas for isos already present in Mathlib -/

variable {ι : Type*} [DecidableEq ι]

@[simp] lemma DirectSum.sigmaCurry_of
    {α : ι → Type*} [∀ i : ι, DecidableEq (α i)]
    {M : (i : ι) → α i → Type*} [∀ i : ι, ∀ j : α i, AddCommMonoid (M i j)]
    (ij : (i : ι) × α i) (m : M ij.fst ij.snd) :
    (sigmaCurryEquiv) ((of (fun ij' ↦ M ij'.fst ij'.snd) ij ) m)
    = (of (fun i' ↦ ⨁ (j' : α i'), M i' j') ij.fst) ((of (fun j' ↦ M ij.fst j') ij.snd ) m)
  := by
  exact DFinsupp.sigmaCurry_single ij m

@[simp] lemma DirectSum.equivCongrLeft_of
    {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)]
    {κ : Type*} [DecidableEq κ] (h : ι ≃ κ) (k : κ) (m : M (h.symm k)) :
    (equivCongrLeft h) ((of M (h.symm k)) m) = (of (fun k ↦ M (h.symm k)) k) m
  := by
  exact DFinsupp.comapDomain'_single (⇑h.symm) h.right_inv k m
end DirectSum.of


section DirectSum.sigmaFiberAddEquiv
/-
1. Definition of `sigmaFiberAddEquiv`
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
                := by
                exact AddEquiv.refl (⨁ (k : (y : ι₂) × { x // f x = y }), β ((Equiv.sigmaFiberEquiv f).symm.symm k))
     let iso₁ := equivCongrLeft (Equiv.sigmaFiberEquiv f).symm (β := β)
     let iso₂ := sigmaCurryEquiv (δ := fun (j : ι₂) ↦ (fun (i : { i : ι₁ // f i = j}) ↦ β i))
     --let iso' : (⨁ (k : (y : ι₂) × { x // f x = y }), M ((Equiv.sigmaFiberEquiv f).symm.symm k))
     --        ≃+ (⨁ (k : (y : ι₂) × { x // f x = y }), M k.snd) := by exact?
     #check iso₂
     #check iso'
     #check iso'.trans iso₂
     #check iso₁.trans iso'
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


section coeAddMonoidHom
/- `coeLinearMap` is the map from the direct sum of some submoduls of M to M.
    We show here that it's restriction to its codomain (the span of those submodules)
    is surjective.

   **Note:**  The proofs and constructions further below actually use
   the map toIsup instead (not present in the construction of the module
   version of the induced decomposition.)
-/

theorem AddMonoidHom.mrange_coeAddMonoidHom {ι : Type*} [DecidableEq ι]
  {M : Type*} [AddCommMonoid M] (ℳ : ι → AddSubmonoid M) :
  AddMonoidHom.mrange (DirectSum.coeAddMonoidHom ℳ) = ⨆ i, ℳ i :=
  (AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom ℳ).symm
  /-
  by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using DirectSum.induction_on with
    | zero => exact zero_mem _
    | of i x =>
        simp only [DirectSum.coeAddMonoidHom_of]
        exact AddSubmonoid.mem_iSup_of_mem i x.2
    | add x y hx hy => simpa using add_mem hx hy
  · exact iSup_le fun i => by
      rintro x hx
      exact ⟨DirectSum.of _ i ⟨x, hx⟩, by simp [DirectSum.coeAddMonoidHom_of]⟩
  -/
  --(Submodule.iSup_eq_range_dfinsupp_lsum _).symm

variable {M : Type*} [AddCommMonoid M]
variable {ι : Type*}
variable (ℳ : ι → AddSubmonoid M)
variable [DecidableEq ι]

abbrev DirectSum.coeAddMonoidHom.codRestrict :
  (⨁ (i : ι), ℳ i) →+ (⨆ (i : ι), ℳ i : AddSubmonoid M)
  := (AddEquiv.addSubmonoidCongr (AddMonoidHom.mrange_coeAddMonoidHom ℳ)).toAddMonoidHom.comp
     (DirectSum.coeAddMonoidHom ℳ).mrangeRestrict
  -- This is just an `abbrev` so that `simp` and other tactics will unfold it automatically.

lemma DirectSum.coeAddMonoidHom.mrangeRestrict_surjective :
  Function.Surjective (⇑(coeAddMonoidHom.codRestrict ℳ)) := by
  simpa using AddMonoidHom.mrangeRestrict_surjective _

/- **Alternative:** (This is what is actually used below.)  -/

def toIsup : (⨁ i, ℳ i) →+ (⨆ i, ℳ i : AddSubmonoid M) :=
    DirectSum.toAddMonoid fun i => AddSubmonoid.inclusion (le_iSup ℳ i)

lemma toIsup_surjective : Function.Surjective (toIsup ℳ):= by
  intro ⟨y, hy⟩
  have ⟨a,ha⟩: ∃ a, ((toIsup ℳ) a : M) = y := by
    induction hy using AddSubmonoid.iSup_induction' with
    | mem i x hxS => exact ⟨DirectSum.of _ i ⟨x,hxS⟩, by simp [toIsup]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
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
end coeAddMonoidHom


section Decomposition
/- MAIN PART:  Construction of induced decomposition -/

universe u
variable {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
variable (f : ι₁ → ι₂)
variable {M : Type*} [AddCommMonoid M] (ℳ : ι₁ → AddSubmonoid M)
variable [DirectSum.Decomposition ℳ]


def DirectSum.Decomposition.map : ι₂ → AddSubmonoid M
  := fun j ↦ (⨆ (i : { i : ι₁ // f i = j}), ℳ i : AddSubmonoid M)

/-
There's some tension here between the way the `DirectSum.Decomposition` itself is set up and
my definition of an induced decompositions.  `DirectSum.Decomposition` makes a claim about
the direct sum of some submodules *without reference to the lattice structure on submodules*.
For the induced decomposition, however, I need to view certain partial direct sums as
submodules, and so I *am* using the lattice structure on submodules.
-/

abbrev Dec' := ⨁ j, (Decomposition.map f ℳ) j
abbrev sigma := (DirectSum.sigmaFiberAddEquiv f (fun i ↦ ↥(ℳ i))).toAddMonoidHom
abbrev decomp := (decomposeAddEquiv ℳ).toAddMonoidHom
abbrev decomp' : M →+ (⨁ j, (Decomposition.map f ℳ) j) :=
    (map (fun (j : ι₂)
    ↦ toIsup (ℳ := (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i))))).comp
    ((sigma f ℳ).comp (decomp ℳ))


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
      unfold decomp'
      unfold Decomposition.map toIsup
      intro i
      ext m
      simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
        Function.comp_apply, coeAddMonoidHom_of, decomposeAddEquiv_apply, decompose_coe,
        sigmaFiberAddEquiv_of, map_of, toAddMonoid_of, AddSubmonoid.coe_inclusion,
        AddMonoidHom.id_comp]
      ) (by
    -- 3 reduction steps:
      apply addHom_ext'
      intro j
      unfold Decomposition.map -- needed in v4.29r8, but not in v4.28.0
      rw [← AddMonoidHom.cancel_right
        (toIsup_surjective (fun (i : { i : ι₁ // f i = j}) ↦ ((ℳ ↑i))))]
      apply addHom_ext'
    -- now simplify everything:
      unfold decomp' toIsup
      intro ⟨i, hi⟩
      subst hi
      ext m : 1
      simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
        Function.comp_apply, toAddMonoid_of, coeAddMonoidHom_of, AddSubmonoid.coe_inclusion,
        decomposeAddEquiv_apply, decompose_coe, sigmaFiberAddEquiv_of, map_of, AddMonoidHom.id_comp]
    )
end Decomposition
