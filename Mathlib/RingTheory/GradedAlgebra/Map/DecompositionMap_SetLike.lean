import Mathlib
open DirectSum


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


section toIsup
open DirectSum
variable {M : Type*} [AddCommMonoid M]
variable {ι : Type*} [DecidableEq ι]
variable {σ : Type*} [SetLike σ M] [AddSubmonoidClass σ M] [CompleteLattice σ] [IsConcreteLE σ M]
variable (ℳ : ι → σ)

def SetLike.inclusion {p q : σ} (h : p ≤ q) : ↥p →+ ↥q :=
    (AddSubmonoidClass.subtype p).codRestrict q
      (fun x ↦ IsConcreteLE.coe_subset_coe'.mpr h x.2)

def SetLike.toIsup : (⨁ i, ℳ i) →+ (⨆ i, ℳ i : σ) :=
    DirectSum.toAddMonoid fun i ↦ SetLike.inclusion (le_iSup ℳ i)

/- To verify that the map `toIsup` is surjective, I introduce the *assumption
   that the iSup in σ is just the usual iSup of additive submonoids.
   For now, I formulate this assumption as a sorried lemma
   that's modelled on the corresponding lemma for modules:

   theorem iSup_toAddSubmonoid {ι : Sort*} (p : ι → Submodule R M) :
     (⨆ i, p i).toAddSubmonoid = ⨆ i, (p i).toAddSubmonoid
-/
lemma SetLike.iSup_toAddSubmonoid  :
  AddSubmonoid.ofClass (⨆ i, ℳ i : σ) = ⨆ i, AddSubmonoid.ofClass (ℳ i) := by
  sorry  -- this is really just an assumption I want to make

lemma SetLike.toIsup_surjective : Function.Surjective (toIsup ℳ):= by
  intro ⟨y, hy'⟩
  change y ∈ AddSubmonoid.ofClass (⨆ i, ℳ i) at hy'
  rw [SetLike.iSup_toAddSubmonoid] at hy'
  have ⟨a, ha⟩ : ∃ a, ((toIsup ℳ) a : M) = y := by
    induction hy' using AddSubmonoid.iSup_induction' with
    | mem i x hxS => exact ⟨DirectSum.of _ i ⟨x, hxS⟩, by simp [toIsup,SetLike.inclusion]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y u v hx hy =>
      rw [←SetLike.iSup_toAddSubmonoid] at u v
      obtain ⟨a, ha⟩ := (hx u)
      obtain ⟨b, hb⟩ := (hy v)
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
  := fun j ↦ (⨆ (i : { i : ι₁ // f i = j}), ℳ i)


variable [AddSubmonoidClass σ M]
#check DirectSum.sigmaFiberAddEquiv f (fun i ↦ ↥(ℳ i))


variable [IsConcreteLE σ M] [DirectSum.Decomposition ℳ]

abbrev Dec' := ⨁ j, (Decomposition.map f ℳ) j

/- one option: definition as composable maps of sets -/
/-
abbrev sigma := (DirectSum.sigmaFiberAddEquiv f (fun i ↦ ↥(ℳ i))).toFun
abbrev decomp := (decomposeAddEquiv ℳ).toFun -- now it's just a map of sets
abbrev decomp' : M → (⨁ j, (Decomposition.map f ℳ) j) :=
    (map (fun (j : ι₂)
    ↦ SetLike.toIsup (ℳ := (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i))))).toFun.comp
    ((sigma f ℳ).comp (decomp ℳ))

#check (DirectSum.coeAddMonoidHom (DirectSum.Decomposition.map f ℳ) (M := M)).toFun
#check decomp' f ℳ (M:=M)
#check (decomp' f ℳ) ∘ (DirectSum.coeAddMonoidHom (DirectSum.Decomposition.map f ℳ))
#check (DirectSum.coeAddMonoidHom (DirectSum.Decomposition.map f ℳ)) ∘ (decomp' f ℳ)
-/
/- probably better option: definition as additive maps -/
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
      unfold decomp'
      unfold Decomposition.map SetLike.toIsup SetLike.inclusion
      intro i
      ext m
      simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
        Function.comp_apply, coeAddMonoidHom_of, decomposeAddEquiv_apply, decompose_coe,
        sigmaFiberAddEquiv_of, map_of, toAddMonoid_of, AddMonoidHom.codRestrict_apply,
        AddSubmonoidClass.subtype_apply, AddMonoidHom.id_comp]
      ) (by
    -- 3 reduction steps:
      apply addHom_ext'
      intro j
      unfold Decomposition.map -- needed in v4.29r8, but not in v4.28.0
      rw [← AddMonoidHom.cancel_right
        (SetLike.toIsup_surjective (fun (i : { i : ι₁ // f i = j}) ↦ ((ℳ ↑i))))]
      apply addHom_ext'
    -- now simplify everything:
      unfold decomp' SetLike.toIsup SetLike.inclusion
      intro ⟨i, hi⟩
      subst hi
      ext m : 1
      simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
        Function.comp_apply, toAddMonoid_of, AddMonoidHom.codRestrict_apply,
        AddSubmonoidClass.subtype_apply, coeAddMonoidHom_of, decomposeAddEquiv_apply, decompose_coe,
        sigmaFiberAddEquiv_of, map_of, AddMonoidHom.id_comp]
      )
end Decomposition

section ModuleDecomposition
/- MAIN PART:  Construction of induced decomposition -/
universe u
variable {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
variable (f : ι₁ → ι₂)
variable {R M : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] (ℳ : ι₁ → Submodule R M)
variable [DirectSum.Decomposition ℳ]

/-
abbrev Module.Dec' := ⨁ j, (Decomposition.map f ℳ) j
abbrev Module.decomp := (decomposeLinearEquiv ℳ).toLinearMap
abbrev Module.sigma := (DirectSum.sigmaFiberLinearEquiv R f (fun i ↦ ↥(ℳ i))).toLinearMap


#check Dec'
--#check (sigma f ℳ) ∘ₗ (decomp ℳ)

variable (j : ι₂)
#check @DirectSum.coeLinearMap.codRestrict R _ M _ _ { i : ι₁ // f i = j} (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i)) _
#check DirectSum.coeLinearMap.codRestrict R (ℳ := (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i)))
#check lmap (fun (j : ι₂) ↦
             DirectSum.coeLinearMap.codRestrict R (ℳ := (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i))))

abbrev decomp' : M →ₗ[R] (Dec' f ℳ) :=
    lmap (fun (j : ι₂)
    ↦ DirectSum.coeLinearMap.codRestrict R (ℳ := (fun (i : { i : ι₁ // f i = j}) ↦ (ℳ ↑i))))
    ∘ₗ (sigma f ℳ) ∘ₗ (decomp ℳ)
-/
#check decomp' f ℳ

instance DirectSum.Module.Decomposition.map.decomposition :
  (DirectSum.Decomposition (Decomposition.map f ℳ) )
  :=
  DirectSum.Decomposition.ofAddHom
    (Decomposition.map f ℳ)
    (decomp' f ℳ)
    (by sorry)
    (by sorry)

end ModuleDecomposition
