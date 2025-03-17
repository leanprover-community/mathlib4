/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Sublattice

/-!
# Boolean subalgebras

This file defines boolean subalgebras.
-/

open Function Set

variable {ι : Sort*} {α β γ : Type*}

variable (α) in
/-- A boolean subalgebra of a boolean algebra is a set containing the bottom and top elements, and
closed under suprema, infima and complements. -/
structure BooleanSubalgebra [BooleanAlgebra α] extends Sublattice α where
  compl_mem' {a} : a ∈ carrier → aᶜ ∈ carrier
  bot_mem' : ⊥ ∈ carrier

namespace BooleanSubalgebra
section BooleanAlgebra
variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ] {L M : BooleanSubalgebra α}
  {f : BoundedLatticeHom α β} {s t : Set α} {a b : α}

initialize_simps_projections BooleanSubalgebra (carrier → coe, as_prefix coe)

instance instSetLike : SetLike (BooleanSubalgebra α) α where
  coe L := L.carrier
  coe_injective' L M h := by obtain ⟨⟨_, _⟩, _⟩ := L; congr

lemma coe_inj : (L : Set α) = M ↔ L = M := SetLike.coe_set_eq

@[simp] lemma supClosed (L : BooleanSubalgebra α) : SupClosed (L : Set α) := L.supClosed'
@[simp] lemma infClosed (L : BooleanSubalgebra α) : InfClosed (L : Set α) := L.infClosed'

lemma compl_mem (ha : a ∈ L) : aᶜ ∈ L := L.compl_mem' ha
@[simp] lemma compl_mem_iff : aᶜ ∈ L ↔ a ∈ L := ⟨fun ha ↦ by simpa using compl_mem ha, compl_mem⟩
@[simp] lemma bot_mem : ⊥ ∈ L := L.bot_mem'
@[simp] lemma top_mem : ⊤ ∈ L := by simpa using compl_mem L.bot_mem
lemma sup_mem (ha : a ∈ L) (hb : b ∈ L) : a ⊔ b ∈ L := L.supClosed ha hb
lemma inf_mem (ha : a ∈ L) (hb : b ∈ L) : a ⊓ b ∈ L := L.infClosed ha hb
lemma sdiff_mem (ha : a ∈ L) (hb : b ∈ L) : a \ b ∈ L := by
  simpa [sdiff_eq] using L.infClosed ha (compl_mem hb)
lemma himp_mem (ha : a ∈ L) (hb : b ∈ L) : a ⇨ b ∈ L := by
  simpa [himp_eq] using L.supClosed hb (compl_mem ha)

lemma mem_carrier : a ∈ L.carrier ↔ a ∈ L := .rfl
@[simp] lemma mem_toSublattice : a ∈ L.toSublattice ↔ a ∈ L := .rfl
@[simp] lemma mem_mk {L : Sublattice α} (h_compl h_bot) : a ∈ mk L h_compl h_bot ↔ a ∈ L := .rfl
@[simp] lemma coe_mk (L : Sublattice α) (h_compl h_bot) : (mk L h_compl h_bot : Set α) = L := rfl
@[simp] lemma mk_le_mk {L M : Sublattice α} (hL_compl hL_bot hM_compl hM_bot) :
    mk L hL_compl hL_bot ≤ mk M hM_compl hM_bot ↔ L ≤ M := .rfl
@[simp] lemma mk_lt_mk{L M : Sublattice α} (hL_compl hL_bot hM_compl hM_bot) :
    mk L hL_compl hL_bot < mk M hM_compl hM_bot ↔ L < M := .rfl

/-- Copy of a boolean subalgebra with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (L : BooleanSubalgebra α) (s : Set α) (hs : s = L) : BooleanSubalgebra α where
  toSublattice := L.toSublattice.copy s <| by subst hs; rfl
  compl_mem' := by subst hs; exact L.compl_mem'
  bot_mem' := by subst hs; exact L.bot_mem'

@[simp, norm_cast]
lemma coe_copy (L : BooleanSubalgebra α) (s : Set α) (hs) : L.copy s hs = s := rfl

lemma copy_eq (L : BooleanSubalgebra α) (s : Set α) (hs) : L.copy s hs = L :=
  SetLike.coe_injective hs

/-- Two boolean subalgebras are equal if they have the same elements. -/
lemma ext : (∀ a, a ∈ L ↔ a ∈ M) → L = M := SetLike.ext

/-- A boolean subalgebra of a lattice inherits a bottom element. -/
instance instBotCoe : Bot L where bot := ⟨⊥, bot_mem⟩

/-- A boolean subalgebra of a lattice inherits a top element. -/
instance instTopCoe : Top L where top := ⟨⊤, top_mem⟩

/-- A boolean subalgebra of a lattice inherits a supremum. -/
instance instSupCoe : Max L where max a b := ⟨a ⊔ b, L.supClosed a.2 b.2⟩

/-- A boolean subalgebra of a lattice inherits an infimum. -/
instance instInfCoe : Min L where min a b := ⟨a ⊓ b, L.infClosed a.2 b.2⟩

/-- A boolean subalgebra of a lattice inherits a complement. -/
instance instHasComplCoe : HasCompl L where compl a := ⟨aᶜ, compl_mem a.2⟩

/-- A boolean subalgebra of a lattice inherits a difference. -/
instance instSDiffCoe : SDiff L where sdiff a b := ⟨a \ b, sdiff_mem a.2 b.2⟩

/-- A boolean subalgebra of a lattice inherits a Heyting implication. -/
instance instHImpCoe : HImp L where himp a b := ⟨a ⇨ b, himp_mem a.2 b.2⟩

@[simp, norm_cast] lemma val_bot : (⊥ : L) = (⊥ : α) := rfl
@[simp, norm_cast] lemma val_top : (⊤ : L) = (⊤ : α) := rfl
@[simp, norm_cast] lemma val_sup (a b : L) : a ⊔ b = (a : α) ⊔ b := rfl
@[simp, norm_cast] lemma val_inf (a b : L) : a ⊓ b = (a : α) ⊓ b := rfl
@[simp, norm_cast] lemma val_compl (a : L) : aᶜ = (a : α)ᶜ := rfl
@[simp, norm_cast] lemma val_sdiff (a b : L) : a \ b = (a : α) \ b := rfl
@[simp, norm_cast] lemma val_himp (a b : L) : a ⇨ b = (a : α) ⇨ b := rfl

@[simp] lemma mk_bot : (⟨⊥, bot_mem⟩ : L) = ⊥ := rfl
@[simp] lemma mk_top : (⟨⊤, top_mem⟩ : L) = ⊤ := rfl
@[simp] lemma mk_sup_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩ :=
  rfl
@[simp] lemma mk_inf_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩ :=
  rfl
@[simp] lemma compl_mk (a : α) (ha) : (⟨a, ha⟩ : L)ᶜ = ⟨aᶜ, compl_mem ha⟩ := rfl
@[simp] lemma mk_sdiff_mk (a b : α) (ha hb) : (⟨a, ha⟩ \ ⟨b, hb⟩ : L) = ⟨a \ b, sdiff_mem ha hb⟩ :=
  rfl
@[simp] lemma mk_himp_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⇨ ⟨b, hb⟩ : L) = ⟨a ⇨ b, himp_mem ha hb⟩ :=
  rfl

/-- A boolean subalgebra of a lattice inherits a boolean algebra structure. -/
instance instBooleanAlgebraCoe (L : BooleanSubalgebra α) : BooleanAlgebra L :=
  Subtype.coe_injective.booleanAlgebra _ val_sup val_inf val_top val_bot val_compl val_sdiff
    val_himp

/-- The natural lattice hom from a boolean subalgebra to the original lattice. -/
def subtype (L : BooleanSubalgebra α) : BoundedLatticeHom L α where
  toFun := ((↑) : L → α)
  map_bot' := L.val_bot
  map_top' := L.val_top
  map_sup' := val_sup
  map_inf' := val_inf

@[simp, norm_cast] lemma coe_subtype (L : BooleanSubalgebra α) : L.subtype = ((↑) : L → α) := rfl
lemma subtype_apply (L : BooleanSubalgebra α) (a : L) : L.subtype a = a := rfl

lemma subtype_injective (L : BooleanSubalgebra α) : Injective <| subtype L := Subtype.coe_injective

/-- The inclusion homomorphism from a boolean subalgebra `L` to a bigger boolean subalgebra `M`. -/
def inclusion (h : L ≤ M) : BoundedLatticeHom L M where
  toFun := Set.inclusion h
  map_bot' := rfl
  map_top' := rfl
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

@[simp] lemma coe_inclusion (h : L ≤ M) : inclusion h = Set.inclusion h := rfl
lemma inclusion_apply (h : L ≤ M) (a : L) : inclusion h a = Set.inclusion h a := rfl

lemma inclusion_injective (h : L ≤ M) : Injective <| inclusion h := Set.inclusion_injective h

@[simp] lemma inclusion_rfl (L : BooleanSubalgebra α) : inclusion le_rfl = .id L := rfl
@[simp] lemma subtype_comp_inclusion (h : L ≤ M) : M.subtype.comp (inclusion h) = L.subtype := rfl

/-- The maximum boolean subalgebra of a lattice. -/
instance instTop : Top (BooleanSubalgebra α) where
  top.carrier := univ
  top.bot_mem' := mem_univ _
  top.compl_mem' _ := mem_univ _
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ

/-- The trivial boolean subalgebra of a lattice. -/
instance instBot : Bot (BooleanSubalgebra α) where
  bot.carrier := {⊥, ⊤}
  bot.bot_mem' := by simp
  bot.compl_mem' := by simp
  bot.supClosed' _ := by simp
  bot.infClosed' _ := by simp

/-- The inf of two boolean subalgebras is their intersection. -/
instance instInf : Min (BooleanSubalgebra α) where
  min L M :=  { carrier := L ∩ M
                bot_mem' := ⟨bot_mem, bot_mem⟩
                compl_mem' := fun ha ↦ ⟨compl_mem ha.1, compl_mem ha.2⟩
                supClosed' := L.supClosed.inter M.supClosed
                infClosed' := L.infClosed.inter M.infClosed }

/-- The inf of boolean subalgebras is their intersection. -/
instance instInfSet : InfSet (BooleanSubalgebra α) where
  sInf S := { carrier := ⋂ L ∈ S, L
              bot_mem' := mem_iInter₂.2 fun _ _ ↦ bot_mem
              compl_mem' := fun ha ↦ mem_iInter₂.2 fun L hL ↦ compl_mem <| mem_iInter₂.1 ha L hL
              supClosed' := supClosed_sInter <| forall_mem_range.2 fun L ↦ supClosed_sInter <|
                forall_mem_range.2 fun _ ↦ L.supClosed
              infClosed' := infClosed_sInter <| forall_mem_range.2 fun L ↦ infClosed_sInter <|
                forall_mem_range.2 fun _ ↦ L.infClosed }

instance instInhabited : Inhabited (BooleanSubalgebra α) := ⟨⊥⟩

/-- The top boolean subalgebra is isomorphic to the original boolean algebra.

This is the boolean subalgebra version of `Equiv.Set.univ α`. -/
def topEquiv : (⊤ : BooleanSubalgebra α) ≃o α where
  toEquiv := Equiv.Set.univ _
  map_rel_iff' := .rfl

@[simp, norm_cast] lemma coe_top : (⊤ : BooleanSubalgebra α) = (univ : Set α) := rfl
@[simp, norm_cast] lemma coe_bot : (⊥ : BooleanSubalgebra α) = ({⊥, ⊤} : Set α) := rfl
@[simp, norm_cast] lemma coe_inf (L M : BooleanSubalgebra α) : L ⊓ M = (L : Set α) ∩ M := rfl

@[simp, norm_cast]
lemma coe_sInf (S : Set (BooleanSubalgebra α)) : sInf S = ⋂ L ∈ S, (L : Set α) := rfl

@[simp, norm_cast]
lemma coe_iInf (f : ι → BooleanSubalgebra α) : ⨅ i, f i = ⋂ i, (f i : Set α) := by simp [iInf]

@[simp, norm_cast] lemma coe_eq_univ : L = (univ : Set α) ↔ L = ⊤ := by rw [← coe_top, coe_inj]

@[simp] lemma mem_bot : a ∈ (⊥ : BooleanSubalgebra α) ↔ a = ⊥ ∨ a = ⊤ := .rfl
@[simp] lemma mem_top : a ∈ (⊤ : BooleanSubalgebra α) := mem_univ _
@[simp] lemma mem_inf : a ∈ L ⊓ M ↔ a ∈ L ∧ a ∈ M := .rfl
@[simp] lemma mem_sInf {S : Set (BooleanSubalgebra α)} : a ∈ sInf S ↔ ∀ L ∈ S, a ∈ L := by
  rw [← SetLike.mem_coe]; simp
@[simp] lemma mem_iInf {f : ι → BooleanSubalgebra α} : a ∈ ⨅ i, f i ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe]; simp

/-- BooleanSubalgebras of a lattice form a complete lattice. -/
instance instCompleteLattice : CompleteLattice (BooleanSubalgebra α) where
  bot := ⊥
  bot_le _S _a := by aesop
  top := ⊤
  le_top _S a _ha := mem_top
  inf := (· ⊓ ·)
  le_inf _L _M _N hM hN _a ha := ⟨hM ha, hN ha⟩
  inf_le_left _L _M _a := And.left
  inf_le_right _L _M _a := And.right
  __ := completeLatticeOfInf (BooleanSubalgebra α)
      fun _s ↦ IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf

instance [IsEmpty α] : Subsingleton (BooleanSubalgebra α) := SetLike.coe_injective.subsingleton
instance [IsEmpty α] : Unique (BooleanSubalgebra α) := uniqueOfSubsingleton ⊤

/-- The preimage of a boolean subalgebra along a bounded lattice homomorphism. -/
def comap (f : BoundedLatticeHom α β) (L : BooleanSubalgebra β) : BooleanSubalgebra α where
  carrier := f ⁻¹' L
  bot_mem' := by simp
  compl_mem' := by simp [map_compl']
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _

@[simp, norm_cast]
lemma coe_comap (L : BooleanSubalgebra β) (f : BoundedLatticeHom α β) : L.comap f = f ⁻¹' L := rfl

@[simp] lemma mem_comap {L : BooleanSubalgebra β} : a ∈ L.comap f ↔ f a ∈ L := .rfl

lemma comap_mono : Monotone (comap f) := fun _ _ ↦ preimage_mono

@[simp] lemma comap_id (L : BooleanSubalgebra α) : L.comap (BoundedLatticeHom.id _) = L := rfl

@[simp] lemma comap_comap (L : BooleanSubalgebra γ) (g : BoundedLatticeHom β γ)
    (f : BoundedLatticeHom α β) : (L.comap g).comap f = L.comap (g.comp f) := rfl

/-- The image of a boolean subalgebra along a monoid homomorphism is a boolean subalgebra. -/
def map (f : BoundedLatticeHom α β) (L : BooleanSubalgebra α) : BooleanSubalgebra β where
  carrier := f '' L
  bot_mem' := ⟨⊥, by simp⟩
  compl_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨aᶜ, by simpa [map_compl']⟩
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f

@[simp] lemma coe_map (f : BoundedLatticeHom α β) (L : BooleanSubalgebra α) :
    (L.map f : Set β) = f '' L := rfl

@[simp] lemma mem_map {b : β} : b ∈ L.map f ↔ ∃ a ∈ L, f a = b := .rfl

lemma mem_map_of_mem (f : BoundedLatticeHom α β) {a : α} : a ∈ L → f a ∈ L.map f :=
  mem_image_of_mem f

lemma apply_coe_mem_map (f : BoundedLatticeHom α β) (a : L) : f a ∈ L.map f :=
  mem_map_of_mem f a.prop

lemma map_mono : Monotone (map f) := fun _ _ ↦ image_subset _

@[simp] lemma map_id : L.map (.id α) = L := SetLike.coe_injective <| image_id _

@[simp] lemma map_map (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    (L.map f).map g = L.map (g.comp f) := SetLike.coe_injective <| image_image _ _ _

lemma mem_map_equiv {f : α ≃o β} {a : β} : a ∈ L.map f ↔ f.symm a ∈ L := Set.mem_image_equiv

lemma apply_mem_map_iff (hf : Injective f) : f a ∈ L.map f ↔ a ∈ L := hf.mem_set_image

lemma map_equiv_eq_comap_symm (f : α ≃o β) (L : BooleanSubalgebra α) :
    L.map f = L.comap (f.symm : BoundedLatticeHom β α) :=
  SetLike.coe_injective <| f.toEquiv.image_eq_preimage L

lemma comap_equiv_eq_map_symm (f : β ≃o α) (L : BooleanSubalgebra α) :
    L.comap f = L.map (f.symm : BoundedLatticeHom α β) := (map_equiv_eq_comap_symm f.symm L).symm

lemma map_symm_eq_iff_eq_map {M : BooleanSubalgebra β} {e : β ≃o α} :
    L.map ↑e.symm = M ↔ L = M.map ↑e := by
  simp_rw [← coe_inj]; exact (Equiv.eq_image_iff_symm_image_eq _ _ _).symm

lemma map_le_iff_le_comap {f : BoundedLatticeHom α β} {M : BooleanSubalgebra β} :
    L.map f ≤ M ↔ L ≤ M.comap f := image_subset_iff

lemma gc_map_comap (f : BoundedLatticeHom α β) : GaloisConnection (map f) (comap f) :=
  fun _ _ ↦ map_le_iff_le_comap

@[simp] lemma map_bot (f : BoundedLatticeHom α β) : (⊥ : BooleanSubalgebra α).map f = ⊥ :=
  (gc_map_comap f).l_bot

lemma map_sup (f : BoundedLatticeHom α β) (L M : BooleanSubalgebra α) :
    (L ⊔ M).map f = L.map f ⊔ M.map f := (gc_map_comap f).l_sup

lemma map_iSup (f : BoundedLatticeHom α β) (L : ι → BooleanSubalgebra α) :
    (⨆ i, L i).map f = ⨆ i, (L i).map f := (gc_map_comap f).l_iSup

@[simp] lemma comap_top (f : BoundedLatticeHom α β) : (⊤ : BooleanSubalgebra β).comap f = ⊤ :=
  (gc_map_comap f).u_top

lemma comap_inf (L M : BooleanSubalgebra β) (f : BoundedLatticeHom α β) :
    (L ⊓ M).comap f = L.comap f ⊓ M.comap f := (gc_map_comap f).u_inf

lemma comap_iInf (f : BoundedLatticeHom α β) (L : ι → BooleanSubalgebra β) :
    (⨅ i, L i).comap f = ⨅ i, (L i).comap f := (gc_map_comap f).u_iInf

lemma map_inf_le (L M : BooleanSubalgebra α) (f : BoundedLatticeHom α β) :
    map f (L ⊓ M) ≤ map f L ⊓ map f M := map_mono.map_inf_le _ _

lemma le_comap_sup (L M : BooleanSubalgebra β) (f : BoundedLatticeHom α β) :
    comap f L ⊔ comap f M ≤ comap f (L ⊔ M) := comap_mono.le_map_sup _ _

lemma le_comap_iSup (f : BoundedLatticeHom α β) (L : ι → BooleanSubalgebra β) :
    ⨆ i, (L i).comap f ≤ (⨆ i, L i).comap f := comap_mono.le_map_iSup

lemma map_inf (L M : BooleanSubalgebra α) (f : BoundedLatticeHom α β) (hf : Injective f) :
    map f (L ⊓ M) = map f L ⊓ map f M := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

lemma map_top (f : BoundedLatticeHom α β) (h : Surjective f) : BooleanSubalgebra.map f ⊤ = ⊤ :=
  SetLike.coe_injective <| by simp [h.range_eq]

/-- The minimum boolean subalgebra containing a given set. -/
def closure (s : Set α) : BooleanSubalgebra α := sInf {L | s ⊆ L}

variable {s : Set α}

lemma mem_closure {x : α} : x ∈ closure s ↔ ∀ ⦃L : BooleanSubalgebra α⦄, s ⊆ L → x ∈ L := mem_sInf

@[aesop safe 20 apply (rule_sets := [SetLike])]
lemma subset_closure : s ⊆ closure s := fun _ hx ↦ mem_closure.2 fun _ hK ↦ hK hx

@[simp] lemma closure_le : closure s ≤ L ↔ s ⊆ L := ⟨subset_closure.trans, fun h ↦ sInf_le h⟩

lemma closure_mono (hst : s ⊆ t) : closure s ≤ closure t := sInf_le_sInf fun _L ↦ hst.trans

lemma latticeClosure_subset_closure : latticeClosure s ⊆ closure s :=
  latticeClosure_min subset_closure (closure s).isSublattice

@[simp] lemma closure_latticeClosure (s : Set α) : closure (latticeClosure s) = closure s :=
  le_antisymm (closure_le.2 latticeClosure_subset_closure) (closure_mono subset_latticeClosure)

/-- An induction principle for closure membership. If `p` holds for `⊥` and all elements of `s`, and
is preserved under suprema and complement, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_elim]
lemma closure_bot_sup_induction {p : ∀ g ∈ closure s, Prop} (mem : ∀ x hx, p x (subset_closure hx))
    (bot : p ⊥ bot_mem)
    (sup : ∀ x hx y hy, p x hx → p y hy → p (x ⊔ y) (supClosed _ hx hy))
    (compl : ∀ x hx, p x hx → p xᶜ (compl_mem hx)) {x} (hx : x ∈ closure s) : p x hx :=
  have inf ⦃x hx y hy⦄ (hx' : p x hx) (hy' : p y hy) : p (x ⊓ y) (infClosed _ hx hy) := by
    simpa using compl _ _ <| sup _ _ _ _ (compl _ _ hx') (compl _ _ hy')
  let L : BooleanSubalgebra α :=
    { carrier := { x | ∃ hx, p x hx }
      supClosed' := fun _a ⟨_, ha⟩ _b ⟨_, hb⟩ ↦ ⟨_, sup _ _ _ _ ha hb⟩
      infClosed' := fun _a ⟨_, ha⟩ _b ⟨_, hb⟩ ↦ ⟨_, inf ha hb⟩
      bot_mem' := ⟨_, bot⟩
      compl_mem' := fun ⟨_, hb⟩ ↦ ⟨_, compl _ _ hb⟩ }
  closure_le (L := L).mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

section sdiff_sup

variable (isSublattice : IsSublattice s) (bot_mem : ⊥ ∈ s) (top_mem : ⊤ ∈ s)
include isSublattice bot_mem top_mem

theorem mem_closure_iff_sup_sdiff {a : α} :
    a ∈ closure s ↔ ∃ t : Finset (s × s), a = t.sup fun x ↦ x.1.1 \ x.2.1 := by
  classical
  refine ⟨closure_bot_sup_induction
    (fun x h ↦ ⟨{(⟨x, h⟩, ⟨⊥, bot_mem⟩)}, by simp⟩) ⟨∅, by simp⟩ ?_ ?_, ?_⟩
  · rintro ⟨t, rfl⟩
    exact t.sup_mem _ (subset_closure bot_mem) (fun _ h _ ↦ sup_mem h) _
      fun x hx ↦ sdiff_mem (subset_closure x.1.2) (subset_closure x.2.2)
  · rintro _ - _ - ⟨t₁, rfl⟩ ⟨t₂, rfl⟩
    exact ⟨t₁ ∪ t₂, by rw [Finset.sup_union]⟩
  rintro x - ⟨t, rfl⟩
  refine t.induction ⟨{(⟨⊤, top_mem⟩, ⟨⊥, bot_mem⟩)}, by simp⟩ fun ⟨x, y⟩ t _ ⟨tc, eq⟩ ↦ ?_
  simp_rw [Finset.sup_insert, compl_sup, eq]
  refine tc.induction ⟨∅, by simp⟩ fun ⟨z, w⟩ tc _ ⟨t, eq⟩ ↦ ?_
  simp_rw [Finset.sup_insert, inf_sup_left, eq]
  use {(z, ⟨_, isSublattice.supClosed x.2 w.2⟩), (⟨_, isSublattice.infClosed y.2 z.2⟩, w)} ∪ t
  simp_rw [Finset.sup_union, Finset.sup_insert, Finset.sup_singleton, sdiff_eq,
    compl_sup, inf_left_comm z.1, compl_inf, compl_compl, inf_sup_right, inf_assoc]

@[elab_as_elim] theorem closure_sdiff_sup_induction {p : ∀ g ∈ closure s, Prop}
    (sdiff : ∀ x hx y hy, p (x \ y) (sdiff_mem (subset_closure hx) (subset_closure hy)))
    (sup : ∀ x hx y hy, p x hx → p y hy → p (x ⊔ y) (sup_mem hx hy))
    (x) (hx : x ∈ closure s) : p x hx := by
  obtain ⟨t, rfl⟩ := (mem_closure_iff_sup_sdiff isSublattice bot_mem top_mem).mp hx
  revert hx
  classical
  refine t.induction (by simpa using sdiff _ bot_mem _ bot_mem) fun x t _ ih hxt ↦ ?_
  simp only [Finset.sup_insert] at hxt ⊢
  exact sup _ _ _ ((mem_closure_iff_sup_sdiff isSublattice bot_mem top_mem).mpr ⟨_, rfl⟩)
    (sdiff _ x.1.2 _ x.2.2) (ih _)

end sdiff_sup

end BooleanAlgebra

section CompleteBooleanAlgebra
variable [CompleteBooleanAlgebra α] {L : BooleanSubalgebra α} {f : ι → α} {s : Set α}

lemma iSup_mem [Finite ι] (hf : ∀ i, f i ∈ L) : ⨆ i, f i ∈ L := L.supClosed.iSup_mem bot_mem hf
lemma iInf_mem [Finite ι] (hf : ∀ i, f i ∈ L) : ⨅ i, f i ∈ L := L.infClosed.iInf_mem top_mem hf
lemma sSup_mem (hs : s.Finite) (hsL : s ⊆ L) : sSup s ∈ L := L.supClosed.sSup_mem hs bot_mem hsL
lemma sInf_mem (hs : s.Finite) (hsL : s ⊆ L) : sInf s ∈ L := L.infClosed.sInf_mem hs top_mem hsL

lemma biSup_mem {ι : Type*} {t : Set ι} {f : ι → α} (ht : t.Finite) (hf : ∀ i ∈ t, f i ∈ L) :
    ⨆ i ∈ t, f i ∈ L := L.supClosed.biSup_mem ht bot_mem hf

lemma biInf_mem {ι : Type*} {t : Set ι} {f : ι → α} (ht : t.Finite) (hf : ∀ i ∈ t, f i ∈ L) :
    ⨅ i ∈ t, f i ∈ L := L.infClosed.biInf_mem ht top_mem hf

end CompleteBooleanAlgebra
end BooleanSubalgebra
