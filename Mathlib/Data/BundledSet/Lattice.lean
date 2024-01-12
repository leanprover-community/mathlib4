import Mathlib.Tactic.SetLike
import Mathlib.Data.BundledSet.Basic
import Mathlib.Data.Set.Lattice

open Set

namespace BundledSet

section SemilatticeInf

class InterPred (α : Type*) (p : Set α → Prop) : Prop where
  inter : ∀ s, p s → ∀ t, p t → p (s ∩ t)

variable {α : Type*} {p : Set α → Prop} [InterPred α p]

instance InterPred.and {q : Set α → Prop} [InterPred α q] : InterPred α (fun s ↦ p s ∧ q s) :=
  ⟨fun s hs t ht ↦ ⟨inter s hs.1 t ht.1, inter s hs.2 t ht.2⟩⟩

instance InterPred.mem_implies {x : α} : InterPred α (fun s ↦ x ∈ s → p s) :=
  ⟨fun s hs t ht ⟨hxs, hxt⟩ ↦ inter s (hs hxs) t (ht hxt)⟩

instance InterPred.forall {ι : Sort*} {p : ι → Set α → Prop} [∀ i, InterPred α (p i)] :
    InterPred α (∀ i, p i ·) :=
  ⟨fun s hs t ht i ↦ inter s (hs i) t (ht i)⟩

instance InterPred.mem {x : α} : InterPred α (x ∈ ·) := ⟨fun _s hs _t ht ↦ ⟨hs, ht⟩⟩

protected instance instInf : Inf (BundledSet α p) where
  inf s t := ⟨s ∩ t, InterPred.inter s s.2 t t.2⟩

@[simp]
theorem inf_carrier (s t : BundledSet α p) : (s ⊓ t).carrier = ↑s ∩ ↑t := rfl

@[simp] theorem mem_inf {s t : BundledSet α p} {x : α} : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := .rfl

protected instance instSemilatticeInf : SemilatticeInf (BundledSet α p) where
  toPartialOrder := BundledSet.instPartialOrder
  toInf := BundledSet.instInf
  __ := carrier_injective.semilatticeInf _ inf_carrier

end SemilatticeInf

section SemilatticeSup

class SupPred (α : Type*) (p : Set α → Prop) (op : outParam <| Set α → Set α → Set α) : Prop where
  sup : ∀ ⦃s⦄, p s → ∀ ⦃t⦄, p t → p (op s t)
  left_subset_sup (s t : BundledSet α p) : s.1 ⊆ op s t
  right_subset_sup (s t : BundledSet α p) : t.1 ⊆ op s t
  sup_subset (s t u : BundledSet α p) : s ≤ u → t ≤ u → op s t ⊆ u

variable {α : Type*} {p : Set α → Prop} {op : Set α → Set α → Set α}

theorem SupPred.mk_union (h : ∀ ⦃s⦄, p s → ∀ ⦃t⦄, p t → p (s ∪ t)) : SupPred α p (· ∪ ·) where
  sup := h
  left_subset_sup _ _ := subset_union_left _ _
  right_subset_sup _ _ := subset_union_right _ _
  sup_subset _ _ _ := union_subset

variable [SupPred α p op]

protected instance instSemilatticeSup : SemilatticeSup (BundledSet α p) where
  sup s t := ⟨op s t, SupPred.sup s.2 t.2⟩
  le_sup_left := SupPred.left_subset_sup
  le_sup_right := SupPred.right_subset_sup
  sup_le := SupPred.sup_subset

@[simp]
lemma carrier_sup_eq_union [SupPred α p (· ∪ ·)] (s t : BundledSet α p) :
    (s ⊔ t).1 = s.1 ∪ t :=
  rfl

lemma mem_sup_left {s t : BundledSet α p} {x : α} (h : x ∈ s) : x ∈ s ⊔ t :=
  (le_sup_left : s ≤ s ⊔ t) h

lemma mem_sup_right {s t : BundledSet α p} {x : α} (h : x ∈ t) : x ∈ s ⊔ t :=
  (le_sup_right : t ≤ s ⊔ t) h

end SemilatticeSup

protected instance instLattice {α : Type*} {p : Set α → Prop} {op : Set α → Set α → Set α}
    [InterPred α p] [SupPred α p op] : Lattice (BundledSet α p) where
  toSemilatticeSup := BundledSet.instSemilatticeSup
  __ := BundledSet.instSemilatticeInf

section OrderTop

class UnivPred (α : Type*) (p : Set α → Prop) : Prop where
  univ : p Set.univ

variable {α : Type*} {p : Set α → Prop} [UnivPred α p]

instance UnivPred.and {q : Set α → Prop} [UnivPred α q] : UnivPred α (fun s ↦ p s ∧ q s) :=
  ⟨univ, univ⟩

instance UnivPred.mem_implies {x : α} : UnivPred α (fun s ↦ x ∈ s → p s) :=
  ⟨fun _ ↦ univ⟩

instance UnivPred.forall {ι : Sort*} {p : ι → Set α → Prop} [∀ i, UnivPred α (p i)] :
    UnivPred α (∀ i, p i ·) :=
  ⟨fun _ ↦ univ⟩

instance UnivPred.mem {x : α} : UnivPred α (x ∈ ·) := ⟨mem_univ x⟩

protected instance instOrderTop : OrderTop (BundledSet α p) where
  top := ⟨univ, UnivPred.univ⟩
  le_top s := subset_univ s.1

@[simp] theorem top_carrier : (⊤ : BundledSet α p).1 = univ := rfl
@[simp] theorem mem_top (x : α) : x ∈ (⊤ : BundledSet α p) := trivial

end OrderTop

section OrderBot

class BotPred (α : Type*) (p : Set α → Prop) (b : outParam (Set α)) : Prop where
  bot : p b
  bot_subset {t} : p t → b ⊆ t

theorem BotPred.mk_empty {α : Type*} {p : Set α → Prop} (h : p ∅) : BotPred α p ∅ :=
  ⟨h, fun _ ↦ empty_subset _⟩

variable {α : Type*} {p : Set α → Prop} {b : Set α} [BotPred α p b]

protected instance instOrderBot : OrderBot (BundledSet α p) where
  bot := ⟨b, BotPred.bot⟩
  bot_le t := BotPred.bot_subset t.2

@[simp] theorem bot_carrier : (⊥ : BundledSet α p).1 = b := rfl
protected theorem mem_bot {x : α} : x ∈ (⊥ : BundledSet α p) ↔ x ∈ b := .rfl

variable [UnivPred α p]

protected instance instBoundedOrder : BoundedOrder (BundledSet α p) where

theorem subsingleton_iff : Subsingleton (BundledSet α p) ↔ b = univ := by
  rw [← subsingleton_iff_bot_eq_top, ← carrier_inj]; rfl

theorem nontrivial_iff : Nontrivial (BundledSet α p) ↔ b ≠ univ := by
  rw [← not_iff_not, not_nontrivial_iff_subsingleton, subsingleton_iff, Ne.def, not_not]

end OrderBot

@[simp]
theorem not_mem_bot {α : Type*} {p : Set α → Prop} [BotPred α p ∅] {x : α} :
    x ∉ (⊥ : BundledSet α p) :=
  not_false

section CompleteSemilatticeInf

class SetInterPred (α : Type*) (p : Set α → Prop) : Prop where
  sInter (S : Set (Set α)) : (∀ s ∈ S, p s) → p (⋂₀ S)

variable {α : Type*} {ι : Sort*} {p : Set α → Prop} [SetInterPred α p]

instance SetInterPred.and {q : Set α → Prop} [SetInterPred α q] :
    SetInterPred α (fun s ↦ p s ∧ q s) :=
  ⟨fun S hS ↦ ⟨sInter S fun s hs ↦ (hS s hs).1, sInter S fun s hs ↦ (hS s hs).2⟩⟩

instance SetInterPred.mem_implies {x : α} : SetInterPred α (fun s ↦ x ∈ s → p s) :=
  ⟨fun S hS hx ↦ sInter S fun s hs ↦ hS s hs <| sInter_subset_of_mem hs hx⟩

instance SetInterPred.forall {ι : Sort*} {p : ι → Set α → Prop} [∀ i, SetInterPred α (p i)] :
    SetInterPred α (∀ i, p i ·) :=
  ⟨fun S hS i ↦ sInter S (hS · · i)⟩

instance SetInterPred.mem {x : α} : SetInterPred α (x ∈ ·) := ⟨fun _ ↦ id⟩

instance (priority := low) : InterPred α p where
  inter (s hs t ht) := by simpa [*] using SetInterPred.sInter (p := p) {s, t}

instance (priority := low) : UnivPred α p where
  univ := by simpa using SetInterPred.sInter ∅

instance instCompleteSemilatticeInf : CompleteSemilatticeInf (BundledSet α p) where
  toPartialOrder := BundledSet.instPartialOrder
  sInf S := ⟨⋂ s ∈ S, ↑s, by
    rw [← sInter_image]
    exact SetInterPred.sInter _ <| ball_image_iff.2 fun s _ ↦ s.2⟩
  le_sInf S s hs := subset_iInter₂ hs
  sInf_le S s hs := biInter_subset_of_mem hs

@[simp, norm_cast]
theorem sInf_carrier (S : Set (BundledSet α p)) : (sInf S).carrier = ⋂ s ∈ S, ↑s := rfl

@[simp, norm_cast]
theorem iInf_carrier {S : ι → BundledSet α p} : (⨅ i, S i).1 = ⋂ i, ↑(S i) := by simp [iInf]

@[simp]
theorem mem_sInf {S : Set (BundledSet α p)} {x : α} : x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s := mem_iInter₂

@[simp]
theorem mem_iInf {S : ι → BundledSet α p} {x : α} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by simp [iInf]

variable (α p)

theorem BotPred.of_setInterPred : BotPred α p (sInf (univ : Set (BundledSet α p))).1 where
  bot := BundledSet.prop _
  bot_subset {t} ht := by rw [← carrier_mk t ht, carrier_subset_carrier]; exact sInf_le trivial

def supOfSetInter (s t : Set α) : Set α := (sInf {u | s ⊆ u ∧ t ⊆ u} : BundledSet α p)

theorem SupPred.of_setInterPred :
    SupPred α p (supOfSetInter α p) where
  sup _ _ _ _ := BundledSet.prop _
  left_subset_sup _ _ := carrier_subset_carrier.2 <| le_sInf fun _ ↦ And.left
  right_subset_sup _ _ := carrier_subset_carrier.2 <| le_sInf fun _ ↦ And.right
  sup_subset _ _ _ ha hb := carrier_subset_carrier.2 <| sInf_le ⟨ha, hb⟩

variable {α p}

instance instCompleteSemilatticeSupOfInf : CompleteSemilatticeSup (BundledSet α p) where
  sSup S := sInf (upperBounds S)
  le_sSup _ _ hs := le_sInf fun _ h ↦ h hs
  sSup_le _ _ hs := sInf_le hs

theorem mem_sSup {x : α} {S : Set (BundledSet α p)} : x ∈ sSup S ↔ ∀ t ∈ upperBounds S, x ∈ t :=
  mem_sInf

theorem mem_iSup {x : α} {s : ι → BundledSet α p} : x ∈ iSup s ↔ ∀ t, (∀ i, s i ≤ t) → x ∈ t :=
  mem_sSup.trans <| by simp only [mem_upperBounds, forall_range_iff]

variable (α p) in
def completeLatticeOfBotSupSetInter {b : outParam (Set α)} {sup : outParam (Set α → Set α → Set α)}
    [BotPred α p b] [SupPred α p sup] : CompleteLattice (BundledSet α p) where
  __ := instCompleteSemilatticeInf
  __ := BundledSet.instBoundedOrder
  __ := instCompleteSemilatticeSupOfInf
  toLattice := BundledSet.instLattice

variable (α p) in
def completeLatticeOfSetInter : CompleteLattice (BundledSet α p) :=
  haveI := BotPred.of_setInterPred α p
  haveI := SupPred.of_setInterPred α p
  BundledSet.completeLatticeOfBotSupSetInter α p

variable (p)

protected def closure (s : Set α) : BundledSet α p := sInf {t | s ⊆ t}

protected theorem gc : GaloisConnection (BundledSet.closure p) carrier := fun _ _ ↦
  ⟨Subset.trans <| subset_iInter₂ fun _ ↦ id, fun h ↦ sInf_le h⟩

protected def gi : GaloisInsertion (BundledSet.closure p) carrier :=
  (BundledSet.gc p).toGaloisInsertion fun _ ↦ le_sInf fun _ ↦ id

variable {p}

theorem mem_closure {s : Set α} {x : α} :
    x ∈ BundledSet.closure p s ↔ ∀ t : BundledSet α p, s ⊆ t → x ∈ t :=
  mem_iInter₂

@[simp]
theorem closure_le {s : Set α} {t : BundledSet α p} : BundledSet.closure p s ≤ t ↔ s ⊆ t :=
  BundledSet.gc _ _ _

@[simp]
theorem closure_eq (s : BundledSet α p) : BundledSet.closure p s = s :=
  (BundledSet.gi p).l_u_eq _

@[simp, aesop safe 20 apply (rule_sets [SetLike])]
theorem subset_closure {s : Set α} : s ⊆ BundledSet.closure p s := closure_le.1 le_rfl

theorem not_mem_of_not_mem_closure {x : α} {s : Set α} (hx : x ∉ BundledSet.closure p s) :
    x ∉ s := fun h =>
  hx (subset_closure h)

theorem closure_eq_of_le {s : Set α} {S : BundledSet α p} (h₁ : s ⊆ S)
    (h₂ : S ≤ BundledSet.closure p s) : BundledSet.closure p s = S :=
  (closure_le.2 h₁).antisymm h₂

theorem closure_singleton_le {a : α} {t : BundledSet α p} :
    BundledSet.closure p {a} ≤ t ↔ a ∈ t := by
  simp

@[simp] theorem closure_univ : BundledSet.closure p univ = ⊤ := (BundledSet.gi p).l_top

@[simp]
theorem closure_empty {b} [BotPred α p b] : BundledSet.closure p ∅ = ⊥ :=
  (BundledSet.gc p).l_bot

@[simp] theorem closure_eq_bot {b s} [BotPred α p b] : BundledSet.closure p s = ⊥ ↔ s ⊆ b :=
  (BundledSet.gc p).l_eq_bot

@[mono]
theorem closure_mono : Monotone (BundledSet.closure p) := (BundledSet.gc p).monotone_l

theorem closure_union {op} [SupPred α p op] (s t : Set α) :
    BundledSet.closure p (s ∪ t) = BundledSet.closure p s ⊔ BundledSet.closure p t :=
  (BundledSet.gc (p := p)).l_sup

theorem closure_iUnion (s : ι → Set α) :
    BundledSet.closure p (⋃ i, s i) = ⨆ i, BundledSet.closure p (s i) :=
  let _ := completeLatticeOfSetInter α p
  (BundledSet.gc p).l_iSup

theorem iSup_eq_closure (s : ι → BundledSet α p) :
    (⨆ i, s i) = BundledSet.closure p (⋃ i, s i) := by
  simp_rw [closure_iUnion, closure_eq]

end CompleteSemilatticeInf

section DirectedUnion

class DirectedSetUnionPred (α : Type*) (p : Set α → Prop) : Prop where
  directedSUnion : ∀ S : Set (Set α), S.Nonempty → DirectedOn (· ⊆ ·) S → (∀ s ∈ S, p s) → p (⋃₀ S)

variable {α : Type*} {p : Set α → Prop} [DirectedSetUnionPred α p]

instance DirectedSetUnionPred.and {q : Set α → Prop} [DirectedSetUnionPred α q] :
    DirectedSetUnionPred α (fun s ↦ p s ∧ q s) :=
  ⟨fun S hne hdS hS ↦ ⟨directedSUnion S hne hdS fun s hs ↦ (hS s hs).1,
    directedSUnion S hne hdS fun s hs ↦ (hS s hs).2⟩⟩

instance DirectedSetUnionPred.mem_implies {x : α} : DirectedSetUnionPred α (fun s ↦ x ∈ s → p s) :=
  ⟨fun S _ hdS hS hxS ↦ by
    -- TODO: move to a lemma
    have H₁ : ⋃₀ S = ⋃₀ (S ∩ {s | x ∈ s}) := by
      refine Subset.antisymm ?_ (sUnion_mono <| inter_subset_left _ _)
      rintro y ⟨s, hs, hys⟩
      rcases hxS with ⟨t, ht, hxt⟩
      rcases hdS s hs t ht with ⟨u, hu, hsu, htu⟩
      exact ⟨u, ⟨hu, htu hxt⟩, hsu hys⟩
    rw [H₁]
    refine directedSUnion _ hxS ?_ fun s hs ↦ hS s hs.1 hs.2
    -- TODO: move to a lemma
    rintro s ⟨hs, hxs⟩ t ⟨ht, -⟩
    rcases hdS s hs t ht with ⟨u, hu, hsu, htu⟩
    exact ⟨u, ⟨hu, hsu hxs⟩, hsu, htu⟩⟩

instance DirectedSetUnionPred.forall {ι : Sort*} {p : ι → Set α → Prop}
    [∀ i, DirectedSetUnionPred α (p i)] : DirectedSetUnionPred α (∀ i, p i ·) :=
  ⟨fun S hne hdS hS i ↦ directedSUnion S hne hdS (hS · · i)⟩

instance DirectedSetUnionPred.mem {x : α} : DirectedSetUnionPred α (x ∈ ·) :=
  ⟨fun _S ⟨s, hs⟩ _ hS ↦ ⟨s, hs, hS s hs⟩⟩

variable [SetInterPred α p]

lemma carrier_sSup_of_directedOn {S : Set (BundledSet α p)} (hne : S.Nonempty)
    (hd : DirectedOn (· ≤ ·) S) : (sSup S : BundledSet α p).1 = ⋃ s ∈ S, s := by
  have hU : p (⋃ s ∈ S, s) := by
    rw [← sUnion_image]
    apply DirectedSetUnionPred.directedSUnion
    · exact hne.image _
    · rwa [directedOn_image]
    · exact ball_image_iff.2 fun s _ ↦ s.2
  have : sSup S = ⟨_, hU⟩ := eq_of_forall_ge_iff fun _ ↦ sSup_le_iff.trans iUnion₂_subset_iff.symm
  simp [this]

lemma mem_sSup_of_directedOn {S : Set (BundledSet α p)} (hne : S.Nonempty)
    (hd : DirectedOn (· ≤ ·) S) {x : α} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  rw [← mem_carrier]
  simp [carrier_sSup_of_directedOn hne hd]

lemma carrier_iSup_of_directed {ι : Sort*} [Nonempty ι] {s : ι → BundledSet α p}
    (hd : Directed (· ≤ ·) s) : (⨆ i, s i).1 = ⋃ i, s i :=
  (carrier_sSup_of_directedOn (range_nonempty s) hd.directedOn_range).trans biUnion_range

lemma mem_iSup_of_directed {ι : Sort*} [Nonempty ι] {s : ι → BundledSet α p}
    (hd : Directed (· ≤ ·) s) {x : α} : (x ∈ ⨆ i, s i) ↔ ∃ i, x ∈ s i :=
  (mem_sSup_of_directedOn (range_nonempty _) hd.directedOn_range).trans exists_range_iff

lemma carrier_biSup_of_directedOn {ι : Type*} {I : Set ι} {s : ι → BundledSet α p}
    (hne : I.Nonempty) (hd : DirectedOn (s · ≤ s ·) I) : (⨆ i ∈ I, s i).1 = ⋃ i ∈ I, s i := by
  let _ := completeLatticeOfSetInter α p
  rw [← sSup_image, carrier_sSup_of_directedOn (hne.image _) (directedOn_image.2 hd), biUnion_image]

lemma mem_biSup_of_directedOn {ι : Type*} {I : Set ι} {s : ι → BundledSet α p}
    (hne : I.Nonempty) (hd : DirectedOn (s · ≤ s ·) I) {x : α} :
    x ∈ ⨆ i ∈ I, s i ↔ ∃ i ∈ I, x ∈ s i := by
  simp_rw [← mem_carrier, carrier_biSup_of_directedOn hne hd, mem_iUnion₂, exists_prop]

variable [BotPred α p ∅]

lemma mem_sSup_of_directedOn' {S : Set (BundledSet α p)} (hd : DirectedOn (· ≤ ·) S) {x : α} :
    x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  have := SupPred.of_setInterPred α p; letI := completeLatticeOfBotSupSetInter α p
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · exact mem_sSup_of_directedOn hne hd

lemma carrier_sSup_of_directedOn' {S : Set (BundledSet α p)}
    (hd : DirectedOn (· ≤ ·) S) : (sSup S : BundledSet α p).1 = ⋃ s ∈ S, s := by
  ext; simp [mem_sSup_of_directedOn' hd]

lemma mem_iSup_of_directed' {ι : Sort*} {s : ι → BundledSet α p} (hd : Directed (· ≤ ·) s) {x : α} :
    (x ∈ ⨆ i, s i) ↔ ∃ i, x ∈ s i :=
  (mem_sSup_of_directedOn' hd.directedOn_range).trans exists_range_iff

lemma carrier_iSup_of_directed' {ι : Sort*} {s : ι → BundledSet α p} (hd : Directed (· ≤ ·) s) :
    (⨆ i, s i).1 = ⋃ i, s i :=
  (carrier_sSup_of_directedOn' hd.directedOn_range).trans biUnion_range

lemma carrier_biSup_of_directedOn' {ι : Type*} {I : Set ι} {s : ι → BundledSet α p}
    (hd : DirectedOn (s · ≤ s ·) I) : (⨆ i ∈ I, s i).1 = ⋃ i ∈ I, s i := by
  let _ := completeLatticeOfSetInter α p
  rw [← sSup_image, carrier_sSup_of_directedOn' (directedOn_image.2 hd), biUnion_image]

lemma mem_biSup_of_directedOn' {ι : Type*} {I : Set ι} {s : ι → BundledSet α p}
    (hd : DirectedOn (s · ≤ s ·) I) {x : α} :
    x ∈ ⨆ i ∈ I, s i ↔ ∃ i ∈ I, x ∈ s i := by
  simp_rw [← mem_carrier, carrier_biSup_of_directedOn' hd, mem_iUnion₂, exists_prop]

end DirectedUnion

end BundledSet
