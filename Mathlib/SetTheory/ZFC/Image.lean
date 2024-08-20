import Mathlib.SetTheory.ZFC.Ordinal

noncomputable section
set_option autoImplicit true

axiom Quot.move {ι} {α : ι → Sort*} {r : ∀ i, α i → α i → Prop}
    (x : ∀ i, Quot (r i)) : Quot (fun (a b : ∀ i, α i) => ∀ i, r i (a i) (b i))

axiom Quot.move_rec {ι} {α : ι → Sort*} {r : ∀ i, α i → α i → Prop}
    (x : ∀ i, Quot (r i)) (y : ∀ i, α i)
  : Quot.move x = Quot.mk _ y ↔ ∀ i, x i = Quot.mk _ (y i)

def Quot.lift' {α β ι} {r : α → α → Prop}
    (x : ι → Quot r) (f : (ι → α) → β) (eq : ∀ a b, (∀ i, r (a i) (b i)) → f a = f b) : β :=
  Quot.lift f eq (Quot.move x)

def lm1 {r : α → α → Prop} {f : α → β} (eq : ∀ (a b : α), r a b → f a = f b)
    {a b : α} (R : EqvGen r a b) : f a = f b :=
  EqvGen.rec eq (fun _ => rfl) (fun _ _ _ e => e.symm) (fun _ _ _ _ _ e e' => e.trans e') R

def lm2 {α : Type*} {r : α → α → Prop} {f : α → β} (eq : ∀ (a b : α), r a b → f a = f b)
    {a b : α} (R : Quot.mk r a = Quot.mk r b) : f a = f b :=
  lm1 eq (Quot.eq.mp R)

def Quot.lift_prop {α : Type*} {β} {r : α → α → Prop} {p : β → Prop} (f : α → β)
    (eq : ∀ (a b : α), r a b → f a = f b) (x : Quot r)
  : p (Quot.lift f eq x) ↔ ∃ y, x = Quot.mk r y ∧ p (f y) := by
  induction x using Quot.ind
  rename α => y
  simpa only using ⟨fun h => ⟨y, rfl, h⟩, fun ⟨z, h₁, h₂⟩ => lm2 eq h₁ ▸ h₂⟩

def Quot.lift_prop' {α : Type*} {β} {r : α → α → Prop} {p : β → Prop} (f : α → β)
    (eq : ∀ (a b : α), r a b → f a = f b) (x : Quot r)
  : p (Quot.lift f eq x) ↔ ∀ y, x = Quot.mk r y → p (f y) := by
  induction x using Quot.ind
  rename α => y
  simpa only using ⟨fun h x h' => lm2 eq h' ▸ h, fun h => h y rfl⟩

def collection (f : ι → ZFSet) : ZFSet :=
  Quot.lift' f (fun f => ⟦PSet.mk ι f⟧) $
  fun a b r => by dsimp; rw [ZFSet.eq]; exact And.intro (fun i => ⟨i, r i⟩) (fun i => ⟨i, r i⟩)

def mem_collection {f : ι → ZFSet} : x ∈ collection f ↔ ∃ i, x = f i := by
  apply Iff.intro
  · intro h
    simp [collection, Quot.lift', Quot.lift_prop (p := fun y => x ∈ y), Quot.move_rec, ZFSet.Mem] at h
    obtain ⟨y, h₁, h₂⟩ := h
    induction x using Quotient.ind
    rename_i x; simp [ZFSet.mk_mem_iff] at h₂
    change x.Mem (.mk ι y) at h₂
    simp [PSet.Mem] at h₂; obtain ⟨z, hz⟩ := h₂
    use z; replace h₁ := h₁ z
    exact (Quot.sound hz).trans h₁.symm
  · intro h
    simp [collection, Quot.lift', Quot.lift_prop' (p := fun y => x ∈ y), Quot.move_rec]
    intro g h; induction x using Quotient.ind
    rename_i x; simp [ZFSet.mk_mem_iff]
    change x.Mem _; simp [PSet.Mem]; obtain ⟨i, hi⟩ := h
    use i; have := Quot.eq.mp (hi.trans (h i))
    rwa [Equivalence.eqvGen_eq Setoid.iseqv] at this

def image (x : ZFSet) (f : ZFSet → ZFSet) : ZFSet := by
  refine Quotient.lift
    (fun ⟨α, g⟩ => collection (fun z => f ⟦g z⟧))
    (fun ⟨α, g⟩ ⟨β, g'⟩ h => ?_) x
  ext z; simp [mem_collection]
  change PSet.Equiv _ _ at h; obtain ⟨h₁, h₂⟩ := h
  apply Iff.intro
  · rintro ⟨w, h'⟩; obtain ⟨w', h₁⟩ := h₁ w
    use w'; exact (show _ = ZFSet.mk (g' w') from Quot.sound h₁) ▸ h'
  · rintro ⟨w', h'⟩; obtain ⟨w, h₁⟩ := h₂ w'
    use w; exact (show ZFSet.mk (g w) = _ from Quot.sound h₁) ▸ h'

def mem_image (x : ZFSet) (f : ZFSet → ZFSet) : y ∈ image x f ↔ ∃ z ∈ x, y = f z := by
  induction x using Quotient.ind; rename_i z
  cases' z with α g
  simp [image, mem_collection, -ZFSet.mk_eq]
  refine Iff.intro (fun ⟨z, h⟩ => ⟨⟦g z⟧, ?_, h⟩) (fun ⟨z, h₁, h₂⟩ => ?_)
  · simp only [ZFSet.mk_eq, ZFSet.mk_mem_iff]
    change PSet.Mem _ _; simp [PSet.Mem]; use z
  · induction z using Quotient.ind; rename_i z
    simp at h₁; change PSet.Mem _ _ at h₁; simp [PSet.Mem] at h₁
    obtain ⟨a, h⟩ := h₁
    use a; exact (show _ = ⟦g a⟧ from Quot.sound h) ▸ h₂

#print axioms mem_image
