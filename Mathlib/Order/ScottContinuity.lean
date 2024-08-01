/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.Bounds.Lattice

/-!
# Scott continuity
-/

open Set

variable {α β : Type*}

section ScottContinuous
variable [Preorder α] [Preorder β] {D D₁ D₂ : Set (Set α)} {E : Set (Set β)}
  {f : α → β} {a : α}

/-- A function between preorders is said to be Scott continuous on a set `D` of directed sets if it
preserves `IsLUB` on elements of `D`.

The dual notion

```lean
∀ ⦃d : Set α⦄, d ∈ D →  d.Nonempty → DirectedOn (· ≥ ·) d → ∀ ⦃a⦄, IsGLB d a → IsGLB (f '' d) (f a)
```

does not appear to play a significant role in the literature, so is omitted here.
-/
def ScottContinuousOn (D : Set (Set α)) (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)

lemma ScottContinuousOn.mono (hD : D₁ ⊆ D₂) (hf : ScottContinuousOn D₂ f) :
    ScottContinuousOn D₁ f := fun _  hdD₁ hd₁ hd₂ _ hda => hf (hD hdD₁) hd₁ hd₂ hda

protected theorem ScottContinuousOn.monotone (D : Set (Set α)) (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
    (h : ScottContinuousOn D f) : Monotone f := by
  refine fun a b hab =>
    (h (hD a b hab) (insert_nonempty _ _) (directedOn_pair le_refl hab) ?_).1
      (mem_image_of_mem _ <| mem_insert _ _)
  rw [IsLUB, upperBounds_insert, upperBounds_singleton,
    inter_eq_self_of_subset_right (Ici_subset_Ici.2 hab)]
  exact isLeast_Ici

@[simp] lemma ScottContinuousOn.id : ScottContinuousOn D (id : α → α) := by simp [ScottContinuousOn]

variable {g : α → β}

lemma ScottContinuousOn.prodMk (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
    (hf : ScottContinuousOn D f) (hg : ScottContinuousOn D g) :
    ScottContinuousOn D fun x => (f x, g x) := fun d hd₁ hd₂ hd₃ a hda => by
  rw [IsLUB, IsLeast, upperBounds]
  constructor
  · simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq,
    Prod.mk_le_mk]
    intro b hb
    exact ⟨hf.monotone D hD (hda.1 hb), hg.monotone D hD (hda.1 hb)⟩
  · intro ⟨p₁, p₂⟩ hp
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq,
      Prod.mk_le_mk] at hp
    constructor
    · rw [isLUB_le_iff (hf hd₁ hd₂ hd₃ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq]
      intro _ hb
      exact (hp _ hb).1
    · rw [isLUB_le_iff (hg hd₁ hd₂ hd₃ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq]
      intro _ hb
      exact (hp _ hb).2

/-- A function between preorders is said to be Scott continuous if it preserves `IsLUB` on directed
sets. It can be shown that a function is Scott continuous if and only if it is continuous wrt the
Scott topology.
-/
def ScottContinuous (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)

@[simp] lemma scottContinuousOn_univ : ScottContinuousOn univ f ↔ ScottContinuous f := by
  simp [ScottContinuousOn, ScottContinuous]

lemma ScottContinuous.scottContinuousOn {D : Set (Set α)} :
    ScottContinuous f → ScottContinuousOn D f := fun h _ _ d₂ d₃ _ hda => h d₂ d₃ hda

protected theorem ScottContinuous.monotone (h : ScottContinuous f) : Monotone f :=
  h.scottContinuousOn.monotone univ (fun _ _ _ ↦ trivial)

@[simp] lemma ScottContinuous.id : ScottContinuous (id : α → α) := by simp [ScottContinuous]

end ScottContinuous

section Products

variable {γ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ]

lemma monotone {f : α × β → γ} (h₁ : ∀ b, Monotone (fun a => f (a,b)))
    (h₂ : ∀ a, Monotone (fun b => f (a,b))) : Monotone f := fun _ _ hab =>
  le_trans (h₁ _ (Prod.mk_le_mk.mp hab).1) (h₂ _ (Prod.mk_le_mk.mp hab).2)

-- c.f. isLUB_prod
-- theorem isLUB_prod {s : Set (α × β)} (p : α × β) :
--    IsLUB s p ↔ IsLUB (Prod.fst '' s) p.1 ∧ IsLUB (Prod.snd '' s) p.2 := by

lemma d1 {d : Set (α × β)} (hd : DirectedOn (· ≤ ·) d) : DirectedOn (· ≤ ·) (Prod.fst '' d) := by
  intro a ⟨p,hp⟩ b ⟨q,hq⟩
  obtain ⟨r,hr⟩ := hd p hp.1 q hq.1
  aesop

lemma d2 {d : Set (α × β)} (hd : DirectedOn (· ≤ ·) d) : DirectedOn (· ≤ ·) (Prod.snd '' d) := by
  intro a ⟨p,hp⟩ b ⟨q,hq⟩
  obtain ⟨r,hr⟩ := hd p hp.1 q hq.1
  aesop

  --obtain z := hd (a,b)

lemma Prod.upperBounds {f : α × β → γ} (hf : Monotone f)
    {d : Set (α × β)} (hd : DirectedOn (· ≤ ·) d) :
    upperBounds (f '' d) = upperBounds (f '' (Prod.fst '' d) ×ˢ (Prod.snd '' d)) := by
  apply le_antisymm
  · intro u hu
    rw [mem_upperBounds]
    intro c hc
    simp at hc
    cases' hc with a₁ ha
    cases' ha with b₁ hab
    obtain ⟨⟨⟨b₂,hb₂⟩,⟨a₂,ha₂⟩⟩, right⟩ := hab
    obtain ⟨⟨a₃,b₃⟩,hm⟩ := hd _ hb₂ _ ha₂
    have e1 : (a₁,b₁) ≤ (a₃,b₃) := by
      aesop
    rw [← right]
    apply le_trans (hf e1)
    rw [mem_upperBounds] at hu
    apply hu
    use (a₃, b₃)
    exact And.imp_right (fun _ ↦ rfl) hm
  · apply upperBounds_mono_set
    apply image_mono
    intro _ _
    aesop

lemma Prod.IsLub {f : α × β → γ} (hf : Monotone f)
    {d : Set (α × β)} (hd : DirectedOn (· ≤ ·) d) (u : γ) :
    IsLUB (f '' d) u ↔ IsLUB (f '' (Prod.fst '' d) ×ˢ (Prod.snd '' d)) u := by
  rw [IsLUB, Prod.upperBounds hf hd, ← IsLUB]


lemma step1 {f : α × β → γ} {d : Set (α × β)} (hd₁ : (Prod.fst '' d).Nonempty)
    (hd₂ : DirectedOn (· ≤ ·) (Prod.fst '' d)) {p₁ : α} {p₂ : β} (h : IsLUB d (p₁,p₂))
    (h₁ : ∀ b, ScottContinuous (fun a => f (a,b))) {b : β} :
    IsLUB (f '' (Prod.fst '' d) ×ˢ {b}) (f (p₁,b)) := by
  simp only [prod_singleton]
  have e1 : IsLUB (Prod.fst '' d) p₁ := ((isLUB_prod (p₁,p₂)).mp h).1
  have e3 {S : Set α} : f '' ((fun a ↦ (a, b)) '' S) = (fun a ↦ f (a, b)) '' S := by
    exact image_image f (fun a ↦ (a, b)) S
  rw [e3]
  exact h₁ b hd₁ hd₂ e1

lemma step1' {f : α × β → γ} {d : Set (α × β)} (hd₁ : (Prod.snd '' d).Nonempty)
    (hd₂ : DirectedOn (· ≤ ·) (Prod.snd '' d)) {p₁ : α} {p₂ : β} (h : IsLUB d (p₁,p₂))
    (h₁ : ∀ a, ScottContinuous (fun b => f (a,b))) {a : α} :
    IsLUB (f '' {a} ×ˢ (Prod.snd '' d)) (f (a,p₂)) := by
  simp only [singleton_prod]
  have e1 : IsLUB (Prod.snd '' d) p₂ := ((isLUB_prod (p₁,p₂)).mp h).2
  have e3 {S : Set β} : f '' ((fun b ↦ (a, b)) '' S) = (fun b ↦ f (a, b)) '' S := by
    exact image_image f (fun b ↦ (a, b)) S
  rw [e3]
  exact h₁ a hd₁ hd₂ e1


lemma test {f : α × β → γ} {d : Set (α × β)} (hd₁ : d.Nonempty)
    (hd₂ : DirectedOn (· ≤ ·) d) {p₁ : α} {p₂ : β} (h : IsLUB d (p₁,p₂))
    (h₁ : ∀ a, ScottContinuous (fun b => f (a,b))) (h₂ : ∀ b, ScottContinuous (fun a => f (a,b))) :
    IsLUB (f '' d) (f (p₁,p₂)) := by
  have e1 : IsLUB (Prod.fst '' d) p₁ := ((isLUB_prod (p₁,p₂)).mp h).1
  rw [Prod.IsLub (monotone (fun a => (h₂ a).monotone) (fun a => (h₁ a).monotone)) hd₂]
  rw [← iUnion_of_singleton_coe (Prod.fst '' d), iUnion_prod_const, image_iUnion]
  apply IsLUB.iUnion
  apply fun a => step1' (Nonempty.image Prod.snd hd₁) (d2 hd₂) h h₁
  have e2 : IsLUB ((fun a ↦ f (a, p₂)) '' (Prod.fst '' d)) (f (p₁,p₂)) :=
    h₂ p₂ (Nonempty.image Prod.fst hd₁) (d1 hd₂) e1
  rw [Set.range]
  rw [Set.image] at e2
  aesop



/-
lemma testprod {S : Set α} {T : Set β} {u : S → α × β} (v : α × β)
    (hS : ∀ (s : S), IsLUB ({↑s} ×ˢ T) (u s)) (h : IsLUB {u s | (s : S)} v) :
    IsLUB (S ×ˢ T) v := sorry

lemma testprod' {S : Set α} {T : Set β} {u : S → γ} {f : α × β → γ} (v : γ)
    (hS : ∀ (s : S), IsLUB (f '' ({↑s} ×ˢ T)) (u s)) (h : IsLUB (Set.range u) v) :
    IsLUB (f '' (S ×ˢ T)) v := sorry

lemma testprod'' {S : Set α} {T : Set β} {u : T → γ} {f : α × β → γ} (v : γ)
    (hT : ∀ (t : T), IsLUB (f '' (S ×ˢ {↑t})) (u t)) (h : IsLUB (u '' univ) v) :
    IsLUB (f '' (S ×ˢ T)) v := sorry


lemma test2 {f : α × β → γ} {d : Set (α × β)} (hd₁ : (Prod.fst '' d).Nonempty)
    (hd₂ : DirectedOn (· ≤ ·) (Prod.fst '' d)) {p₁ : α} {p₂ : β} (h : IsLUB d (p₁,p₂))
    (h₁ : ∀ b, ScottContinuous (fun a => f (a,b))) (h₂ : ∀ a, ScottContinuous (fun b => f (a,b))) :
    IsLUB (f '' (Prod.fst '' d) ×ˢ (Prod.snd '' d)) (f (p₁,p₂)) := by
  have e1 : IsLUB (Prod.fst '' d) p₁ := ((isLUB_prod (p₁,p₂)).mp h).1
  have e2 : IsLUB (Prod.snd '' d) p₂ := ((isLUB_prod (p₁,p₂)).mp h).2
  --apply testprod' (u := fun a => f (a, p₂)) (v := (f (p₁,p₂))) (S := Prod.fst '' d)
   (T := Prod.snd '' d) _ _

  --apply testprod'' (u := fun b => f (p₁, b)) (v := (f (p₁,p₂))) (S := Prod.fst '' d)
    T := Prod.snd '' d)
  intro a
  apply step1 hd₁ hd₂
  apply (h₂ p₁)
  --apply test hd₁ hd₂ h h₁
-/

lemma stepn {f : α × β → γ} {d : Set (α × β)} {p₁ : α} {p₂ : β} (hf : Monotone f)
    (hd : DirectedOn (· ≤ ·) d) (h : IsLUB (f '' (Prod.fst '' d) ×ˢ (Prod.snd '' d)) (f (p₁,p₂))) :
    IsLUB (f '' d) (f (p₁,p₂)) := by
  exact (Prod.IsLub hf hd (f (p₁, p₂))).mpr h









/-
lemma Prod.ScottContinuous {f : α × β → γ} (h₁ : ∀ b, ScottContinuous (fun a => f (a,b)))
    (h₂ : ∀ a, ScottContinuous (fun b => f (a,b))) : ScottContinuous f := by
    intro d hd₁ hd₂ p hdp
    rw [Prod.IsLub (monotone (fun b ↦ ScottContinuous.monotone (h₁ b))
      (fun a ↦ ScottContinuous.monotone (h₂ a)))]
    rw [isLUB_prod] at hdp

  --rw [ScottContinuous]
-/

end Products

section SemilatticeSup

variable [Preorder α] [SemilatticeSup β]

lemma ScottContinuousOn.sup₂ {D : Set (Set (β × β))} :
    ScottContinuousOn D fun (a, b) => (a ⊔ b : β) := by
  simp only
  intro d _ _ _ ⟨p₁, p₂⟩ hdp
  rw [IsLUB, IsLeast, upperBounds] at hdp
  simp only [Prod.forall, mem_setOf_eq, Prod.mk_le_mk] at hdp
  rw [IsLUB, IsLeast, upperBounds]
  constructor
  · simp only [mem_image, Prod.exists, forall_exists_index, and_imp, mem_setOf_eq]
    intro a b₁ b₂ hbd hba
    rw [← hba]
    exact sup_le_sup (hdp.1 _ _ hbd).1 (hdp.1 _ _ hbd).2
  · simp only [mem_image, Prod.exists, forall_exists_index, and_imp]
    intro b hb
    simp only [sup_le_iff]
    have e1 : (p₁, p₂) ∈ lowerBounds {x | ∀ (b₁ b₂ : β), (b₁, b₂) ∈ d → (b₁, b₂) ≤ x} := hdp.2
    rw [lowerBounds] at e1
    simp only [mem_setOf_eq, Prod.forall, Prod.mk_le_mk] at e1
    apply e1
    intro b₁ b₂ hb'
    exact sup_le_iff.mp (hb b₁ b₂ hb' rfl)

end SemilatticeSup
