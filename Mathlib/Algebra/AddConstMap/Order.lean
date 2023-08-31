import Mathlib.Algebra.AddConstMap.Basic
import Mathlib.Algebra.Bounds
import Mathlib.Algebra.Order.LatticeGroup

open Set AddConstMapClass
namespace AddConstMap

section Order

variable [Add G] [Add H]

instance (priority := low) [LE H] : LE (G →+c[a, b] H) where
  le f g := (f : G → H) ≤ g

@[simp, norm_cast]
theorem coe_le_coe [LE H] {f g : G →+c[a, b] H} : ⇑f ≤ ⇑g ↔ f ≤ g := Iff.rfl

instance (priority := low) [Preorder H] : Preorder (G →+c[a, b] H) :=
  Preorder.lift FunLike.coe

theorem coe_mono [Preorder H] : Monotone ((↑) : (G →+c[a, b] H) → (G → H)) := fun _ _ ↦ id

instance (priority := low) [PartialOrder H] : PartialOrder (G →+c[a, b] H) :=
  PartialOrder.lift FunLike.coe FunLike.coe_injective

end Order

section AddCommGroupLattice

variable {G H : Type _} [Add G] [AddCommGroup H] [Lattice H] [CovariantClass H H (· + ·) (· ≤ ·)]
  {a : G} {b : H}

instance : Sup (G →+c[a, b] H) where
  sup f g := ⟨⇑f ⊔ g, fun x ↦ by simp [sup_add]⟩

@[simp] theorem coe_sup (f g : G →+c[a, b] H) : ⇑(f ⊔ g) = ⇑f ⊔ g := rfl
theorem sup_apply (f g : G →+c[a, b] H) (x : G) : (f ⊔ g) x = f x ⊔ g x := rfl

instance : Inf (G →+c[a, b] H) where
  inf f g := ⟨⇑f ⊓ g, fun x ↦ by simp [inf_add]⟩

@[simp] theorem coe_inf (f g : G →+c[a, b] H) : ⇑(f ⊓ g) = ⇑f ⊓ g := rfl
theorem inf_apply (f g : G →+c[a, b] H) (x : G) : (f ⊓ g) x = f x ⊓ g x := rfl

protected instance lattice : Lattice (G →+c[a, b] H) :=
  FunLike.coe_injective.lattice _ coe_sup coe_inf

end AddCommGroupLattice

section ConditionallyCompleteLinearOrder

variable {G H : Type _} [Add G] [AddCommGroup H] [ConditionallyCompleteLattice H]
  [CovariantClass H H (· + ·) (· ≤ ·)] {a : G} {b : H} [Inhabited (G →+c[a, b] H)]

open scoped Classical in
protected noncomputable instance supSet : SupSet (G →+c[a, b] H) where
  sSup s := if hs : s.Nonempty ∧ BddAbove s
    then ⟨⨆ f : s, ⇑f.1, fun x ↦ by
      simp only [iSup_apply, map_add_const]
      have := hs.1.to_subtype
      refine (ciSup_add ?_ _).symm
      rw [← image_eq_range fun f : G →+c[a, b] H ↦ f x]
      refine Monotone.map_bddAbove (fun _ _ h ↦ ?_) hs.2
      exact h x⟩
    else default

theorem coe_sSup {s : Set (G →+c[a, b] H)} (hne : s.Nonempty) (hbdd : BddAbove s) :
    ⇑(sSup s) = ⨆ f : s, ⇑f.1 := by
  simp only [AddConstMap.supSet, dif_pos (And.intro hne hbdd), coe_mk]

protected theorem isLUB_sSup {s : Set (G →+c[a, b] H)} (hne : s.Nonempty) (hbdd : BddAbove s) :
    IsLUB s (sSup s) :=
  .of_image (f := FunLike.coe) coe_le_coe <| by
    rw [coe_sSup hne hbdd]
    exact isLUB_ciSup_set (coe_mono.map_bddAbove hbdd) hne

theorem coe_iSup [Nonempty ι] {f : ι → G →+c[a, b] H} (hf : BddAbove (range f)) :
    ⇑(⨆ i, f i) = ⨆ i, ⇑(f i) := by
  rw [iSup, coe_sSup (range_nonempty f) hf, iSup_range']

protected theorem sSup_apply {s : Set (G →+c[a, b] H)} (hne : s.Nonempty) (hbdd : BddAbove s)
    (x : G) : sSup s x = ⨆ f : s, f.1 x := by
  rw [coe_sSup hne hbdd, iSup_apply]

protected theorem iSup_apply [Nonempty ι] {f : ι → G →+c[a, b] H}
    (hf : BddAbove (range f)) (x : G) : (⨆ i, f i) x = ⨆ i, f i x := by
  rw [coe_iSup hf, iSup_apply]

protected noncomputable instance infSet : InfSet (G →+c[a, b] H) :=
  letI : Inhabited (G →+c[a, b] Hᵒᵈ) := ‹_›; OrderDual.infSet (G →+c[a, b] Hᵒᵈ)

theorem coe_sInf {s : Set (G →+c[a, b] H)} (hne : s.Nonempty) (hbdd : BddBelow s) :
    ⇑(sInf s) = ⨅ f : s, ⇑f.1 :=
  letI : Inhabited (G →+c[a, b] Hᵒᵈ) := ‹_›; coe_sSup (H := Hᵒᵈ) hne hbdd

protected theorem isGLB_sInf {s : Set (G →+c[a, b] H)} (hne : s.Nonempty) (hbdd : BddBelow s) :
    IsGLB s (sInf s) :=
  letI : Inhabited (G →+c[a, b] Hᵒᵈ) := ‹_›; AddConstMap.isLUB_sSup (H := Hᵒᵈ) hne hbdd

theorem coe_iInf [Nonempty ι] {f : ι → G →+c[a, b] H} (hf : BddBelow (range f)) :
    ⇑(⨅ i, f i) = ⨅ i, ⇑(f i) := by
  rw [iInf, coe_sInf (range_nonempty f) hf, iInf_range']

protected theorem sInf_apply {s : Set (G →+c[a, b] H)} (hne : s.Nonempty) (hbdd : BddBelow s)
    (x : G) : sInf s x = ⨅ f : s, f.1 x := by
  rw [coe_sInf hne hbdd, iInf_apply]

protected theorem iInf_apply [Nonempty ι] {f : ι → G →+c[a, b] H}
    (hf : BddBelow (range f)) (x : G) : (⨅ i, f i) x = ⨅ i, f i x := by
  rw [coe_iInf hf, iInf_apply]

noncomputable instance : ConditionallyCompleteLattice (G →+c[a, b] H) where
  __ := AddConstMap.lattice
  le_csSup _s f hs hf := (AddConstMap.isLUB_sSup ⟨f, hf⟩ hs).1 hf
  csSup_le _s f hs hf := (AddConstMap.isLUB_sSup hs ⟨f, hf⟩).2 hf
  csInf_le _s f hs hf := (AddConstMap.isGLB_sInf ⟨f, hf⟩ hs).1 hf
  le_csInf _s f hs hf := (AddConstMap.isGLB_sInf hs ⟨f, hf⟩).2 hf
  
end ConditionallyCompleteLinearOrder

end AddConstMap
