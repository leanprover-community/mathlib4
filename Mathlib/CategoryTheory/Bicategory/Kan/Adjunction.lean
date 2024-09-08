/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Kan.HasKan
import Mathlib.CategoryTheory.Bicategory.Adjunction
import Mathlib.Tactic.TFAE

/-!
# Adjunctions as Kan extensions

We show that adjunctions are realized as Kan extensions or Kan lifts.

We also show that a left adjoint commutes with a left Kan extension. Under the assumption that
`IsLeftAdjoint h`, the isomorphism `f⁺ (g ≫ h) ≅ f⁺ g ≫ h` can be accessed by
`Lan.CommuteWith.lanCompIso f g h`.

## References

* [Riehl, *Category theory in context*, Proposition 6.5.2][riehl2017]

## TODO

At the moment, the results are stated for left Kan extensions and left Kan lifts. We can prove the
similar results for right Kan extensions and right Kan lifts.

-/

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

section LeftExtension

open LeftExtension

/-- For an adjuntion `f ⊣ u`, `u` is an absolute left Kan extension of the identity along `f`.
The unit of this Kan extension is given by the unit of the adjunction. -/
def Adjunction.isAbsoluteLeftKan {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u) :
    IsAbsKan (.mk u adj.unit) := fun {x} h ↦
  .mk (fun s  ↦ LeftExtension.homMk
    (𝟙 _ ⊗≫ u ◁ s.unit ⊗≫ adj.counit ▷ s.extension ⊗≫ 𝟙 _ : u ≫ h ⟶ s.extension) <|
      calc _
        _ = 𝟙 _ ⊗≫ (adj.unit ▷ _ ≫ _ ◁ s.unit) ⊗≫ f ◁ adj.counit ▷ s.extension ⊗≫ 𝟙 _ := by
          dsimp only [whisker_extension, StructuredArrow.mk_right, whisker_unit,
            StructuredArrow.mk_hom_eq_self]
          coherence
        _ = 𝟙 _ ⊗≫ s.unit ⊗≫ leftZigzag adj.unit adj.counit ▷ s.extension ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange, leftZigzag]; coherence
        _ = s.unit := by
          rw [adj.left_triangle]; coherence) <| by
    intro s τ₀
    ext
    /- We need to specify the type of `τ` to use the notation `⊗≫`. -/
    let τ : u ≫ h ⟶ s.extension := τ₀.right
    have hτ : adj.unit ▷ h ⊗≫ f ◁ τ = s.unit := by
      rw [← LeftExtension.w τ₀]
      dsimp only [whisker_extension, StructuredArrow.mk_right, whisker_unit,
        StructuredArrow.mk_hom_eq_self]
      coherence
    calc τ
      _ = 𝟙 _ ⊗≫ rightZigzag adj.unit adj.counit ▷ h ⊗≫ τ ⊗≫ 𝟙 _ := by
        rw [adj.right_triangle]; coherence
      _ = 𝟙 _ ⊗≫ u ◁ adj.unit ▷ h ⊗≫ (adj.counit ▷ _ ≫ _ ◁ τ) ⊗≫ 𝟙 _ := by
        rw [rightZigzag]; coherence
      _ = 𝟙 _ ⊗≫ u ◁ (adj.unit ▷ h ⊗≫ f ◁ τ) ⊗≫ adj.counit ▷ s.extension ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; coherence
      _ = _ := by
        rw [hτ]; dsimp

/-- A left Kan extension of the identity along `f` such that `f` commutes with is a right adjoint
to `f`. The unit of this adjoint is given by the unit of the Kan extension. -/
def LeftExtension.IsKan.adjunction {f : a ⟶ b} {t : LeftExtension f (𝟙 a)}
    (H : IsKan t) (H' : IsKan (t.whisker f)) :
      f ⊣ t.extension :=
  let t' := LeftExtension.mk _ <| (λ_ f).hom ≫ (ρ_ f).inv
  let ε : t.extension ≫ f ⟶ 𝟙 b := H'.desc t'
  have Hε := calc leftZigzag t.unit ε = t.unit ▷ f ⊗≫ f ◁ ε := rfl
    _ = (t.unit ▷ f ≫ (α_ _ _ _).hom) ≫ f ◁ H'.desc t' := by coherence
    _ = (λ_ f).hom ≫ (ρ_ f).inv := H'.fac t'
  { unit := t.unit
    counit := ε
    left_triangle := Hε
    right_triangle := by
      apply (cancel_epi (ρ_ _).inv).mp
      apply H.hom_ext
      calc _
        _ = 𝟙 _ ⊗≫ t.unit ⊗≫ f ◁ rightZigzag t.unit ε ⊗≫ 𝟙 _ := by
          coherence
        _ = 𝟙 _ ⊗≫ (t.unit ▷ _ ≫ _ ◁ t.unit) ⊗≫ f ◁ ε ▷ t.extension ⊗≫ 𝟙 _ := by
          rw [rightZigzag]; coherence
        _ = 𝟙 _ ⊗≫ t.unit ⊗≫ (t.unit ▷ f ⊗≫ f ◁ ε) ▷ t.extension ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]; coherence
        _ = _ := by
          rw [← leftZigzag, Hε]; coherence }

/-- For an adjuntion `f ⊣ u`, `u` is a left Kan extension of the identity along `f`.
The unit of this Kan extension is given by the unit of the adjunction. -/
def LeftExtension.IsAbsKan.adjunction {f : a ⟶ b} (t : LeftExtension f (𝟙 a)) (H : IsAbsKan t) :
    f ⊣ t.extension :=
  H.isKan.adjunction (H f)

theorem isLeftAdjoint_TFAE (f : a ⟶ b) :
    List.TFAE [
      IsLeftAdjoint f,
      HasAbsLeftKanExtension f (𝟙 a),
      ∃ _ : HasLeftKanExtension f (𝟙 a), Lan.CommuteWith f (𝟙 a) f] := by
  tfae_have 1 → 2
  · intro h
    exact IsAbsKan.hasAbsLeftKanExtension (Adjunction.ofIsLeftAdjoint f).isAbsoluteLeftKan
  tfae_have 2 → 3
  · intro h
    exact ⟨inferInstance, inferInstance⟩
  tfae_have 3 → 1
  · intro ⟨h, h'⟩
    exact .mk <| (lanIsKan f (𝟙 a)).adjunction <| Lan.CommuteWith.isKan f (𝟙 a) f
  tfae_finish

end LeftExtension

section LeftLift

open LeftLift

/-- For an adjuntion `f ⊣ u`, `f` is an absolute left Kan lift of the identity along `u`.
The unit of this Kan lift is given by the unit of the adjunction. -/
def Adjunction.isAbsoluteLeftKanLift {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u) :
    IsAbsKan (.mk f adj.unit) := fun {x} h ↦
  .mk (fun s ↦ LeftLift.homMk
    (𝟙 _ ⊗≫ s.unit ▷ f ⊗≫ s.lift ◁ adj.counit ⊗≫ 𝟙 _ : h ≫ f ⟶ s.lift) <|
      calc _
      _ = 𝟙 _ ⊗≫ (_ ◁ adj.unit ≫ s.unit ▷ _) ⊗≫ s.lift ◁ adj.counit ▷ u ⊗≫ 𝟙 _ := by
        dsimp only [whisker_lift, StructuredArrow.mk_right, whisker_unit,
          StructuredArrow.mk_hom_eq_self]
        coherence
      _ = s.unit ⊗≫ s.lift ◁ (rightZigzag adj.unit adj.counit) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange, rightZigzag]; coherence
      _ = s.unit := by
        rw [adj.right_triangle]; coherence) <| by
      intro s τ₀
      ext
      /- We need to specify the type of `τ` to use the notation `⊗≫`. -/
      let τ : h ≫ f ⟶ s.lift := τ₀.right
      have hτ : h ◁ adj.unit ⊗≫ τ ▷ u = s.unit := by
        rw [← LeftLift.w τ₀]
        dsimp only [whisker_lift, StructuredArrow.mk_right, whisker_unit,
          StructuredArrow.mk_hom_eq_self]
        coherence
      calc τ
        _ = 𝟙 _ ⊗≫ h ◁ leftZigzag adj.unit adj.counit ⊗≫ τ ⊗≫ 𝟙 _ := by
          rw [adj.left_triangle]; coherence
        _ = 𝟙 _ ⊗≫ h ◁ adj.unit ▷ f ⊗≫ (_ ◁ adj.counit ≫ τ ▷ _) ⊗≫ 𝟙 _ := by
          rw [leftZigzag]; coherence
        _ = 𝟙 _ ⊗≫ (h ◁ adj.unit ⊗≫ τ ▷ u) ▷ f ⊗≫ s.lift ◁ adj.counit ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]; coherence
        _ = _ := by
          rw [hτ]; dsimp

/-- A left Kan lift of the identity along `u` such that `u` commutes with is a left adjoint
to `u`. The unit of this adjoint is given by the unit of the Kan lift. -/
def LeftLift.IsKan.adjunction {u : b ⟶ a} {t : LeftLift u (𝟙 a)}
    (H : IsKan t) (H' : IsKan (t.whisker u)) :
      t.lift ⊣ u :=
  let t' := LeftLift.mk _ <| (ρ_ u).hom ≫ (λ_ u).inv
  let ε : u ≫ t.lift ⟶ 𝟙 b := H'.desc t'
  have Hε := calc
    rightZigzag t.unit ε = (u ◁ t.unit ≫ (α_ _ _ _).inv) ≫ H'.desc t' ▷ u := by
      dsimp only [rightZigzag]; coherence
    _ = (ρ_ u).hom ≫ (λ_ u).inv := H'.fac t'
  { unit := t.unit
    counit := ε
    left_triangle := by
      apply (cancel_epi (λ_ _).inv).mp
      apply H.hom_ext
      calc _
        _ = 𝟙 _ ⊗≫ t.unit ⊗≫ leftZigzag t.unit ε ▷ u ⊗≫ 𝟙 _ := by
          coherence
        _ = 𝟙 _ ⊗≫ (_ ◁ t.unit ≫ t.unit ▷ _) ⊗≫ t.lift ◁ ε ▷ u ⊗≫ 𝟙 _ := by
          rw [leftZigzag]; coherence
        _ = 𝟙 _ ⊗≫ t.unit ⊗≫ t.lift ◁ (u ◁ t.unit ⊗≫ ε ▷ u) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]; coherence
        _ = _ := by
          rw [← rightZigzag, Hε]; coherence
    right_triangle := Hε }

/-- For an adjuntion `f ⊣ u`, `f` is a left Kan lift of the identity along `u`.
The unit of this Kan lift is given by the unit of the adjunction. -/
def LeftLift.IsAbsKan.adjunction {u : b ⟶ a} (t : LeftLift u (𝟙 a)) (H : IsAbsKan t) :
    t.lift ⊣ u :=
  H.isKan.adjunction (H u)

theorem isRightAdjoint_TFAE (u : b ⟶ a) :
    List.TFAE [
      IsRightAdjoint u,
      HasAbsLeftKanLift u (𝟙 a),
      ∃ _ : HasLeftKanLift u (𝟙 a), LanLift.CommuteWith u (𝟙 a) u] := by
  tfae_have 1 → 2
  · intro h
    exact IsAbsKan.hasAbsLeftKanLift (Adjunction.ofIsRightAdjoint u).isAbsoluteLeftKanLift
  tfae_have 2 → 3
  · intro h
    exact ⟨inferInstance, inferInstance⟩
  tfae_have 3 → 1
  · intro ⟨h, h'⟩
    exact .mk <| (lanLiftIsKan u (𝟙 a)).adjunction <| LanLift.CommuteWith.isKan u (𝟙 a) u
  tfae_finish

end LeftLift

namespace LeftExtension

/-- A left adjoint commutes with a left Kan extension. -/
def isKanOfWhiskerLeftAdjoint
    {f : a ⟶ b} {g : a ⟶ c} {t : LeftExtension f g} (H : LeftExtension.IsKan t)
      {x : B} {h : c ⟶ x} {u : x ⟶ c} (adj : h ⊣ u) :
        LeftExtension.IsKan (t.whisker h) :=
  let η' := adj.unit
  let H' : LeftLift.IsAbsKan (.mk _ η') := adj.isAbsoluteLeftKanLift
  .mk (fun s ↦
    let k := s.extension
    let θ := s.unit
    let τ : t.extension ⟶ k ≫ u := H.desc (.mk _ <| 𝟙 _ ⊗≫ g ◁ η' ⊗≫ θ ▷ u ⊗≫ 𝟙 _)
    let σ : t.extension ≫ h ⟶ k := H'.desc <| (.mk _ <| (ρ_ _).hom ≫ τ)
    LeftExtension.homMk σ <| (H' g).hom_ext <| by
      have Hσ := calc
        t.extension ◁ η' ⊗≫ σ ▷ u
        _ = (t.extension ◁ η' ≫ (α_ _ _ _).inv) ≫ (H' t.extension).desc (LeftLift.mk k _) ▷ u := by
          coherence
        _ = (ρ_ t.extension).hom ≫ τ := (H' _).fac (.mk _ <| (ρ_ _).hom ≫ τ)
        _ = 𝟙 _ ⊗≫ τ := by coherence
      calc _
        _ = 𝟙 _ ⊗≫ (g ◁ η' ≫ t.unit ▷ (h ≫ u)) ⊗≫ f ◁ σ ▷ u ⊗≫ 𝟙 _ := by
          dsimp only [LeftLift.whisker_lift, StructuredArrow.mk_right, LeftLift.whisker_unit,
            StructuredArrow.mk_hom_eq_self, whisker_extension, whisker_unit]
          coherence
        _ = 𝟙 _ ⊗≫ t.unit ▷ (𝟙 c) ⊗≫ f ◁ (t.extension ◁ η' ⊗≫ σ ▷ u) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]; coherence
        _ = _ := by
          rw [Hσ]; simp [τ, bicategoricalComp, BicategoricalCoherence.hom]) <| by
    intro s' τ₀'
    let τ' : t.extension ≫ h ⟶ s'.extension := τ₀'.right
    have Hτ' : t.unit ▷ h ⊗≫ f ◁ τ' = s'.unit := by
      simpa [bicategoricalComp, BicategoricalCoherence.hom] using τ₀'.w.symm
    ext
    apply (H' _).hom_ext
    dsimp only [StructuredArrow.homMk_right]
    rw [(H' _).fac]
    apply (cancel_epi (ρ_ _).inv).mp
    apply H.hom_ext
    calc _
      _ = 𝟙 _ ⊗≫ (t.unit ▷ (𝟙 c) ≫ (f ≫ t.extension) ◁ η') ⊗≫ f ◁ τ' ▷ u := by
        dsimp only [LeftLift.whisker_lift, StructuredArrow.mk_right, LeftLift.whisker_unit,
          StructuredArrow.mk_hom_eq_self]
        coherence
      _ = 𝟙 g ⊗≫ g ◁ η' ⊗≫ (t.unit ▷ h ⊗≫ f ◁ τ') ▷ u ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; coherence
      _ = _ := by
        rw [Hτ']; simp

instance {f : a ⟶ b} {g : a ⟶ c} {x : B} {h : c ⟶ x} [IsLeftAdjoint h] [HasLeftKanExtension f g] :
    Lan.CommuteWith f g h :=
  ⟨⟨isKanOfWhiskerLeftAdjoint (lanIsKan f g) (Adjunction.ofIsLeftAdjoint h)⟩⟩

end LeftExtension

end Bicategory

end CategoryTheory
