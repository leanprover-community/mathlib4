/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Kan.HasKan
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.Data.List.TFAE
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.TFAE
import Mathlib.Util.CompileInductive

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

@[expose] public section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

section LeftExtension

open LeftExtension

/-- For an adjunction `f ⊣ u`, `u` is an absolute left Kan extension of the identity along `f`.
The unit of this Kan extension is given by the unit of the adjunction. -/
def Adjunction.isAbsoluteLeftKan {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u) :
    IsAbsKan (.mk u adj.unit) := fun {x} h ↦
  .mk (fun s  ↦ LeftExtension.homMk
    (𝟙 _ ⊗≫ u ◁ s.unit ⊗≫ adj.counit ▷ s.extension ⊗≫ 𝟙 _ : u ≫ h ⟶ s.extension) <|
      calc _
        _ = 𝟙 _ ⊗≫ (adj.unit ▷ _ ≫ _ ◁ s.unit) ⊗≫ f ◁ adj.counit ▷ s.extension ⊗≫ 𝟙 _ := by
          dsimp only [whisker_extension, StructuredArrow.mk_right, whisker_unit,
            StructuredArrow.mk_hom_eq_self]
          bicategory
        _ = 𝟙 _ ⊗≫ s.unit ⊗≫ leftZigzag adj.unit adj.counit ▷ s.extension ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]; bicategory
        _ = s.unit := by
          rw [adj.left_triangle]; bicategory) <| by
    intro s τ₀
    ext
    /- We need to specify the type of `τ` to use the notation `⊗≫`. -/
    let τ : u ≫ h ⟶ s.extension := τ₀.right
    have hτ : adj.unit ▷ h ⊗≫ f ◁ τ = s.unit := by
      simpa [bicategoricalComp] using LeftExtension.w τ₀
    calc τ
      _ = 𝟙 _ ⊗≫ rightZigzag adj.unit adj.counit ▷ h ⊗≫ τ ⊗≫ 𝟙 _ := by
        rw [adj.right_triangle]; bicategory
      _ = 𝟙 _ ⊗≫ u ◁ adj.unit ▷ h ⊗≫ (adj.counit ▷ _ ≫ _ ◁ τ) ⊗≫ 𝟙 _ := by
        rw [rightZigzag]; bicategory
      _ = 𝟙 _ ⊗≫ u ◁ (adj.unit ▷ h ⊗≫ f ◁ τ) ⊗≫ adj.counit ▷ s.extension ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
      _ = _ := by
        rw [hτ]; dsimp only [StructuredArrow.homMk_right]

/-- A left Kan extension `t` of the identity along `f` that commutes with `f`, in the sense that
`t.whisker f` is a left Kan extension, is a right adjoint to `f`. The unit of this adjoint is
given by the unit of the Kan extension. -/
def LeftExtension.IsKan.adjunction {f : a ⟶ b} {t : LeftExtension f (𝟙 a)}
    (H : IsKan t) (H' : IsKan (t.whisker f)) :
      f ⊣ t.extension :=
  let ε : t.extension ≫ f ⟶ 𝟙 b := H'.desc <| .mk _ <| (λ_ f).hom ≫ (ρ_ f).inv
  have Hε : leftZigzag t.unit ε = (λ_ f).hom ≫ (ρ_ f).inv := by
    simpa [leftZigzag, bicategoricalComp] using H'.fac <| .mk _ <| (λ_ f).hom ≫ (ρ_ f).inv
  { unit := t.unit
    counit := ε
    left_triangle := Hε
    right_triangle := by
      apply (cancel_epi (ρ_ _).inv).mp
      apply H.hom_ext
      calc _
        _ = 𝟙 _ ⊗≫ t.unit ⊗≫ f ◁ rightZigzag t.unit ε ⊗≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ ⊗≫ (t.unit ▷ _ ≫ _ ◁ t.unit) ⊗≫ f ◁ ε ▷ t.extension ⊗≫ 𝟙 _ := by
          rw [rightZigzag]; bicategory
        _ = 𝟙 _ ⊗≫ t.unit ⊗≫ (t.unit ▷ f ⊗≫ f ◁ ε) ▷ t.extension ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]; bicategory
        _ = _ := by
          rw [← leftZigzag, Hε]; bicategory }

/-- An absolute left Kan extension of the identity along `f` is a right adjoint to `f`.
The unit of this adjunction is given by the unit of the Kan extension. -/
def LeftExtension.IsAbsKan.adjunction {f : a ⟶ b} (t : LeftExtension f (𝟙 a)) (H : IsAbsKan t) :
    f ⊣ t.extension :=
  H.isKan.adjunction (H f)

theorem isLeftAdjoint_TFAE (f : a ⟶ b) :
    List.TFAE [
      IsLeftAdjoint f,
      HasAbsLeftKanExtension f (𝟙 a),
      ∃ _ : HasLeftKanExtension f (𝟙 a), Lan.CommuteWith f (𝟙 a) f] := by
  tfae_have 1 → 2
  | h => IsAbsKan.hasAbsLeftKanExtension (Adjunction.ofIsLeftAdjoint f).isAbsoluteLeftKan
  tfae_have 2 → 3
  | h => ⟨inferInstance, inferInstance⟩
  tfae_have 3 → 1
  | ⟨h, h'⟩ => .mk <| (lanIsKan f (𝟙 a)).adjunction <| Lan.CommuteWith.isKan f (𝟙 a) f
  tfae_finish

end LeftExtension

section LeftLift

open LeftLift

/-- For an adjunction `f ⊣ u`, `f` is an absolute left Kan lift of the identity along `u`.
The unit of this Kan lift is given by the unit of the adjunction. -/
def Adjunction.isAbsoluteLeftKanLift {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u) :
    IsAbsKan (.mk f adj.unit) := fun {x} h ↦
  .mk (fun s ↦ LeftLift.homMk
    (𝟙 _ ⊗≫ s.unit ▷ f ⊗≫ s.lift ◁ adj.counit ⊗≫ 𝟙 _ : h ≫ f ⟶ s.lift) <|
      calc _
      _ = 𝟙 _ ⊗≫ (_ ◁ adj.unit ≫ s.unit ▷ _) ⊗≫ s.lift ◁ adj.counit ▷ u ⊗≫ 𝟙 _ := by
        dsimp only [whisker_lift, StructuredArrow.mk_right, whisker_unit,
          StructuredArrow.mk_hom_eq_self]
        bicategory
      _ = s.unit ⊗≫ s.lift ◁ (rightZigzag adj.unit adj.counit) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange, rightZigzag]; bicategory
      _ = s.unit := by
        rw [adj.right_triangle]; bicategory) <| by
      intro s τ₀
      ext
      /- We need to specify the type of `τ` to use the notation `⊗≫`. -/
      let τ : h ≫ f ⟶ s.lift := τ₀.right
      have hτ : h ◁ adj.unit ⊗≫ τ ▷ u = s.unit := by simpa [bicategoricalComp] using LeftLift.w τ₀
      calc τ
        _ = 𝟙 _ ⊗≫ h ◁ leftZigzag adj.unit adj.counit ⊗≫ τ ⊗≫ 𝟙 _ := by
          rw [adj.left_triangle]; bicategory
        _ = 𝟙 _ ⊗≫ h ◁ adj.unit ▷ f ⊗≫ (_ ◁ adj.counit ≫ τ ▷ _) ⊗≫ 𝟙 _ := by
          rw [leftZigzag]; bicategory
        _ = 𝟙 _ ⊗≫ (h ◁ adj.unit ⊗≫ τ ▷ u) ▷ f ⊗≫ s.lift ◁ adj.counit ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]; bicategory
        _ = _ := by
          rw [hτ]; dsimp only [StructuredArrow.homMk_right]

/-- A left Kan lift `t` of the identity along `u` that commutes with `u`, in the sense that
`t.whisker u` is a left Kan lift, is a left adjoint to `u`. The unit of this adjoint is given by
the unit of the Kan lift. -/
def LeftLift.IsKan.adjunction {u : b ⟶ a} {t : LeftLift u (𝟙 a)}
    (H : IsKan t) (H' : IsKan (t.whisker u)) :
      t.lift ⊣ u :=
  let ε : u ≫ t.lift ⟶ 𝟙 b := H'.desc <| .mk _ <| (ρ_ u).hom ≫ (λ_ u).inv
  have Hε : rightZigzag t.unit ε = (ρ_ u).hom ≫ (λ_ u).inv := by
    simpa [rightZigzag, bicategoricalComp] using H'.fac <| .mk _ <| (ρ_ u).hom ≫ (λ_ u).inv
  { unit := t.unit
    counit := ε
    left_triangle := by
      apply (cancel_epi (λ_ _).inv).mp
      apply H.hom_ext
      calc _
        _ = 𝟙 _ ⊗≫ t.unit ⊗≫ leftZigzag t.unit ε ▷ u ⊗≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ ⊗≫ (_ ◁ t.unit ≫ t.unit ▷ _) ⊗≫ t.lift ◁ ε ▷ u ⊗≫ 𝟙 _ := by
          rw [leftZigzag]; bicategory
        _ = 𝟙 _ ⊗≫ t.unit ⊗≫ t.lift ◁ (u ◁ t.unit ⊗≫ ε ▷ u) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]; bicategory
        _ = _ := by
          rw [← rightZigzag, Hε]; bicategory
    right_triangle := Hε }

/-- An absolute left Kan lift of the identity along `u` is a left adjoint to `u`.
The unit of this adjunction is given by the unit of the Kan lift. -/
def LeftLift.IsAbsKan.adjunction {u : b ⟶ a} (t : LeftLift u (𝟙 a)) (H : IsAbsKan t) :
    t.lift ⊣ u :=
  H.isKan.adjunction (H u)

theorem isRightAdjoint_TFAE (u : b ⟶ a) :
    List.TFAE [
      IsRightAdjoint u,
      HasAbsLeftKanLift u (𝟙 a),
      ∃ _ : HasLeftKanLift u (𝟙 a), LanLift.CommuteWith u (𝟙 a) u] := by
  tfae_have 1 → 2
  | h => IsAbsKan.hasAbsLeftKanLift (Adjunction.ofIsRightAdjoint u).isAbsoluteLeftKanLift
  tfae_have 2 → 3
  | h => ⟨inferInstance, inferInstance⟩
  tfae_have 3 → 1
  | ⟨h, h'⟩ => .mk <| (lanLiftIsKan u (𝟙 a)).adjunction <| LanLift.CommuteWith.isKan u (𝟙 a) u
  tfae_finish

end LeftLift

namespace LeftExtension

set_option backward.isDefEq.respectTransparency false in
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
    let sτ := LeftExtension.mk _ <| 𝟙 _ ⊗≫ g ◁ η' ⊗≫ θ ▷ u ⊗≫ 𝟙 _
    let τ : t.extension ⟶ k ≫ u := H.desc sτ
    let sσ := LeftLift.mk _ <| (ρ_ _).hom ≫ τ
    let σ : t.extension ≫ h ⟶ k := H'.desc sσ
    LeftExtension.homMk σ <| (H' g).hom_ext <| by
      have Hσ : t.extension ◁ η' ⊗≫ σ ▷ u  = 𝟙 _ ⊗≫ τ := by
        simpa [bicategoricalComp] using (H' _).fac (.mk _ <| (ρ_ _).hom ≫ τ)
      dsimp only [LeftLift.whisker_lift, StructuredArrow.mk_right, LeftLift.whisker_unit,
        StructuredArrow.mk_hom_eq_self, whisker_extension, whisker_unit]
      calc _
        _ = (g ◁ η' ≫ t.unit ▷ (h ≫ u)) ⊗≫ f ◁ σ ▷ u ⊗≫ 𝟙 _ := by
          bicategory
        _ = t.unit ▷ (𝟙 c) ⊗≫ f ◁ (t.extension ◁ η' ⊗≫ σ ▷ u) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]; bicategory
        _ = (ρ_ g).hom ≫ t.unit ≫ f ◁ H.desc sτ ≫ (α_ f s.extension u).inv := by
          rw [Hσ]
          dsimp only [τ]
          bicategory
        _ = _ := by
          rw [IsKan.fac_assoc]
          dsimp only [StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self, sτ]
          bicategory) <| by
    intro s' τ₀'
    let τ' : t.extension ≫ h ⟶ s'.extension := τ₀'.right
    have Hτ' : t.unit ▷ h ⊗≫ f ◁ τ' = s'.unit := by simpa [bicategoricalComp] using τ₀'.w
    ext
    apply (H' _).hom_ext
    dsimp only [StructuredArrow.homMk_right]
    rw [(H' _).fac]
    apply (cancel_epi (ρ_ _).inv).mp
    apply H.hom_ext
    dsimp only [LeftLift.whisker_lift, StructuredArrow.mk_right, LeftLift.whisker_unit,
      StructuredArrow.mk_hom_eq_self]
    let σs' := LeftExtension.mk (s'.extension ≫ u)
      (𝟙 g ⊗≫ g ◁ η' ⊗≫ s'.unit ▷ u ⊗≫ 𝟙 (f ≫ s'.extension ≫ u))
    calc _
      _ = 𝟙 _ ⊗≫ (t.unit ▷ (𝟙 c) ≫ (f ≫ t.extension) ◁ η') ⊗≫ f ◁ τ' ▷ u := by
        bicategory
      _ = 𝟙 g ⊗≫ g ◁ η' ⊗≫ (t.unit ▷ h ⊗≫ f ◁ τ') ▷ u ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
      _ = t.unit ≫ f ◁ H.desc σs' := by
        rw [Hτ', IsKan.fac]
        dsimp only [StructuredArrow.mk_hom_eq_self, σs']
      _ = _ := by
        bicategory

instance {f : a ⟶ b} {g : a ⟶ c} {x : B} {h : c ⟶ x} [IsLeftAdjoint h] [HasLeftKanExtension f g] :
    Lan.CommuteWith f g h :=
  ⟨⟨isKanOfWhiskerLeftAdjoint (lanIsKan f g) (Adjunction.ofIsLeftAdjoint h)⟩⟩

end LeftExtension

end Bicategory

end CategoryTheory
