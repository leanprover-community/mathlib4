module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CanonicalCocone

@[expose] public section

open TopologicalSpace CategoryTheory Limits

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hpath_connected : ∀ U : Opens X, U ∈ 𝒰 → IsPathConnected (U : Set X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

/-- Helper: given a point `x` in an open `U ∈ 𝒰`, get the corresponding object in `s.pt`. -/
def obj_at (x : X) (U : Opens X) (hU : U ∈ 𝒰) (hx : x ∈ U) : s.pt :=
  (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk ⟨x, hx⟩)

/-- The object obtained from `x ∈ U ∈ 𝒰` is the same as from `x ∈ V ∈ 𝒰`.
    This uses the fact that `U ∩ V ∈ 𝒰` and the cocone naturality. -/
lemma obj_at_eq
    (hfinite_intersections :
      ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)
    (x : X)
    (U V : Opens X) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰) (hxU : x ∈ U) (hxV : x ∈ V) :
    obj_at X 𝒰 s x U hU hxU = obj_at X 𝒰 s x V hV hxV := by
  classical
  -- The intersection U ∩ V is in 𝒰 by finite intersections property
  let s_finset : Finset (Opens X) := {U, V}
  have h_nonempty : s_finset.Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr (by simp [s_finset])
  have h_all_in : ∀ W ∈ s_finset, W ∈ 𝒰 := by
    intro W hW
    have : W = U ∨ W = V := by
      simpa [s_finset] using hW
    rcases this with (rfl | rfl) <;> tauto
  let W := s_finset.inf (fun U : Opens X => U)
  have hW_in : W ∈ 𝒰 := hfinite_intersections s_finset h_nonempty h_all_in
  have hW_le_U : W ≤ U := Finset.inf_le (Finset.mem_insert_self U {V})
  have hW_le_V : W ≤ V := Finset.inf_le (by simp [s_finset])
  have hW_eq : W = U ⊓ V := by
    have h : W = s_finset.inf id := by rfl
    rw [h]
    have h2 : ({U, V} : Finset (Opens X)).inf id = U ⊓ V := by
      classical
      simp [Finset.inf_insert]
      <;> rfl
    exact h2
  have hxW : x ∈ W := by
    rw [hW_eq]
    exact ⟨hxU, hxV⟩

  -- Now we have W ∈ 𝒰 with W ≤ U and W ≤ V, and x ∈ W
  let i_WU : (⟨W, hW_in⟩ : {U // U ∈ 𝒰}) ⟶ ⟨U, hU⟩ := homOfLE hW_le_U
  let i_WV : (⟨W, hW_in⟩ : {U // U ∈ 𝒰}) ⟶ ⟨V, hV⟩ := homOfLE hW_le_V

  -- The cocone naturality: D.map i_WU ≫ s.ι.app ⟨U, hU⟩ = s.ι.app ⟨W, hW_in⟩
  -- where D is the diagram functor
  let D := ((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
    Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor
  have h_nat_U : D.map i_WU ≫ s.ι.app ⟨U, hU⟩ = s.ι.app ⟨W, hW_in⟩ := by
    exact s.ι.naturality i_WU
  have h_nat_V : D.map i_WV ≫ s.ι.app ⟨V, hV⟩ = s.ι.app ⟨W, hW_in⟩ := by
    exact s.ι.naturality i_WV

  -- Apply both sides to the object corresponding to x in W
  let x_W : D.obj ⟨W, hW_in⟩ := FundamentalGroupoid.mk ⟨x, hxW⟩

  have h1 : (s.ι.app ⟨U, hU⟩).obj ((D.map i_WU).obj x_W) = (s.ι.app ⟨W, hW_in⟩).obj x_W := by
    have h_eq : (D.map i_WU ≫ s.ι.app ⟨U, hU⟩).obj x_W = (s.ι.app ⟨W, hW_in⟩).obj x_W := by
      rw [h_nat_U]
      <;> rfl
    exact h_eq
  have h2 : (s.ι.app ⟨V, hV⟩).obj ((D.map i_WV).obj x_W) = (s.ι.app ⟨W, hW_in⟩).obj x_W := by
    have h_eq : (D.map i_WV ≫ s.ι.app ⟨V, hV⟩).obj x_W = (s.ι.app ⟨W, hW_in⟩).obj x_W := by
      rw [h_nat_V]
      <;> rfl
    exact h_eq

  -- But (D.map i_WU).obj x_W is just the object corresponding to x in U
  have h3 : (D.map i_WU).obj x_W = FundamentalGroupoid.mk ⟨x, hxU⟩ := by rfl
  have h4 : (D.map i_WV).obj x_W = FundamentalGroupoid.mk ⟨x, hxV⟩ := by rfl

  rw [h3] at h1
  rw [h4] at h2
  exact h1.trans h2.symm

/-- The object part of the descent functor.
    Given a point x of X, pick some U ∈ 𝒰 containing x (exists by hcover),
    and use the cocone leg at U to get an object of s.pt.
    The result is independent of the choice of U by obj_at_eq. -/
def desc_functor_obj (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) :
    s.pt :=
  let x_pt : X := x.as
  let h : ∃ (U : Opens X), U ∈ 𝒰 ∧ x_pt ∈ U := hcover x_pt
  let U : Opens X := Classical.choose h
  let hU : U ∈ 𝒰 ∧ x_pt ∈ U := Classical.choose_spec h
  obj_at X 𝒰 s x_pt U hU.1 hU.2

/-- The fac property: on objects, composing the inclusion π₁(U) → π₁(X) with the descent
    functor gives the same as applying the cocone leg directly. -/
theorem fac_property_obj
    (hfinite_intersections :
      ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)
    (U : Opens X) (hU : U ∈ 𝒰) :
    ∀ (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U)),
      desc_functor_obj X 𝒰 hcover s
        ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x) =
      (s.ι.app ⟨U, hU⟩).obj x := by
  intro x
  -- x is an object of π₁(U)
  let z : (Opens.toTopCat (TopCat.of X)).obj U := x.as
  let z_X : X := z.val
  have hz : z_X ∈ U := z.property

  -- The inclusion map sends x to FundamentalGroupoid.mk z_X in π₁(X)
  have h1 : (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x =
      (FundamentalGroupoid.mk z_X : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) := by
    rfl

  rw [h1]

  have h_main : desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk z_X) =
      obj_at X 𝒰 s z_X U hU hz := by
    dsimp only [desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ z_X ∈ U' := hcover z_X
    have h' : obj_at X 𝒰 s z_X (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2 =
        obj_at X 𝒰 s z_X U hU hz :=
      obj_at_eq X 𝒰 s hfinite_intersections z_X (Classical.choose h) U
        (Classical.choose_spec h).1 hU (Classical.choose_spec h).2 hz
    exact h'

  have h3 : obj_at X 𝒰 s z_X U hU hz = (s.ι.app ⟨U, hU⟩).obj x := by
    rfl

  calc
    desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk z_X)
      = obj_at X 𝒰 s z_X U hU hz := h_main
    _ = (s.ι.app ⟨U, hU⟩).obj x := h3

end

end
