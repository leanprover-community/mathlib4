import Mathlib.Tactic.Tendsto.Multiseries.Colist
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Tactic

-- universe u v

namespace TendstoTactic

abbrev Basis := List (ℝ → ℝ)

abbrev PreMS (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | _ :: tl => CoList (ℝ × PreMS tl)

namespace PreMS

instance (basis : Basis) : Inhabited (PreMS basis) where
  default := match basis with
  | [] => default
  | _ :: _ => default

inductive wellOrdered : {basis : Basis} → (PreMS basis) → Prop
| const (ms : PreMS []) : wellOrdered ms
| colist {hd : _} {tl : _} (ms : PreMS (hd :: tl))
    (h_head : ∀ x, ms.head = .some x → x.2.wellOrdered)
    (h_tail : wellOrdered (basis := hd :: tl) ms.tail)
    (h_wo : ∀ i j x y, (i < j) → (ms.get i = .some x) → (ms.get j = .some y) → (x.1 > y.1)) : wellOrdered ms -- maybe define in another way

noncomputable def partialSumsFrom (Cs : CoList (ℝ → ℝ)) (degs : CoList ℝ) (basis_fun : ℝ → ℝ) (init : ℝ → ℝ) : CoList (ℝ → ℝ) :=
  Cs.zip degs |>.fold init fun acc (C, deg) =>
    fun x ↦ acc x + (basis_fun x)^deg * (C x)

noncomputable def partialSums (Cs : CoList (ℝ → ℝ)) (degs : CoList ℝ) (basis_fun : ℝ → ℝ) : CoList (ℝ → ℝ) :=
  partialSumsFrom Cs degs basis_fun 0

theorem partialSumsFrom_cons {Cs_hd : ℝ → ℝ} {Cs_tl : CoList (ℝ → ℝ)} {degs_hd : ℝ} {degs_tl : CoList ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ} :
    partialSumsFrom (.cons Cs_hd Cs_tl) (.cons degs_hd degs_tl) basis_fun init =
    (.cons init <| partialSumsFrom Cs_tl degs_tl basis_fun (fun x ↦ init x + (basis_fun x)^degs_hd * (Cs_hd x))) := by
  simp [partialSumsFrom]

theorem partialSumsFrom_eq_map {Cs : CoList (ℝ → ℝ)} {degs : CoList ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ}
    (h : Cs.atLeastAsLongAs degs) :
    partialSumsFrom Cs degs basis_fun init = (partialSums Cs degs basis_fun).map fun G => init + G := by

  let motive : CoList (ℝ → ℝ) → CoList (ℝ → ℝ) → Prop := fun x y =>
    ∃ Cs degs init D,
      Cs.atLeastAsLongAs degs ∧
      (
        (x = partialSumsFrom Cs degs basis_fun (D + init)) ∧
        (y = (partialSumsFrom Cs degs basis_fun init).map fun G => D + G)
      ) ∨
      (x = .nil ∧ y = .nil)
  apply CoList.Eq.principle motive
  · intro x y ih
    simp [motive] at ih
    obtain ⟨Cs', degs', init', D, ih⟩ := ih
    cases' ih with ih ih
    · left
      obtain ⟨h_alal, h_x_eq, h_y_eq⟩ := ih
      revert h_alal h_x_eq h_y_eq
      apply degs'.casesOn
      · simp [partialSums, partialSumsFrom]
        intro h_x_eq h_y_eq
        use D + init'
        use .nil
        constructor
        · assumption
        use D + init'
        use .nil
        constructor
        · assumption
        constructor
        · rfl
        simp [motive]
      · intro degs_hd degs_tl h_alal h_x_eq h_y_eq
        obtain ⟨Cs_hd, Cs_tl, h_Cs⟩ := CoList.atLeastAsLongAs_cons h_alal
        subst h_Cs
        simp [partialSums, partialSumsFrom_cons] at h_x_eq h_y_eq
        use D + init'
        use (partialSumsFrom Cs_tl degs_tl basis_fun fun x ↦ D x + init' x + basis_fun x ^ degs_hd * Cs_hd x)
        use D + init'
        use (CoList.map (fun G ↦ D + G) (partialSumsFrom Cs_tl degs_tl basis_fun fun x ↦ init' x + basis_fun x ^ degs_hd * Cs_hd x))
        constructor
        · assumption
        constructor
        · assumption
        constructor
        · rfl
        simp [motive]
        simp at h_alal
        use Cs_tl
        use degs_tl
        use fun x ↦ init' x + basis_fun x ^ degs_hd * Cs_hd x
        use D
        left
        constructor
        · assumption
        constructor
        · congr
          eta_expand
          simp
          ext
          ring_nf
        rfl
    · right
      exact ih
  · simp [motive]
    use Cs
    use degs
    use 0
    use init
    left
    constructor
    · assumption
    constructor
    · simp
    · simp [partialSums]

-- a non valid occurrence of the datatypes being declared
-- inductive isApproximation : (ℝ → ℝ) → (basis : Basis) → PreMS basis → Prop where
-- | const {c : ℝ} {F : ℝ → ℝ} (h : F =ᶠ[Filter.atTop] fun _ ↦ c) : isApproximation F [] c
-- | colist {F basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : PreMS (basis_hd :: basis_tl))
--   (Cs : CoList (ℝ → ℝ))
--   (h_coef : (Cs.zip ms).all fun (C, (deg, coef)) => isApproximation C basis_tl coef)
--   (h_comp : (partialSums Cs (ms.map fun x => x.1) basis_hd).zip (ms.map fun x => x.1) |>.all fun (ps, deg) => ∀ deg', deg < deg' → (fun x ↦ F x - ps x) =o[Filter.atTop] (fun x ↦ (basis_hd x)^deg')) :
--   isApproximation F (basis_hd :: basis_tl) ms

def isApproximation (F : ℝ → ℝ) (basis : Basis) (ms : PreMS basis) : Prop :=
  match basis with
  | [] => F =ᶠ[Filter.atTop] fun _ ↦ ms
  | basis_hd :: basis_tl =>
    ∃ Cs : CoList (ℝ → ℝ),
    Cs.atLeastAsLongAs ms ∧
    ((Cs.zip ms).all fun (C, (_, coef)) => isApproximation C basis_tl coef) ∧
    (
      let degs := ms.map fun x => x.1;
      let degs' : CoList (Option ℝ) := (degs.map .some).append (.cons .none .nil);
      (partialSums Cs degs basis_hd).zip degs' |>.all fun (ps, deg?) =>
        match deg? with
        | .some deg => ∀ deg', deg < deg' → (fun x ↦ F x - ps x) =o[Filter.atTop] (fun x ↦ (basis_hd x)^deg')
        | .none => (fun x ↦ F x - ps x) =ᶠ[Filter.atTop] 0
    )

theorem isApproximation_nil {F basis_hd : ℝ → ℝ} {basis_tl : Basis} (h : isApproximation F (basis_hd :: basis_tl) CoList.nil) :
    F =ᶠ[Filter.atTop] 0 := by
  unfold isApproximation at h
  obtain ⟨Cs, _, _, h_comp⟩ := h
  simp at h_comp
  unfold CoList.all at h_comp
  specialize h_comp 0
  simpa [partialSums, partialSumsFrom] using h_comp

theorem isApproximation_cons {F basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} (h : isApproximation F (basis_hd :: basis_tl) (.cons (deg, coef) tl)) :
    ∃ C,
      isApproximation C basis_tl coef ∧
      (∀ deg', deg < deg' → F =o[Filter.atTop] (fun x ↦ (basis_hd x)^deg')) ∧
      isApproximation (fun x ↦ F x - (basis_hd x)^deg * (C x)) (basis_hd :: basis_tl) tl := by
  unfold isApproximation at h
  obtain ⟨Cs, h_alal, h_coef, h_comp⟩ := h
  obtain ⟨C, Cs_tl, h_alal⟩ := CoList.atLeastAsLongAs_cons h_alal
  subst h_alal
  use C
  simp [CoList.all_cons] at h_coef
  constructor
  · exact h_coef.left
  · constructor
    · simp [partialSums, partialSumsFrom] at h_comp
      exact h_comp.left
    · simp at h_alal
      unfold isApproximation
      use Cs_tl
      constructor
      · assumption
      · constructor
        · exact h_coef.right
        · simp [partialSums, partialSumsFrom_cons] at h_comp
          replace h_comp := h_comp.right
          rw [partialSumsFrom_eq_map (CoList.atLeastAsLongAs_map h_alal)] at h_comp
          rw [CoList.map_zip_left] at h_comp
          replace h_comp := CoList.map_all h_comp
          apply CoList.all_mp _ h_comp
          intro (C', deg?)
          simp
          intro h
          ring_nf at h
          ring_nf
          exact h

structure auxT (motive : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : List (ℝ → ℝ)) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (basis_hd : ℝ → ℝ) (basis_tl : List (ℝ → ℝ)) where
  val : PreMS (basis_hd :: basis_tl)
  F : ℝ → ℝ
  h : motive F basis_hd basis_tl val

theorem isApproximation_principle (motive : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : List (ℝ → ℝ)) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_survive : ∀ basis_hd basis_tl F ms, motive F basis_hd basis_tl ms →
      (ms = .nil ∧ F =ᶠ[Filter.atTop] 0) ∨
      (
        ∃ deg coef tl C, ms = .cons (deg, coef) tl ∧
        (isApproximation C basis_tl coef) ∧
        (∀ deg', deg < deg' → F =o[Filter.atTop] fun x ↦ (basis_hd x)^deg') ∧
        (motive (fun x ↦ F x - (basis_hd x)^deg * (C x)) basis_hd basis_tl tl)
      )
    ) {basis_hd : ℝ → ℝ} {basis_tl : List (ℝ → ℝ)} {F : ℝ → ℝ} {ms : PreMS (basis_hd :: basis_tl)}
    (h : motive F basis_hd basis_tl ms) : isApproximation F (basis_hd :: basis_tl) ms := by
  simp [isApproximation]
  let Cs : CoList (ℝ → ℝ) :=
    let T := auxT motive basis_hd basis_tl
    let g : T → CoList.OutType (ℝ → ℝ) T := fun ⟨val, F, h⟩ =>
      (val.casesOn (motive := fun ms => motive F basis_hd basis_tl ms → CoList.OutType (ℝ → ℝ) T)
      (nil := fun _ ↦ .nil)
      (cons := fun (deg, coef) tl =>
        fun h =>
          have kek : ∃ C,
              isApproximation C basis_tl coef ∧
              (∀ (deg' : ℝ), deg < deg' → F =o[Filter.atTop] fun x ↦ basis_hd x ^ deg') ∧
              motive (fun x ↦ F x - basis_hd x ^ deg * C x) basis_hd basis_tl tl := by
            specialize h_survive _ _ _ _ h
            simp at h_survive
            obtain ⟨deg_1, coef_1, tl_1, h_survive⟩ := h_survive
            have := CoList.cons_eq_cons h_survive.left
            simp at this
            obtain ⟨⟨h1, h2⟩, h3⟩ := this
            subst h1
            subst h2
            subst h3
            exact h_survive.right
          let C := kek.choose
          .cons C ⟨tl, fun x ↦ F x - (basis_hd x)^deg * (C x), kek.choose_spec.right.right⟩
      )
      ) h
    CoList.corec g ⟨ms, F, h⟩
  use Cs
  constructor
  · sorry -- need coind for atLeastAsLong
  · constructor
    · sorry
    · sorry

-- Prove with coinduction?
theorem isApproximation.nil {F : ℝ → ℝ} {basis_hd : ℝ → ℝ} {basis_tl : List (ℝ → ℝ)}
    (h : F =ᶠ[Filter.atTop] 0) : isApproximation F (basis_hd :: basis_tl) .nil := by
  simp [isApproximation]
  use .nil
  simpa [partialSums, partialSumsFrom]

theorem isApproximation.cons {F : ℝ → ℝ} {basis_hd : ℝ → ℝ} {basis_tl : List (ℝ → ℝ)} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (C : ℝ → ℝ) (h_coef : coef.isApproximation C basis_tl)
    (h_comp : (∀ deg', deg < deg' → F =o[Filter.atTop] (fun x ↦ (basis_hd x)^deg')))
    (h_tl : tl.isApproximation (fun x ↦ F x - (basis_hd x)^deg * (C x)) (basis_hd :: basis_tl)) :
    isApproximation F (basis_hd :: basis_tl) (.cons (deg, coef) tl) := by
  sorry

theorem wellOrdered_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : wellOrdered (basis := basis_hd :: basis_tl) (CoList.cons (deg, coef) tl)) :
    coef.wellOrdered ∧ tl.wellOrdered := by
  sorry

-- theorem wellOrdered.tl {hd : _} {tl : _} {ms : PreMS (hd :: tl)} (h : wellOrdered (basis := hd :: tl) ms) :
--     wellOrdered (basis := hd :: tl) ms.tail := by
--   sorry

---------

theorem isApproximation_of_EventuallyEq {basis : Basis} {ms : PreMS basis} {F F' : ℝ → ℝ}
    (h_approx : ms.isApproximation F basis) (h_equiv : F =ᶠ[Filter.atTop] F') : ms.isApproximation F' basis :=
  match basis with
  | [] => by
    simp [isApproximation] at h_approx
    exact Filter.EventuallyEq.trans h_equiv.symm h_approx
  | basis_hd :: basis_tl => by
    let motive : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) → (basis_tl : List (ℝ → ℝ)) → (ms : PreMS (basis_hd :: basis_tl)) → Prop :=
      fun F' basis_hd basis_tl ms =>
        ∃ F, F =ᶠ[Filter.atTop] F' ∧ isApproximation F (basis_hd :: basis_tl) ms
    apply isApproximation_principle motive
    · intro basis_hd basis_tl F' ms ih
      revert ih
      apply ms.casesOn
      · intro ih
        left
        simp [motive] at ih
        obtain ⟨F, h_equiv, hF⟩ := ih
        replace hF := isApproximation_nil hF
        constructor
        · rfl
        · exact Filter.EventuallyEq.trans h_equiv.symm hF
      · intro (deg, coef) tl ih
        right
        use deg
        use coef
        use tl
        simp
        simp [motive] at ih
        obtain ⟨F, h_equiv, hF⟩ := ih
        replace hF := isApproximation_cons hF
        obtain ⟨C, h_coef, h_comp, h_tl⟩ := hF
        use C
        constructor
        · exact h_coef
        constructor
        · intro deg' h
          apply Filter.EventuallyEq.trans_isLittleO h_equiv.symm
          apply h_comp _ h
        · simp [motive]
          use fun x ↦ F x - basis_hd x ^ deg * (C x)
          constructor
          · apply Filter.EventuallyEq.sub h_equiv
            apply Filter.EventuallyEq.rfl
          · exact h_tl
    · simp only [motive]
      use F

-- Try to prove later
-- theorem EventuallyEq_of_isApproximation {F F' : ℝ → ℝ} {basis : Basis} {ms : PreMS basis}
--     (h_approx : ms.isApproximation F basis) (h_approx' : ms.isApproximation F' basis) : F =ᶠ[Filter.atTop] F' :=
--   match basis with
--   | [] => by
--     simp [isApproximation] at *
--     trans (fun _ ↦ ms)
--     · exact h_approx
--     · exact h_approx'.symm
--   | basis_hd :: basis_tl => by

--     revert h_approx h_approx'
--     apply ms.casesOn
--     · intro h_approx h_approx'
--       replace h_approx := isApproximation_nil h_approx
--       replace h_approx' := isApproximation_nil h_approx'
--       trans (fun _ ↦ 0)
--       · exact h_approx
--       · exact h_approx'.symm
--     · intro (deg, coef) tl h_approx h_approx'
--       replace h_approx := isApproximation_cons h_approx
--       replace h_approx' := isApproximation_cons h_approx'
--       obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
--       obtain ⟨C', h_coef', h_comp', h_tl'⟩ := h_approx'



--   induction ms using PreMS.rec' generalizing F F' basis with
--   | nil =>
--     cases h_approx with | nil _ _ h =>
--     cases h_approx' with | nil _ _ h' =>
--     trans 0
--     · exact h
--     · exact h'.symm
--   | const c =>
--     cases h_approx with | const _ _ h =>
--     cases h_approx' with | const _ _ h' =>
--     trans (fun _ ↦ c)
--     · exact h
--     · exact h'.symm
--   | cons deg coef tl coef_ih tl_ih =>
--     cases h_approx with | cons _ _ _ _ C basis_hd basis_tl h_coef h_tl h_comp =>
--     cases h_approx' with | cons _ _ _ _ C' _ _ h_coef' h_tl' h_comp' =>
--     have : (fun x ↦ basis_hd x ^ deg * C x) =ᶠ[Filter.atTop] (fun x ↦ basis_hd x ^ deg * C' x) :=
--       Filter.EventuallyEq.mul (by rfl) (coef_ih h_coef h_coef')
--     have := (tl_ih h_tl h_tl').add this
--     simpa using this

---------

-- theorem kek (motive : (basis : Basis) → PreMS basis → Prop) (basis basis' : Basis)
--     (h_basis : basis = basis') (ms : PreMS basis) (ms' : PreMS basis') (h_eq : ms = h_basis ▸ ms')
--     (h : motive basis ms) : motive basis' ms' := by
--   subst h_eq
--   subst h_basis
--   simp_all only

def const (c : ℝ) (basis : Basis) : PreMS basis :=
  match basis with
  | [] => c
  | _ :: basis_tl =>
    .cons (0, const c basis_tl) .nil

def zero (basis : Basis) : PreMS basis :=
  const 0 basis

def one (basis : Basis) : PreMS basis :=
  const 1 basis

end PreMS

structure MS where
  basis : Basis
  val : PreMS basis
  F : ℝ → ℝ
  h_wo : val.wellOrdered
  h_approx : val.isApproximation F basis

end TendstoTactic
