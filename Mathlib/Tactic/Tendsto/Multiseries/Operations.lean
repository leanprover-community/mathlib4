import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Tactic.Tendsto.Multiseries.Basis

namespace TendstoTactic

def PreMS.neg (ms : PreMS) : PreMS :=
  match ms with
  | .const c => .const (-c)
  | .nil => .nil
  | .cons deg coef tl => .cons deg coef.neg (.mk fun _ => tl.get.neg)

theorem PreMS.neg_preserve_depth {n : ℕ} {ms : PreMS} (p : ms.hasDepth n) : ms.neg.hasDepth n := by
  induction ms using PreMS.rec' generalizing n with
  | const _ => cases p; simp [neg]; constructor
  | nil =>  cases p; simp [neg]; constructor
  | cons deg coef tl coef_ih tl_ih =>
    cases p with | cons _ _ _ _ h_coef h_tl =>
    simp [PreMS.neg]
    constructor
    · exact coef_ih h_coef
    · exact tl_ih h_tl

theorem PreMS.neg_preserve_wo {ms : PreMS} (p : ms.wellOrdered) : ms.neg.wellOrdered := by
  induction ms using PreMS.rec' with
  | const _ => simp [PreMS.neg, PreMS.wellOrdered]
  | nil => simp [PreMS.neg, PreMS.wellOrdered]
  | cons deg coef tl coef_ih tl_ih =>
    simp [neg, wellOrdered]
    simp [PreMS.wellOrdered] at p
    generalize tl.get = tlg at *
    cases tlg with
    | cons tl_deg _ tl_tl =>
      simp [neg] at tl_ih ⊢
      tauto
    | const c =>
      simp [neg] at tl_ih ⊢
      constructor
      · exact coef_ih p.left
      · exact tl_ih p.right.left
    | nil =>
      simp [neg] at tl_ih ⊢
      constructor
      · exact coef_ih p.left
      · simp [wellOrdered]

theorem PreMS.neg_F {ms : PreMS} {F : ℝ → ℝ} {basis : Basis} (h_approx : ms.isApproximation F basis) :
    ms.neg.isApproximation (fun x ↦ -(F x)) basis := by
  induction ms using PreMS.rec' generalizing F basis with
  | const c =>
    simp [PreMS.neg]
    cases h_approx with | const _ _ h =>
    apply isApproximation.const
    exact Filter.EventuallyEq.neg h
  | nil =>
    simp [PreMS.neg]
    cases h_approx with | nil _ _ h =>
    apply isApproximation.nil
    rw [← neg_zero]
    exact Filter.EventuallyEq.neg h
  | cons deg coef tl coef_ih tl_ih =>
    simp [PreMS.neg]
    cases h_approx with | cons _ _ _ _ C basis_hd basis_tl h_coef h_tl h_comp =>
    apply isApproximation.cons
    · exact coef_ih h_coef
    · simp only [Thunk.get_mk, mul_neg, ← neg_sub']
      exact tl_ih h_tl
    · intros
      apply Asymptotics.IsLittleO.neg_left
      apply h_comp
      assumption

def MS.neg (ms : MS) : MS where
  val := ms.val.neg
  basis := ms.basis
  F := fun x ↦ -(ms.F x)
  h_depth := PreMS.neg_preserve_depth ms.h_depth
  h_wo := PreMS.neg_preserve_wo ms.h_wo
  h_approx := PreMS.neg_F ms.h_approx

noncomputable def PreMS.add (f g : PreMS) : PreMS :=
  match f, g with
  | .nil, g => g
  | f, .nil => f
  | .const a, .const b => .const (a + b)
  | .const _, _ => default
  | _, .const _ => default
  | .cons f_deg f_coef f_tl, .cons deg_g g_coef tl_g =>
    if deg_g < f_deg then
      .cons f_deg f_coef <| .mk fun _ => PreMS.add f_tl.get (.cons deg_g g_coef tl_g)
    else if f_deg < deg_g then
      .cons deg_g g_coef <| .mk fun _ => PreMS.add (.cons f_deg f_coef f_tl) tl_g.get
    else
      .cons f_deg (PreMS.add f_coef g_coef) <| .mk fun _ => PreMS.add f_tl.get tl_g.get

theorem PreMS.add_preserve_depth {n : ℕ} {f g : PreMS} (pf : f.hasDepth n) (pg : g.hasDepth n) :
    (PreMS.add f g).hasDepth n := by
  induction f using PreMS.rec' generalizing n g with
  | const _ =>
    cases g with
    | const _ => cases pf; unfold add; constructor
    | nil => cases pf; unfold add; constructor
    | cons _ _ _ => cases pf; cases pg
  | nil => cases g <;> (cases pf; unfold add; assumption)
  | cons f_deg f_coef f_tl f_coef_ih f_tl_ih =>
    induction g using PreMS.rec' generalizing n with
    | const _ => cases pf; cases pg
    | nil => unfold add; assumption
    | cons g_deg g_coef g_tl _ g_tl_ih =>
      unfold add
      split_ifs
      · cases pf with | cons _ _ _ _ h_f_coef h_f_tl =>
        constructor
        · exact h_f_coef
        · simp only [Thunk.get_mk]
          exact f_tl_ih h_f_tl pg
      · cases pg with | cons _ _ _ _ h_g_coef h_g_tl =>
        constructor
        · exact h_g_coef
        · simp only [Thunk.get_mk]
          exact g_tl_ih pf h_g_tl
      · cases pf with | cons _ _ _ _ h_f_coef h_f_tl =>
        cases pg with | cons _ _ _ _ h_g_coef h_g_tl =>
        constructor
        · exact f_coef_ih h_f_coef h_g_coef
        · simp only [Thunk.get_mk]
          exact f_tl_ih h_f_tl h_g_tl

theorem PreMS.add_preserve_wo {f g : PreMS} (hf_wo : f.wellOrdered) (hg_wo : g.wellOrdered) :
    (PreMS.add f g).wellOrdered := by
  induction f using PreMS.rec' generalizing g with
  | const => cases g <;> simp [add, default, wellOrdered]
  | nil =>
    cases g with
    | cons => simpa [add]
    | _ => simp [add, default, wellOrdered]
  | cons f_deg f_coef f_tl f_coef_ih f_tl_ih =>
    induction g using PreMS.rec' with
    | const _ => simp [add, default, wellOrdered]
    | nil => simpa [add]
    | cons g_deg g_coef g_tl _ g_tl_ih =>
      simp [add]
      split_ifs with h₁ h₂
      · unfold wellOrdered
        simp only [Thunk.get_mk]
        constructor
        · simp [wellOrdered] at hf_wo; tauto
        · constructor
          · simp [wellOrdered] at hf_wo; tauto
          · simp [wellOrdered] at hf_wo
            generalize f_tl.get = ftl at *
            cases ftl with
            | nil => simpa [add]
            | const => simp [add]
            | cons =>
              simp [add]
              simp at hf_wo
              split_ifs <;> (simp only; tauto)
      · unfold wellOrdered -- copypaste of above
        simp only [Thunk.get_mk]
        constructor
        · simp [wellOrdered] at hg_wo; tauto
        · constructor
          · simp [wellOrdered] at hg_wo; tauto
          · simp [wellOrdered] at hg_wo
            generalize g_tl.get = gtl at *
            cases gtl with
            | nil => simpa [add]
            | const => simp [add]
            | cons =>
              simp [add]
              simp at hg_wo
              split_ifs <;> (simp only; tauto)
      · have h : f_deg = g_deg := by linarith -- copypaste of above
        unfold wellOrdered
        simp only [Thunk.get_mk]
        constructor
        · apply f_coef_ih
          · simp [wellOrdered] at hf_wo; tauto
          · simp [wellOrdered] at hg_wo; tauto
        · constructor
          · apply f_tl_ih
            · simp [wellOrdered] at hf_wo; tauto
            · simp [wellOrdered] at hg_wo; tauto
          · simp [wellOrdered] at hf_wo hg_wo
            generalize f_tl.get = ftl at *
            cases ftl with
            | nil => simp [add]; simp_rw [h]; tauto
            | const => cases g_tl.get <;> simp [add]
            | cons =>
              generalize g_tl.get = gtl at *
              cases gtl
              · simp [add]
              · simp [add]; tauto
              · simp [add]
                simp [wellOrdered] at hf_wo hg_wo
                split_ifs <;> simp only
                · tauto
                · rw [h]; tauto
                · tauto

theorem PreMS.add_F {f g : PreMS} {F G : ℝ → ℝ} {basis : Basis} (hf_depth : f.hasDepth basis.length)
    (hg_depth : g.hasDepth basis.length) (hf_approx : f.isApproximation F basis)
    (hg_approx : g.isApproximation G basis) : (f.add g).isApproximation (F + G) basis := by
  induction f using PreMS.rec' generalizing g F G basis with
  | const a =>
    cases g with
    | const _ =>
      cases hf_approx with | const _ _ hF =>
      cases hg_approx with | const _ _ hG =>
      unfold add
      apply isApproximation.const
      exact Filter.EventuallyEq.add hF hG
    | nil =>
      cases hf_approx with | const _ _ hF =>
      cases hg_approx with | nil _ _ hG =>
      unfold add
      apply isApproximation.const
      conv in a => rw [← add_zero a]
      exact Filter.EventuallyEq.add hF hG
    | cons _ _ _ => cases basis <;> (cases hf_depth; try cases hg_depth)
  | nil =>
    simp [add]
    cases hf_approx with | nil _ _ hF =>
    apply PreMS.isApproximation_of_EventuallyEq hg_approx
    symm
    have := Filter.EventuallyEq.add hF (Filter.EventuallyEq.refl _ G)
    simpa using this
  | cons f_deg f_coef f_tl f_coef_ih f_tl_ih =>
    induction g using PreMS.rec' generalizing F G basis with
    | const _ => cases basis <;> (cases hf_depth; try cases hg_depth)
    | nil => -- copypaste
      simp [add]
      cases hg_approx with | nil _ _ hG =>
      apply PreMS.isApproximation_of_EventuallyEq hf_approx
      symm
      have := Filter.EventuallyEq.add (Filter.EventuallyEq.refl _ F) hG
      simpa using this
    | cons g_deg g_coef g_tl _ g_tl_ih =>
      unfold add
      split_ifs with h₁ h₂
      · cases hf_approx with | cons _ _ _ _ C basis_hd basis_tl h_f_coef h_f_tl h_f_comp =>
        cases hf_depth with | cons _ _ _ _ h_f_coef_depth h_f_tl_depth =>
        apply isApproximation.cons
        · exact h_f_coef
        · simp only [Thunk.get_mk]
          conv =>
            lhs
            ext x
            simp
            rw [show F x + G x - basis_hd x ^ f_deg * C x =
              (F x - basis_hd x ^ f_deg * C x) + G x by ring_nf]
          apply f_tl_ih (by simpa) hg_depth h_f_tl hg_approx
        · intro deg h_deg
          apply Asymptotics.IsLittleO.add
          · exact h_f_comp _ h_deg
          · cases hg_approx with | cons _ _ _ _ _ _ _ _ _ h_g_comp =>
            exact h_g_comp _ <| h₁.trans h_deg
      · cases hg_approx with | cons _ _ _ _ C basis_hd basis_tl h_g_coef h_g_tl h_g_comp =>
        cases hg_depth with | cons _ _ _ _ h_g_coef_depth h_g_tl_depth =>
        apply isApproximation.cons
        · exact h_g_coef
        · simp only [Thunk.get_mk]
          conv =>
            lhs
            ext x
            simp
            rw [show F x + G x - basis_hd x ^ g_deg * C x =
              F x + (G x - basis_hd x ^ g_deg * C x) by ring_nf]
          apply g_tl_ih hf_depth (by simpa) hf_approx h_g_tl
        · intro deg h_deg
          apply Asymptotics.IsLittleO.add
          · cases hf_approx with | cons _ _ _ _ _ _ _ _ _ h_f_comp =>
            exact h_f_comp _ <| h₂.trans h_deg
          · exact h_g_comp _ h_deg
      · have h : f_deg = g_deg := by linarith
        cases hf_approx with | cons _ _ _ _ FC basis_hd basis_tl h_f_coef h_f_tl h_f_comp =>
        cases hg_approx with | cons _ _ _ _ GC _ _ h_g_coef h_g_tl h_g_comp =>
        cases hf_depth with | cons _ _ _ _ h_f_coef_depth h_f_tl_depth =>
        cases hg_depth with | cons _ _ _ _ h_g_coef_depth h_g_tl_depth =>
        apply isApproximation.cons
        · exact f_coef_ih h_f_coef_depth h_g_coef_depth h_f_coef h_g_coef
        · simp only [Thunk.get_mk]
          conv =>
            lhs
            ext x
            simp
            rw [show F x + G x - basis_hd x ^ f_deg * (FC x + GC x) =
              (F x - basis_hd x ^ f_deg * FC x) + (G x - basis_hd x ^ g_deg * GC x) by rw [h]; ring_nf]
          apply f_tl_ih <;> ((try simp only [List.length_cons]); assumption)
        · intro deg h_deg
          apply Asymptotics.IsLittleO.add
          · exact h_f_comp _ h_deg
          · exact h_g_comp _ (h ▸ h_deg)

noncomputable def MS.add (f g : MS) (h_basis : f.basis = g.basis) : MS where
  val := f.val.add g.val
  basis := f.basis
  F := f.F + g.F
  h_depth := PreMS.add_preserve_depth f.h_depth (h_basis ▸ g.h_depth)
  h_wo := PreMS.add_preserve_wo f.h_wo g.h_wo
  h_approx := PreMS.add_F f.h_depth (h_basis ▸ g.h_depth) f.h_approx (h_basis ▸ g.h_approx)

noncomputable def PreMS.mul (f g : PreMS) : PreMS :=
  match f, g with
  | .const a, .const b => .const (a * b)
  | .nil, _ => .nil
  | _, .nil => .nil
  | .const _, _ => default
  | _, .const _ => default
  | f, .cons deg_g g_coef tl_g =>
    PreMS.add (mulMonomial f g_coef deg_g) <| PreMS.mul f tl_g.get
where mulMonomial (h m_coef : PreMS) (m_deg : ℝ) : PreMS :=
  match h with
  | .const _ => default
  | .nil => .nil
  | .cons deg coef tl =>
    .cons (deg + m_deg) (PreMS.mul coef m_coef) <| mulMonomial tl.get m_coef m_deg

lemma PreMS.mul_preserve_depth_aux_aux1 {n : ℕ} {c : ℝ} (g : PreMS)
    (hf : (PreMS.const c).hasDepth n) (hg : g.hasDepth n) : ((PreMS.const c).mul g).hasDepth n := by
  cases hg <;> (unfold mul; constructor)

lemma PreMS.mul_preserve_depth_aux_aux2 {n : ℕ} (g : PreMS)
    (hf : PreMS.nil.hasDepth n) (hg : g.hasDepth n) : (PreMS.nil.mul g).hasDepth n := by
  cases n with
  | succ m => simpa [mul]
  | zero => cases g <;> simp_all [mul, hasDepth]

-- lemma PreMS.mul_wf_aux_aux3 {n : ℕ} (h : PreMS) (c m_deg : ℝ)
--     (hh : h.hasDepth (n + 1)) (hm : (PreMS.const c).hasDepth n) : (PreMS.mul.mulMonomial h (PreMS.const c) m_deg).hasDepth (n + 1) := by
--   induction h using PreMS.rec generalizing n with
--   | cons _ coef tl coef_ih tl_ih =>
--     have tl_ih : ∀ {n : ℕ}, tl.get.hasDepth (n + 1) → (const c).hasDepth n → (mul.mulMonomial tl.get (const c) m_deg).hasDepth (n + 1) := tl_ih
--     simp [mul.mulMonomial, mul, hasDepth]
--     constructor
--     · cases coef <;> simp_all [mul, hasDepth]
--     · apply tl_ih
--       · simp [hasDepth] at hh
--         exact hh.right
--       · cases n <;> simp_all [hasDepth]
--   | const _ => simp [hasDepth] at hh
--   | nil => simp [mul.mulMonomial, hasDepth]
--   | mk _ ih => apply ih

-- lemma PreMS.mul_wf_aux_aux4 {n : ℕ} (h : PreMS) (m_deg : ℝ)
--     (hh : h.hasDepth (n + 1)) (hm : PreMS.nil.hasDepth n) : (PreMS.mul.mulMonomial h PreMS.nil m_deg).hasDepth (n + 1) := by
--   induction h using PreMS.rec generalizing n with
--   | cons _ coef tl coef_ih tl_ih =>
--     have tl_ih : ∀ {n : ℕ}, tl.get.hasDepth (n + 1) → nil.hasDepth n → (mul.mulMonomial tl.get nil m_deg).hasDepth (n + 1) := tl_ih
--     simp [mul.mulMonomial, mul, hasDepth]
--     constructor
--     · cases coef <;> simp_all [mul, hasDepth]
--     · apply tl_ih
--       · simp [hasDepth] at hh
--         exact hh.right
--       · simp [hasDepth]
--   | const _ => simp [hasDepth] at hh
--   | nil => simp [mul.mulMonomial, hasDepth]
--   | mk _ ih => apply ih


theorem PreMS.mul_preserve_depth_aux {n : ℕ} (f g_coef : PreMS) (g_deg : ℝ) (g_tl : Thunk PreMS)
    (pf : f.hasDepth n) (pg : (PreMS.cons g_deg g_coef g_tl).hasDepth n) :
    (f.mul (PreMS.cons g_deg g_coef g_tl)).hasDepth n ∧
    (PreMS.mul.mulMonomial f g_coef g_deg).hasDepth n := by
  cases pg with | cons m _ _ _ h_g_coef h_g_tl =>
  induction f using PreMS.rec' generalizing m g_coef g_deg g_tl with
  | cons f_deg f_coef f_tl f_coef_ih f_tl_ih =>
    cases pf with | cons _ _ _ _ h_f_coef h_f_tl =>
    have aux : (mul.mulMonomial (cons f_deg f_coef f_tl) g_coef g_deg).hasDepth (m + 1) := by
      simp [mul.mulMonomial, hasDepth]
      constructor
      · cases h_g_coef with
        | nil => cases f_coef <;> (unfold mul; constructor)
        | const => cases f_coef <;> (unfold mul; constructor)
        | cons _ g_coef_deg g_coef_coef g_coef_tl h_g_coef_coef h_g_coef_tl =>
          exact (f_coef_ih g_coef_coef g_coef_deg g_coef_tl _ h_g_coef_coef h_g_coef_tl h_f_coef).left
      · simp only [Thunk.get_mk]
        exact (f_tl_ih g_coef g_deg g_tl _ h_g_coef h_g_tl h_f_tl).right
    constructor
    · simp only [mul]
      apply PreMS.add_preserve_depth
      · exact aux
      · generalize g_tl.get = tlg at *
        induction tlg using PreMS.rec' with
        | const => cases h_g_tl
        | cons g_tl_deg g_tl_coef g_tl_tl g_tl_coef_ih g_tl_tl_ih =>
          unfold mul
          apply PreMS.add_preserve_depth
          · simp only [mul.mulMonomial]
            constructor
            · cases h_g_tl with | cons _ _ _ _ h_g_tl_coef h_g_tl_tl =>
              cases h_g_tl_coef with
              | cons _ g_tl_coef_deg g_tl_coef_coef g_tl_coef_tl h_g_tl_coef_coef h_g_tl_coef_tl =>
                exact (f_coef_ih g_tl_coef_coef g_tl_coef_deg g_tl_coef_tl _ h_g_tl_coef_coef h_g_tl_coef_tl h_f_coef).left
              | const => cases f_coef <;> (unfold mul; constructor)
              | nil => cases f_coef <;> (unfold mul; constructor)
            · cases h_g_tl with | cons _ _ _ _ h_g_tl_coef h_g_tl_tl =>
              simp only [Thunk.get_mk]
              exact (f_tl_ih g_tl_coef g_tl_deg g_tl_tl _ h_g_tl_coef h_g_tl_tl h_f_tl).right
          · apply g_tl_tl_ih
            cases h_g_tl with | cons _ _ _ _ h_g_tl_coef h_g_tl_tl =>
            exact h_g_tl_tl
        | nil => unfold mul; constructor
    · exact aux
  | const c =>
    constructor
    · apply PreMS.mul_preserve_depth_aux_aux1 _ pf
      constructor <;> assumption
    · simp only [mul.mulMonomial, default]; constructor
  | nil =>
    constructor
    · apply PreMS.mul_preserve_depth_aux_aux2 _ pf
      constructor <;> assumption
    · simp only [mul.mulMonomial, default]; constructor

theorem PreMS.mul_preserve_depth {n : ℕ} {f g : PreMS} (pf : f.hasDepth n) (pg : g.hasDepth n) :
    (f.mul g).hasDepth n :=
  match g with
  | cons g_deg g_coef g_tl => (PreMS.mul_preserve_depth_aux f g_coef g_deg g_tl pf pg).left
  | const _ => by cases pf <;> (unfold mul; constructor)
  | nil => by cases pf <;> (unfold mul; constructor)

theorem PreMS.mulMonomial_preserve_depth {n : ℕ} {f m_coef : PreMS} {m_deg : ℝ}
    (pf : f.hasDepth (n + 1)) (pm : m_coef.hasDepth n) :
    (PreMS.mul.mulMonomial f m_coef m_deg).hasDepth (n + 1) := by
  have : (cons m_deg m_coef (.mk fun () => PreMS.nil)).hasDepth (n + 1) := by
    constructor
    · exact pm
    · simp only [Thunk.get_mk]
      constructor
  apply (PreMS.mul_preserve_depth_aux _ _ _ _ pf this).right

lemma PreMS.mul_preserve_wo_aux_aux1 {c : ℝ} {g : PreMS} (hg : g.wellOrdered) :
    ((PreMS.const c).mul g).wellOrdered := by
  cases g <;> simp [mul, wellOrdered]

lemma PreMS.mul_preserve_wo_aux_aux2 {g : PreMS}
    (hg : g.wellOrdered) : (PreMS.nil.mul g).wellOrdered := by
  cases g <;> simp [mul, wellOrdered]

theorem PreMS.mul_preserve_wo_aux (f g_coef : PreMS) (g_deg : ℝ) (g_tl : Thunk PreMS)
    (pf : f.wellOrdered) (pg : (PreMS.cons g_deg g_coef g_tl).wellOrdered) :
    (f.mul (PreMS.cons g_deg g_coef g_tl)).wellOrdered ∧
    (PreMS.mul.mulMonomial f g_coef g_deg).wellOrdered := by
  induction f using PreMS.rec' generalizing g_deg g_coef g_tl with
  | const c =>
    constructor
    · unfold mul
      simp [wellOrdered]
    · unfold mul.mulMonomial
      simp [wellOrdered]
  | nil =>
    constructor
    · unfold mul
      simp [wellOrdered]
    · unfold mul.mulMonomial
      simp [wellOrdered]
  | cons f_deg f_coef f_tl f_coef_ih f_tl_ih =>
    have aux : (mul.mulMonomial (cons f_deg f_coef f_tl) g_coef g_deg).wellOrdered := by
      unfold mul.mulMonomial
      simp [wellOrdered]
      simp [wellOrdered] at pf
      constructor
      · cases g_coef with
        | const => cases f_coef <;> simp [mul, wellOrdered]
        | nil => cases f_coef <;> simp [mul, wellOrdered]
        | cons g_coef_deg g_coef_coef g_coef_tl =>
          apply (f_coef_ih _ _ _ pf.left _).left
          unfold wellOrdered at pg
          exact pg.left
      · constructor
        · apply (f_tl_ih _ _ ⟨fun () => .nil⟩ pf.right.left _).right
          simp [wellOrdered]
          simp [wellOrdered] at pg
          exact pg.left
        · generalize f_tl.get = ftl at *
          cases ftl with
          | const => simp [mul.mulMonomial]
          | nil => simp [mul.mulMonomial]
          | cons f_tl_deg f_tl_coef f_tl_tl =>
            simp [mul.mulMonomial]
            simp at pf
            exact pf.right.right
    constructor
    · unfold mul
      apply PreMS.add_preserve_wo
      · exact aux
      · simp [wellOrdered] at pg
        generalize g_tl.get = gtl at *
        induction gtl using PreMS.rec' with
        | cons g_tl_deg g_tl_coef g_tl_tl g_tl_coef_ih g_tl_tl_ih => -- shameless copypaste from above
          simp [mul]
          apply PreMS.add_preserve_wo
          · unfold mul.mulMonomial
            simp [wellOrdered]
            simp [wellOrdered] at pf
            constructor
            · cases g_tl_coef with
              | const => cases f_coef <;> simp [mul, wellOrdered]
              | nil => cases f_coef <;> simp [mul, wellOrdered]
              | cons g_coef_deg g_coef_coef g_coef_tl =>
                apply (f_coef_ih _ _ _ pf.left _).left
                unfold wellOrdered at pg
                tauto
            · constructor
              · apply (f_tl_ih _ _ ⟨fun () => .nil⟩ pf.right.left _).right
                simp [wellOrdered]
                simp [wellOrdered] at pg
                tauto
              · generalize f_tl.get = ftl at *
                cases ftl with
                | const => simp [mul.mulMonomial]
                | nil => simp [mul.mulMonomial]
                | cons f_tl_deg f_tl_coef f_tl_tl =>
                  simp [mul.mulMonomial]
                  simp at pf
                  exact pf.right.right
          · apply g_tl_tl_ih
            constructor
            · exact pg.left
            · simp [wellOrdered] at pg
              constructor
              · tauto
              · generalize g_tl_tl.get = gtltl at *
                cases gtltl with
                | const => simp
                | nil => simp
                | cons =>
                  simp at pg
                  linarith
        | nil => simp [mul, wellOrdered]
        | const => simp [mul, wellOrdered]
    · exact aux

theorem PreMS.mul_preserve_wo {f g : PreMS} (pf : f.wellOrdered) (pg : g.wellOrdered) :
    (f.mul g).wellOrdered :=
  match g with
  | cons g_deg g_coef g_tl => (PreMS.mul_preserve_wo_aux f g_coef g_deg g_tl pf pg).left
  | const _ => by cases f <;> simp_all [mul, wellOrdered, default]
  | nil => by cases f <;> simp [mul, wellOrdered, default]

lemma PreMS.mul_F_aux_mul_const {c : ℝ} {f : PreMS} {F G : ℝ → ℝ} {basis : Basis}
    (hf_approx : f.isApproximation F basis)
    (hf_depth : f.hasDepth basis.length)
    (hg_approx : (PreMS.const c).isApproximation G basis) :
    (f.mul (PreMS.const c)).isApproximation (F * G) basis := by
  cases hg_approx with | const _ _ hG =>
  cases hf_approx with
  | nil _ _ hF =>
    unfold mul
    constructor
    trans 0 * G
    · apply Filter.EventuallyEq.mul hF (by rfl)
    · simp
  | const _ _ hF =>
    unfold mul
    constructor
    apply Filter.EventuallyEq.mul hF hG

lemma PreMS.mul_F_aux_mul_nil {f : PreMS} {F G : ℝ → ℝ} {basis : Basis}
    (hf_approx : f.isApproximation F basis)
    (hg_approx : PreMS.nil.isApproximation G basis) :
    (f.mul PreMS.nil).isApproximation (F * G) basis := by
  cases hg_approx with | nil _ _ hG =>
  cases hf_approx <;> {
    unfold mul
    constructor
    trans F * 0
    · apply Filter.EventuallyEq.mul (by rfl) hG
    · simp
  }

lemma PreMS.mul_F_aux_const_mul {c : ℝ} {g : PreMS} {F G : ℝ → ℝ} {basis : Basis}
    (hf_approx : (PreMS.const c).isApproximation F basis)
    (hg_approx : g.isApproximation G basis) :
    ((PreMS.const c).mul g).isApproximation (F * G) basis := by
  cases hf_approx with | const _ _ h_F =>
  cases hg_approx with
  | const _ _ h_G =>
    unfold mul
    constructor
    exact Filter.EventuallyEq.mul h_F h_G
  | nil _ _ h_G =>
    unfold mul
    constructor
    conv in 0 =>
      ext
      simp
      rw [← mul_zero c]
    exact Filter.EventuallyEq.mul h_F h_G

lemma PreMS.mul_F_aux_nil_mul {g : PreMS} {F G : ℝ → ℝ} {basis : Basis}
    (hf_approx : PreMS.nil.isApproximation F basis)
    (hg_approx : g.isApproximation G basis) :
    (PreMS.nil.mul g).isApproximation (F * G) basis := by
  cases hf_approx with | nil _ _ h_F =>
  cases hg_approx <;> {
    unfold mul
    constructor
    conv in 0 =>
      ext x
      simp
      rw [← zero_mul (G x)]
    exact Filter.EventuallyEq.mul h_F (Filter.EventuallyEq.refl _ G)
  }

inductive PreMS.mul_F_aux_mulm_wf : PreMS → PreMS → (ℝ → ℝ) → Basis → Prop
| const (f : PreMS) (F : ℝ → ℝ) (basis : Basis) (c : ℝ) : PreMS.mul_F_aux_mulm_wf f (PreMS.const c) F basis
| nil (f : PreMS) (F : ℝ → ℝ) (basis : Basis) : PreMS.mul_F_aux_mulm_wf f PreMS.nil F basis
| cons (f : PreMS) (F : ℝ → ℝ) (g_deg : ℝ) (g_coef : PreMS) (g_tl : Thunk PreMS) (G GC basis_hd : ℝ → ℝ)
    (basis_tl : Basis) (h_g_coef : g_coef.isApproximation GC basis_tl)
    (h_g_tl : g_tl.get.isApproximation (fun x ↦ (G x) - (basis_hd x)^g_deg * (GC x)) (basis_hd :: basis_tl))
    (h_g_comp : (∀ deg', g_deg < deg' → G =o[Filter.atTop] (fun x => (basis_hd x)^deg')))
    (h : (PreMS.mul.mulMonomial f g_coef g_deg).isApproximation (fun x ↦ (F x) * (basis_hd x)^g_deg * (GC x)) (basis_hd :: basis_tl))
    : PreMS.mul_F_aux_mulm_wf f (PreMS.cons g_deg g_coef g_tl) F (basis_hd :: basis_tl)

-- lemma PreMS.mul_F_aux_mulm_nil {f : PreMS} {m_deg : ℝ} {F M basis_hd : ℝ → ℝ} {basis_tl : Basis}
--     (hf_approx : f.isApproximation F (basis_hd :: basis_tl))
--     (hm_approx : PreMS.nil.isApproximation M basis_tl) :
--     (PreMS.mul.mulMonomial f PreMS.nil m_deg).isApproximation (fun x ↦ (F x) * (basis_hd x) ^ m_deg * M x) (basis_hd :: basis_tl) := by
--   cases hm_approx with | nil _ _ hM =>
--   apply PreMS.isApproximation_of_EventuallyEq (F := 0)
--   · induction f using PreMS.rec' generalizing F with
--     | const => cases hf_approx
--     | nil =>
--       cases hf_approx with | nil _ _ hF =>
--       unfold mul.mulMonomial
--       constructor
--       rfl
--     | cons f_deg f_coef f_tl f_coef_ih f_tl_ih =>
--       cases hf_approx with | cons _ _ _ _ C _ _ h_f_coef h_f_tl h_f_comp =>
--       unfold mul.mulMonomial
--       constructor
--       · cases f_coef <;> (unfold mul; constructor; rfl)
--       · simp
--         apply f_tl_ih h_f_tl
--       · intros
--         apply Asymptotics.isLittleO_zero
--   · symm
--     trans (fun x ↦ F x * basis_hd x ^ m_deg) * 0
--     · apply Filter.EventuallyEq.mul (by rfl) hM
--     · simp

-- lemma PreMS.mul_F_aux_mulm_const {f : PreMS} {mc m_deg : ℝ} {F M basis_hd : ℝ → ℝ} {basis_tl : Basis}
--     (hf_approx : f.isApproximation F (basis_hd :: basis_tl))
--     (hf_depth : f.hasDepth (basis_hd :: basis_tl).length)
--     (hm_approx : (PreMS.const mc).isApproximation M basis_tl)
--     (h_basis : MS.wellOrderedBasis (basis_hd :: basis_tl)) :
--     (PreMS.mul.mulMonomial f (PreMS.const mc) m_deg).isApproximation (fun x ↦ (F x) * (basis_hd x)^m_deg * M x) (basis_hd :: basis_tl) := by
--   cases hm_approx with | const _ _ hM =>
--   apply PreMS.isApproximation_of_EventuallyEq (F := (fun x ↦ F x * basis_hd x ^ m_deg * mc))
--   · induction f using PreMS.rec' generalizing F with
--     | const => cases hf_approx
--     | nil =>
--       cases hf_approx with | nil _ _ hF =>
--       unfold mul.mulMonomial
--       constructor
--       trans 0 * (fun x ↦ basis_hd x ^ m_deg * mc)
--       · simp_rw [mul_assoc]
--         apply Filter.EventuallyEq.mul hF (by rfl)
--       · simp
--     | cons f_deg f_coef f_tl f_coef_ih f_tl_ih =>
--       cases hf_approx with | cons _ _ _ _ C _ _ h_f_coef h_f_tl h_f_comp =>
--       cases hf_depth with | cons _ _ _ _ h_f_coef_depth h_f_tl_depth =>
--       have basis_hd_tendsto_top : Filter.Tendsto basis_hd Filter.atTop Filter.atTop := by
--         apply MS.basis_tendsto_top h_basis
--         simp
--       cases h_f_coef_depth with
--       | const c =>
--         cases h_f_coef with | const _ _ hC =>
--         unfold mul.mulMonomial mul
--         constructor
--         · apply PreMS.isApproximation.const; rfl
--         · simp only [Thunk.get_mk]
--           apply PreMS.isApproximation_of_EventuallyEq (F := fun x ↦ (F x - basis_hd x ^ f_deg * C x) * basis_hd x ^ m_deg * mc)
--           · apply f_tl_ih
--             · simpa
--             · simpa
--           · simp only [Filter.EventuallyEq]
--             apply Filter.Eventually.mono <| (Filter.Tendsto.eventually_gt_atTop basis_hd_tendsto_top 0).and hC
--             rintro x ⟨hx, hC⟩
--             rw [Real.rpow_add hx, hC]
--             ring_nf
--         · intro deg h_deg
--           conv =>
--             arg 2
--             ext x
--             rw [show F x * basis_hd x ^ m_deg * mc = mc * F x * basis_hd x ^ m_deg by ring_nf]
--           let ε := (deg - (f_deg + m_deg)) / 2
--           have h1 : (fun x ↦ mc * F x) =o[Filter.atTop] fun x ↦ basis_hd x ^ (f_deg + ε) := by
--             apply Asymptotics.IsLittleO.const_mul_left
--             apply h_f_comp
--             dsimp only [ε]; linarith
--           have h2 : (fun x ↦ basis_hd x ^ m_deg)  =o[Filter.atTop] fun x ↦ basis_hd x ^ (m_deg + ε) := by
--             apply MS.compare_self
--             apply basis_hd_tendsto_top
--             dsimp only [ε]
--             linarith
--           apply Asymptotics.IsLittleO.trans_eventuallyEq (h1.mul h2)
--           simp only [Filter.EventuallyEq]
--           apply Filter.Eventually.mono (Filter.Tendsto.eventually_gt_atTop basis_hd_tendsto_top 0)
--           intro x hx
--           simp only [← Real.rpow_add hx, ε]
--           ring_nf
--       | nil => -- copypaste from above
--         cases h_f_coef with | nil _ _ hC =>
--         unfold mul.mulMonomial mul
--         constructor
--         · apply PreMS.isApproximation.nil; rfl
--         · simp only [Thunk.get_mk]
--           apply PreMS.isApproximation_of_EventuallyEq (F := fun x ↦ (F x - basis_hd x ^ f_deg * C x) * basis_hd x ^ m_deg * mc)
--           · apply f_tl_ih
--             · simpa
--             · simpa
--           · simp only [Filter.EventuallyEq]
--             apply Filter.Eventually.mono <| (Filter.Tendsto.eventually_gt_atTop basis_hd_tendsto_top 0).and hC
--             rintro x ⟨hx, hC⟩
--             rw [Real.rpow_add hx, hC]
--             simp
--         · intro deg h_deg
--           conv =>
--             arg 2
--             ext x
--             rw [show F x * basis_hd x ^ m_deg * mc = mc * F x * basis_hd x ^ m_deg by ring_nf]
--           let ε := (deg - (f_deg + m_deg)) / 2
--           have h1 : (fun x ↦ mc * F x) =o[Filter.atTop] fun x ↦ basis_hd x ^ (f_deg + ε) := by
--             apply Asymptotics.IsLittleO.const_mul_left
--             apply h_f_comp
--             dsimp only [ε]; linarith
--           have h2 : (fun x ↦ basis_hd x ^ m_deg)  =o[Filter.atTop] fun x ↦ basis_hd x ^ (m_deg + ε) := by
--             apply MS.compare_self
--             apply basis_hd_tendsto_top
--             dsimp only [ε]
--             linarith
--           apply Asymptotics.IsLittleO.trans_eventuallyEq (h1.mul h2)
--           simp only [Filter.EventuallyEq]
--           apply Filter.Eventually.mono (Filter.Tendsto.eventually_gt_atTop basis_hd_tendsto_top 0)
--           intro x hx
--           simp only [← Real.rpow_add hx, ε]
--           ring_nf
--   · symm
--     trans (fun x ↦ F x * basis_hd x ^ m_deg) * (fun _ ↦ mc)
--     · apply Filter.EventuallyEq.mul (by rfl) hM
--     · eta_expand; simp

lemma PreMS.mul_F_aux_nil_mulm {g : PreMS} {F G : ℝ → ℝ} {basis : Basis}
    (hf_approx : PreMS.nil.isApproximation F basis)
    (hg_approx : g.isApproximation G basis) :
    PreMS.mul_F_aux_mulm_wf PreMS.nil g F basis := by
  cases g with
  | nil => constructor
  | const => constructor
  | cons g_deg g_coef g_tl =>
    cases hf_approx with | nil _ _ hF =>
    cases hg_approx with | cons _ _ _ _ GC basis_hd basis_tl h_g_coef h_g_tl h_g_comp =>
    focus
    constructor
    · exact h_g_coef
    · exact h_g_tl
    · exact h_g_comp
    · unfold mul.mulMonomial
      constructor
      trans 0 * (fun x ↦ basis_hd x ^ g_deg * GC x)
      · simp_rw [mul_assoc]
        apply Filter.EventuallyEq.mul hF (by rfl)
      · simp

lemma PreMS.mul_F_aux_const_mulm {c : ℝ} {g : PreMS} {F G : ℝ → ℝ} {basis : Basis}
    (hf_approx : (PreMS.const c).isApproximation F basis)
    (hg_approx : g.isApproximation G basis) :
    PreMS.mul_F_aux_mulm_wf (PreMS.const c) g F basis := by
  cases g with
  | nil => constructor
  | const => constructor
  | cons g_deg g_coef g_tl =>
    cases hf_approx
    cases hg_approx

lemma PreMS.mul_F_aux {f g : PreMS} {F G : ℝ → ℝ} {basis : Basis} (h_basis : MS.wellOrderedBasis basis)
    (hf_depth : f.hasDepth basis.length)
    (hg_depth : g.hasDepth basis.length)
    (hf_approx : f.isApproximation F basis)
    (hg_approx : g.isApproximation G basis) :
    (f.mul g).isApproximation (F * G) basis ∧
    PreMS.mul_F_aux_mulm_wf f g F basis:= by
  induction f using PreMS.rec' generalizing g F G basis with
  | const =>
    constructor
    · exact PreMS.mul_F_aux_const_mul hf_approx hg_approx
    · exact PreMS.mul_F_aux_const_mulm hf_approx hg_approx
  | nil => -- copypaste
    constructor
    · exact PreMS.mul_F_aux_nil_mul hf_approx hg_approx
    · exact PreMS.mul_F_aux_nil_mulm hf_approx hg_approx
  | cons f_deg f_coef f_tl f_coef_ih f_tl_ih =>
    cases h_hf_approx : hf_approx with | cons _ _ _ _ FC basis_hd basis_tl h_f_coef h_f_tl h_f_comp =>
    cases h_hf_depth : hf_depth with | cons _ _ _ _ h_f_coef_depth h_f_tl_depth =>
    induction g using PreMS.rec' generalizing F G with
    | const =>
      constructor
      · exact PreMS.mul_F_aux_mul_const hf_approx hf_depth hg_approx
      · constructor
    | nil =>
      constructor
      · exact PreMS.mul_F_aux_mul_nil hf_approx hg_approx
      · constructor
    | cons g_deg g_coef g_tl g_coef_ih g_tl_ih =>
      cases h_hg_approx : hg_approx with | cons _ _ _ _ GC _ _ h_g_coef h_g_tl h_g_comp =>
      cases h_hg_depth : hg_depth with | cons _ _ _ _ h_g_coef_depth h_g_tl_depth =>
      have aux : (mul.mulMonomial (cons f_deg f_coef f_tl) g_coef g_deg).isApproximation (fun x ↦ F x * basis_hd x ^ g_deg * GC x)
          (basis_hd :: basis_tl) := by
        unfold mul.mulMonomial
        constructor
        · apply (f_coef_ih _ _ _ h_f_coef h_g_coef).left
          · unfold MS.wellOrderedBasis at h_basis; tauto
          · simpa
          · simpa
        · simp only [Thunk.get_mk, Pi.mul_apply]
          have := (f_tl_ih h_basis h_f_tl_depth hg_depth h_f_tl hg_approx).right
          cases this with | cons _ _ _ _ _ GC' _ _ h_g_coef' _ _ h_g_mulm =>
          conv at h_g_mulm =>
            arg 2
            eta_expand
            simp
          apply PreMS.isApproximation_of_EventuallyEq (F := (fun x ↦ (F x - basis_hd x ^ f_deg * FC x) * basis_hd x ^ g_deg * GC' x))
          · exact h_g_mulm
          · simp only [Filter.EventuallyEq]
            apply Filter.Eventually.mono <| (MS.basis_head_eventually_pos h_basis).and (PreMS.EventuallyEq_of_isApproximation h_g_coef' h_g_coef)
            intro x ⟨hx, hC⟩
            rw [hC, Real.rpow_add hx]
            ring_nf
        · intro deg h_deg
          let ε := (deg - (f_deg + g_deg)) / 3
          have h1 : F =o[Filter.atTop] fun x ↦ basis_hd x ^ (f_deg + ε) := by
            apply h_f_comp
            dsimp only [ε]; linarith
          have h2 : (fun x ↦ basis_hd x ^ g_deg)  =o[Filter.atTop] fun x ↦ basis_hd x ^ (g_deg + ε) := by
            apply MS.compare_self
            apply MS.basis_tendsto_top h_basis
            · simp
            · dsimp only [ε]; linarith
          have h3 : GC =o[Filter.atTop] fun x ↦ basis_hd x ^ ε := by
            apply PreMS.isApproximation_coef_isLittleO_head _ h_g_coef h_basis
            dsimp only [ε]; linarith
          apply Asymptotics.IsLittleO.trans_eventuallyEq <| (h1.mul h2).mul h3
          simp only [Filter.EventuallyEq]
          apply Filter.Eventually.mono (MS.basis_head_eventually_pos h_basis)
          intro x hx
          simp only [← Real.rpow_add hx, ε]
          ring_nf
      constructor
      · unfold mul
        conv in F * G =>
          ext x
          simp
          rw [show F x * G x = (F x) * (basis_hd x)^g_deg * (GC x) + (F x) * ((G x) - (basis_hd x)^g_deg * (GC x)) by ring_nf]
        apply PreMS.add_F
        · exact PreMS.mulMonomial_preserve_depth hf_depth h_g_coef_depth
        · exact PreMS.mul_preserve_depth hf_depth h_g_tl_depth
        · exact aux
        · apply (g_tl_ih h_f_comp h_f_tl _ hf_approx h_g_tl _).left
          · simpa
          · rfl
      · constructor
        · exact h_g_coef
        · exact h_g_tl
        · exact h_g_comp
        · exact aux

theorem PreMS.mul_F {f g : PreMS} {F G : ℝ → ℝ} {basis : Basis} (h_basis : MS.wellOrderedBasis basis)
    (hf_depth : f.hasDepth basis.length) (hg_depth : g.hasDepth basis.length)
    (hf_approx : f.isApproximation F basis) (hg_approx : g.isApproximation G basis) :
    (f.mul g).isApproximation (F * G) basis :=
  (PreMS.mul_F_aux h_basis hf_depth hg_depth hf_approx hg_approx).left

noncomputable def MS.mul (f g : MS) (h_basis : MS.wellOrderedBasis f.basis)
    (h_basis_eq : f.basis = g.basis) : MS where
  val := f.val.mul g.val
  basis := f.basis
  F := fun x ↦ (f.F x) * (g.F x)
  h_depth := PreMS.mul_preserve_depth f.h_depth (h_basis_eq ▸ g.h_depth)
  h_wo := PreMS.mul_preserve_wo f.h_wo g.h_wo
  h_approx := PreMS.mul_F h_basis f.h_depth (h_basis_eq ▸ g.h_depth) f.h_approx (h_basis_eq ▸ g.h_approx)

/-
(x + 1) * y^2 + (x^2 + 3) * y
  *
(x + 2) * y + (x - 2) * y^0
  =
mulMonomial
  (x + 1) * y^2 + (x^2 + 3) * y
  (x + 2) 1
+ (x + 1) * y^2 + (x^2 + 3) * y
  * (x - 2) * y^0
  =
  .cons y^3 ((x + 1) * (x + 2)) <|


+ (x + 1) * y^2 + (x^2 + 3) * y
  * (x - 2) * y^0


-/

end TendstoTactic
