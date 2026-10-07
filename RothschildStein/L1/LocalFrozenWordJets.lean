-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LocalLeadingFieldJets
public import RothschildStein.L1.LocalFlatWordJets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Constant directional differentiation preserves equality of the next
ordinary jet. This is a calculus identity, independent of field coefficients. -/
theorem constant_field_jet_eq_of_next_jet_eq_on {N k : ℕ}
    (Ω : Opens (Fin N → ℝ)) (u v : (Fin N → ℝ) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (z : Fin N → ℝ)
    (he : iteratedFDeriv ℝ (k+1) u x = iteratedFDeriv ℝ (k+1) v x) :
    iteratedFDeriv ℝ k (fieldDerivative (fun _ => z) u) x =
      iteratedFDeriv ℝ k (fieldDerivative (fun _ => z) v) x := by
  ext m
  have hdu : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ u) Ω := hu.fderiv_of_isOpen Ω.isOpen (by simp)
  have hdv : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ v) Ω := hv.fderiv_of_isOpen Ω.isOpen (by simp)
  have heu := iteratedFDerivWithin_clm_apply_const_apply Ω.isOpen.uniqueDiffOn hdu
    (i := k) (by simp) hx (u := z) (m := m)
  have hev := iteratedFDerivWithin_clm_apply_const_apply Ω.isOpen.uniqueDiffOn hdv
    (i := k) (by simp) hx (u := z) (m := m)
  simp only [iteratedFDerivWithin_of_isOpen _ Ω.isOpen hx] at heu hev
  change iteratedFDeriv ℝ k (fun y => fderiv ℝ u y z) x m =
      iteratedFDeriv ℝ k (fun y => fderiv ℝ v y z) x m
  rw [heu,hev]
  have he' := congrArg (fun A => A (Fin.snoc m z)) he
  simpa only [iteratedFDeriv_succ_apply_right,Fin.init_snoc,Fin.snoc_last] using he'

/-- Every coefficient may be evaluated at the base point in the
leading jet of an ordered field product when the lower ordinary jets vanish. -/
theorem iteratedFDeriv_wordDerivative_eq_frozen_on {a N : ℕ}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (I : List (Fin a))
    (u : (Fin N → ℝ) → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    ∀ k, (∀ j < k + I.length, iteratedFDeriv ℝ j u x = 0) →
      iteratedFDeriv ℝ k (wordDerivative X I u) x =
        iteratedFDeriv ℝ k (wordDerivative (fun i _ => X i x) I u) x := by
  induction I with
  | nil => intro k _; rfl
  | cons i I ih =>
    intro k hz
    have htail := S.contDiffOn_wordDerivative Ω X hX I u hu
    have htailf := S.contDiffOn_wordDerivative Ω (fun j _ => X j x)
      (fun _ => contDiffOn_const) I u hu
    change iteratedFDeriv ℝ k (fieldDerivative (X i) (wordDerivative X I u)) x = _
    rw [iteratedFDeriv_fieldDerivative_eq_frozen_on Ω (X i) (wordDerivative X I u) hx
      (hX i) htail (fun j hj => iteratedFDeriv_wordDerivative_zero_on Ω X hX I u hu hx
        (r := k + (i :: I).length) hz j (by simp only [List.length_cons]; omega))]
    apply constant_field_jet_eq_of_next_jet_eq_on Ω _ _ htail htailf hx (X i x)
    apply ih (k+1)
    intro j hj
    exact hz j (by simp only [List.length_cons] at *; omega)
end RothschildStein.L1
