-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.TimeOneFlow
public import RothschildStein.G4.GeneratorCalculus
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Iteration of the actual directional derivative. -/
def fieldIterates {n : ℕ} (T : (Fin n → ℝ) → (Fin n → ℝ)) :
    ℕ → ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ)
  | 0, f => f
  | j + 1, f => fieldDerivative T (fieldIterates T j f)

/-- Actual directional iteration preserves smoothness on the
original open domain. -/
theorem fieldIterates_contDiffOn {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {T : (Fin n → ℝ) → (Fin n → ℝ)}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) T Ω) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fieldIterates T j f) Ω := by
  induction j with
  | zero => exact hf
  | succ j ih => exact (ih.fderiv_of_isOpen hΩ (by simp)).clm_apply hT

/-- Time derivatives of a scalar along an actual classical flow
are its directional iterates, including both endpoints of the Taylor interval. -/
theorem iteratedDerivWithin_comp_flow {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {T : (Fin n → ℝ) → (Fin n → ℝ)}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) T Ω) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {γ : ℝ → (Fin n → ℝ)} {a b : ℝ} (hab : a < b)
    (hmap : MapsTo γ (Icc a b) Ω)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (T (γ t)) t) (j : ℕ) :
    EqOn (iteratedDerivWithin j (f ∘ γ) (Icc a b))
      (fun t => fieldIterates T j f (γ t)) (Icc a b) := by
  induction j with
  | zero => intro t ht; rfl
  | succ j ih =>
    intro t ht
    rw [iteratedDerivWithin_succ]
    rw [derivWithin_congr ih (ih ht)]
    have hd := (((fieldIterates_contDiffOn hΩ hT hf j).contDiffAt
      (hΩ.mem_nhds (hmap ht))).differentiableAt (by simp)).hasFDerivAt
    exact (hd.comp_hasDerivAt t (hγ t ht)).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hab) t ht)

end RothschildStein.G4
