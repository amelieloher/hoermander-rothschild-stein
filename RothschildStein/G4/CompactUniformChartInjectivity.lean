-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ReferenceNeighborhoodsFromActualDerivatives

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology

namespace RothschildStein.G4

/-- Compact uniform shifted-chart injectivity follows from the chart data
and continuity of their derivatives. Reference Jacobians and neighborhoods
are constructed, and injectivity transfers along finite chains and auxiliary
shifts (BB pp. 450–458). -/
theorem exists_compact_uniform_chart_injectivity_of_actual_derivative_continuity
    {P : Type*} [TopologicalSpace P] {m n s : ℕ} {K : Set P} (hK : IsCompact K)
    (w : Fin m → ℕ+) (hw : ∀ J, (w J : ℕ) ≤ s)
    (Z : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ))
    (hZ : ∀ p ∈ K, ∀ J, ContinuousOn (Z p J) Ω)
    (F : P → (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (Γ : P → (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (x : P → (Fin n → ℝ)) {a D κ t : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D)
    (hκ : 0 ≤ κ) (hsmall : (n : ℝ) * κ ≤ 1 / 4) (ht : 0 < t) (ht1 : t < 1)
    (hdata : ∀ p ∈ K, ∀ B r, 0 < r → r ≤ 1 → IsSuboptimal (Z p) w B (x p) t r →
      ∀ v ∈ weightedBox w (a * r),
        ChartAnalyticBounds Ω w (Z p) B (F p B v) (weightedBox (w ∘ B) (a * r)) r κ D ∧
        ChartTrajectories Ω (Z p) B (F p B v) (weightedBox (w ∘ B) (a * r)) (x p) v (Γ p B v) ∧
        (v = 0 → F p B v 0 = x p))
    (hZevaluated : ∀ J, Continuous (fun p => Z p J (x p)))
    (hspan : ∀ p ∈ K, ∃ B : Fin n → Fin m, frameDet (Z p) B (x p) ≠ 0)
    (hlocal : ∀ p ∈ K, ∀ B : Fin n → Fin m,
      ∀ᶠ q : (Fin n → ℝ) × P in 𝓝 (0, p), DifferentiableAt ℝ (F q.2 B 0) q.1)
    (hder : ∀ p ∈ K, ∀ B : Fin n → Fin m,
      ContinuousAt (fun q : (Fin n → ℝ) × P => fderiv ℝ (F q.2 B 0) q.1) (0, p)) :
    ∃ r₀ c : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < c ∧ c ≤ a ∧
      ∀ p ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B, IsSuboptimal (Z p) w B (x p) t r →
      ∀ v ∈ weightedBox w (c * r), InjOn (F p B v) (weightedBox (w ∘ B) (c * r)) := by
  have hjac : ∀ p ∈ K, ∀ B R, 0 < R → R ≤ 1 → IsSuboptimal (Z p) w B (x p) 1 R →
      Matrix.det (coordinateDerivativeMatrix (fderiv ℝ (F p B 0) 0)) ≠ 0 := by
    intro p hp B R hR hR1 hopt
    have hsub : IsSuboptimal (Z p) w B (x p) t R := by
      intro C
      exact (mul_le_of_le_one_left
        (mul_nonneg (abs_nonneg _) (zpow_nonneg hR.le _)) ht1.le).trans
        (by simpa only [one_mul] using hopt C)
    have hvzero : (0 : Fin m → ℝ) ∈ weightedBox w (a * R) := by
      intro J
      simp only [Pi.zero_apply, abs_zero]
      exact pow_pos (mul_pos ha hR) _
    have huzero : (0 : Fin n → ℝ) ∈ weightedBox (w ∘ B) (a * R) := by
      intro i
      simp only [Pi.zero_apply, abs_zero]
      exact pow_pos (mul_pos ha hR) _
    exact (hdata p hp B R hR hR1 hsub 0 hvzero).1.2.2.1 0 huzero
  have href := referenceChartNeighborhoods_of_actual_derivative_continuity w Z F x ht ht1
    hZevaluated hspan hlocal hder hjac
  exact exists_compact_uniform_chart_injectivity_of_reference_neighborhoods hK w hw Z Ω hZ
    F Γ x ha ha1 hD hκ hsmall ht.le ht1.le hdata href

end RothschildStein.G4
