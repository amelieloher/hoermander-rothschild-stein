-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.P2.NormTransferFubini

/-!
# Analysis of the fiber integral

For a smooth compactly supported `Φ` on `ℝⁿ⁺ᵐ`, the fiber integral `x ↦ ∫ Φ(x, t) dt` has line
derivative `∫ (∂_v Φ)(x, t) dt` in a base direction `v`, and the integral of a derivative in a
vertical direction vanishes (BB p. 584, the vertical divergences integrate to zero).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.P2
variable {n m : ℕ}

/-- A base direction `v ∈ ℝⁿ` as a direction of `ℝⁿ⁺ᵐ`. -/
def baseDir (v : Fin n → ℝ) : Fin (n + m) → ℝ := joinPoint v (0 : Fin m → ℝ)

/-- A vertical direction `w ∈ ℝᵐ` as a direction of `ℝⁿ⁺ᵐ`. -/
def vertDir (w : Fin m → ℝ) : Fin (n + m) → ℝ := joinPoint (0 : Fin n → ℝ) w

theorem joinPoint_add_baseDir (x v : Fin n → ℝ) (t : Fin m → ℝ) (s : ℝ) :
    joinPoint (x + s • v) t = joinPoint x t + s • baseDir (m := m) v := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun l => ?_) i
  · simp [joinPoint, baseDir]
  · simp [joinPoint, baseDir]

theorem joinPoint_add_vertDir (x : Fin n → ℝ) (t w : Fin m → ℝ) (s : ℝ) :
    joinPoint x (t + s • w) = joinPoint x t + s • vertDir (n := n) w := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun l => ?_) i
  · simp [joinPoint, vertDir]
  · simp [joinPoint, vertDir]

theorem continuous_joinPoint_right (x : Fin n → ℝ) :
    Continuous (fun t : Fin m → ℝ => joinPoint x t) :=
  continuous_joinPoint.comp (Continuous.prodMk continuous_const continuous_id)

theorem continuous_joinPoint_left (t : Fin m → ℝ) :
    Continuous (fun x : Fin n → ℝ => joinPoint x t) :=
  continuous_joinPoint.comp (Continuous.prodMk continuous_id continuous_const)

theorem continuous_tailPoint : Continuous (tailPoint : (Fin (n + m) → ℝ) → Fin m → ℝ) :=
  continuous_pi fun _ => continuous_apply _

/-- Every slice of a compactly supported function has compact support. -/
theorem hasCompactSupport_slice {Φ : (Fin (n + m) → ℝ) → ℝ} (hc : HasCompactSupport Φ)
    (x : Fin n → ℝ) : HasCompactSupport (fun t : Fin m → ℝ => Φ (joinPoint x t)) := by
  apply HasCompactSupport.intro (K := tailPoint '' tsupport Φ)
    (hc.image continuous_tailPoint)
  intro t ht
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact ht ⟨joinPoint x t, hmem, tailPoint_joinPoint x t⟩

/-- The projection of the support of a compactly supported function is compact. -/
theorem isCompact_basePoint_image {Φ : (Fin (n + m) → ℝ) → ℝ} (hc : HasCompactSupport Φ) :
    IsCompact (basePoint '' tsupport Φ) :=
  hc.image continuous_basePoint

/-- The chain rule along a line. -/
theorem hasDerivAt_comp_line {Φ : (Fin (n + m) → ℝ) → ℝ} (hΦ : Differentiable ℝ Φ)
    (a v : Fin (n + m) → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Φ (a + s • v)) (fderiv ℝ Φ (a + s • v) v) s := by
  have h1 : HasDerivAt (fun s : ℝ => a + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add a
  exact (hΦ (a + s • v)).hasFDerivAt.comp_hasDerivAt s h1

/-- Differentiation of the fiber integral in a base direction. -/
theorem hasDerivAt_fiberAvg {Φ : (Fin (n + m) → ℝ) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hc : HasCompactSupport Φ) (x v : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => ∫ t : Fin m → ℝ, Φ (joinPoint (x + s • v) t))
      (∫ t : Fin m → ℝ, fderiv ℝ Φ (joinPoint x t) (baseDir (m := m) v)) 0 := by
  have hdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hfd : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv (by simp)
  have hfdc : HasCompactSupport (fderiv ℝ Φ) := hc.fderiv ℝ
  obtain ⟨C, hC⟩ := (hfdc.exists_bound_of_continuous hfd)
  set K : Set (Fin m → ℝ) := tailPoint '' tsupport Φ with hK
  have hKc : IsCompact K := hc.image continuous_tailPoint
  set B : ℝ := C * ‖baseDir (m := m) v‖ with hB
  have hbound : Integrable (K.indicator (fun _ : Fin m → ℝ => B)) volume :=
    (integrable_indicator_iff hKc.measurableSet).2
      (integrableOn_const hKc.measure_lt_top.ne)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Fin m → ℝ)))
    (F := fun (s : ℝ) (t : Fin m → ℝ) => Φ (joinPoint (x + s • v) t))
    (F' := fun (s : ℝ) (t : Fin m → ℝ) =>
      fderiv ℝ Φ (joinPoint (x + s • v) t) (baseDir (m := m) v))
    (s := univ) (x₀ := 0) (bound := K.indicator (fun _ => B)) univ_mem ?_ ?_ ?_ ?_ hbound ?_
  · simpa using key.2
  · refine Eventually.of_forall fun s => ?_
    exact (hΦ.continuous.comp (continuous_joinPoint_right _)).aestronglyMeasurable
  · exact (hΦ.continuous.comp (continuous_joinPoint_right _)).integrable_of_hasCompactSupport
      (hasCompactSupport_slice hc _)
  · exact ((hfd.comp (continuous_joinPoint_right _)).clm_apply continuous_const).aestronglyMeasurable
  · refine Eventually.of_forall fun t s _ => ?_
    by_cases ht : t ∈ K
    · rw [indicator_of_mem ht]
      calc ‖fderiv ℝ Φ (joinPoint (x + s • v) t) (baseDir (m := m) v)‖
          ≤ ‖fderiv ℝ Φ (joinPoint (x + s • v) t)‖ * ‖baseDir (m := m) v‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ C * ‖baseDir (m := m) v‖ := by gcongr; exact hC _
    · rw [indicator_of_notMem ht]
      have : fderiv ℝ Φ (joinPoint (x + s • v) t) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        exact ht ⟨_, (tsupport_fderiv_subset ℝ) hmem, tailPoint_joinPoint _ t⟩
      simp [this]
  · refine Eventually.of_forall fun t s _ => ?_
    have := hasDerivAt_comp_line hdiff (joinPoint x t) (baseDir (m := m) v) s
    simpa [joinPoint_add_baseDir] using this

/-- The fiber integral of a smooth compactly supported function has the base line derivative
`∫ ∂_v Φ`. -/
theorem lineDeriv_fiberAvg {Φ : (Fin (n + m) → ℝ) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hc : HasCompactSupport Φ) (x v : Fin n → ℝ) :
    lineDeriv ℝ (fun y : Fin n → ℝ => ∫ t : Fin m → ℝ, Φ (joinPoint y t)) x v =
      ∫ t : Fin m → ℝ, fderiv ℝ Φ (joinPoint x t) (baseDir (m := m) v) :=
  (hasDerivAt_fiberAvg hΦ hc x v).deriv

/-- Vertical derivatives integrate to zero over the fiber. -/
theorem integral_fderiv_vertical {Φ : (Fin (n + m) → ℝ) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hc : HasCompactSupport Φ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    ∫ t : Fin m → ℝ, fderiv ℝ Φ (joinPoint x t) (vertDir (n := n) w) = 0 := by
  have hdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hfd : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv (by simp)
  have hfdc : HasCompactSupport (fderiv ℝ Φ) := hc.fderiv ℝ
  set g : (Fin m → ℝ) → ℝ := fun t => Φ (joinPoint x t) with hg
  have hgl : ∀ t, HasLineDerivAt ℝ g (fderiv ℝ Φ (joinPoint x t) (vertDir (n := n) w)) t w := by
    intro t
    have := hasDerivAt_comp_line hdiff (joinPoint x t) (vertDir (n := n) w) 0
    simpa [HasLineDerivAt, hg, joinPoint_add_vertDir] using this
  have hgc : Continuous g := hΦ.continuous.comp (continuous_joinPoint_right x)
  have hgs : HasCompactSupport g := hasCompactSupport_slice hc x
  have hg'c : Continuous (fun t : Fin m → ℝ => fderiv ℝ Φ (joinPoint x t) (vertDir (n := n) w)) :=
    (hfd.comp (continuous_joinPoint_right x)).clm_apply continuous_const
  have hg's : HasCompactSupport
      (fun t : Fin m → ℝ => fderiv ℝ Φ (joinPoint x t) (vertDir (n := n) w)) := by
    apply HasCompactSupport.intro (K := tailPoint '' tsupport Φ) (hc.image continuous_tailPoint)
    intro t ht
    have : fderiv ℝ Φ (joinPoint x t) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact ht ⟨_, (tsupport_fderiv_subset ℝ) hmem, tailPoint_joinPoint _ t⟩
    simp [this]
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin m → ℝ))) (f := fun _ : Fin m → ℝ => (1 : ℝ))
    (f' := fun _ => (0 : ℝ)) (g := g)
    (g' := fun t => fderiv ℝ Φ (joinPoint x t) (vertDir (n := n) w)) (v := w)
    (B := ContinuousLinearMap.mul ℝ ℝ) ?_ ?_ ?_ ?_ (fun t _ => hgl t)
  · simpa using key
  · simp
  · simpa using hg'c.integrable_of_hasCompactSupport hg's
  · simpa using hgc.integrable_of_hasCompactSupport hgs
  · intro t _
    exact (hasDerivAt_const (0 : ℝ) (1 : ℝ))

end RothschildStein.P2
