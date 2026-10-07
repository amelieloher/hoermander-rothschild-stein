-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousKernelBound
public import RothschildStein.G2.LocalPower

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- A continuous punctured homogeneous kernel of degree
strictly greater than −Q is locally integrable on the entire carrier. -/
theorem locallyIntegrable_homogeneousKernel
    {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ) {β : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    (hβ : -(G.homogeneousDimension : ℝ) < β) : LocallyIntegrable f volume := by
  obtain ⟨C, hC, hb⟩ := exists_homogeneousKernel_gauge_bound G hν hf hhom
  have hp : LocallyIntegrable (fun x => (ν x) ^ β) volume := by
    simpa only [neg_neg] using (G2.locallyIntegrable_power_iff hν (-β)).mpr (by linarith)
  have hd : LocallyIntegrable (fun x => C * (ν x) ^ β + ‖f 0‖) volume :=
    (hp.smul C).add (locallyIntegrable_const ‖f 0‖)
  apply hd.mono (hf.stronglyMeasurable_of_countable_compl (by simp)).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  have hn : 0 ≤ C * (ν x) ^ β := mul_nonneg hC (Real.rpow_nonneg (hν.2.1 x) _)
  rw [Real.norm_of_nonneg (add_nonneg hn (norm_nonneg (f 0)))]
  by_cases hx : x = 0
  · subst x
    exact le_add_of_nonneg_left hn
  · exact (hb x hx).trans (le_add_of_nonneg_right (norm_nonneg _))

end RothschildStein.H1
