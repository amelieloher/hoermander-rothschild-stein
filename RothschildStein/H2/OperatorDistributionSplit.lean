-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.Marcinkiewicz
public import RothschildStein.H2.WeakTail

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Split the operator distribution into its good part, the
exceptional set, and the bad part outside that set. -/
theorem operator_distribution_split (μ : Measure X)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hb : MemLp (fun x => f x - g x) 2 μ)
    (E : Set X) (hE : MeasurableSet E) (α : ℝ) :
    distribution μ (fun x => (T (hf.toLp f)) x) α ≤
      distribution μ (fun x => (T (hg.toLp g)) x) (α / 2) +
        (μ E + distribution (μ.restrict Eᶜ)
          (fun x => (T (hb.toLp (fun x => f x - g x))) x) (α / 2)) := by
  have heq : hf.toLp f = hg.toLp g + hb.toLp (fun x => f x - g x) := by
    apply Lp.ext
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp, hb.coeFn_toLp,
      Lp.coeFn_add (hg.toLp g) (hb.toLp (fun x => f x - g x))] with x hfx hgx hbx hx
    rw [hfx, hx]
    simp only [Pi.add_apply, hgx, hbx]
    ring
  have hsub : ∀ᵐ x ∂μ, |(T (hf.toLp f)) x| ≤
      |(T (hg.toLp g)) x| + |(T (hb.toLp (fun x => f x - g x))) x| := by
    rw [heq, T.map_add]
    filter_upwards [Lp.coeFn_add (T (hg.toLp g)) (T (hb.toLp (fun x => f x - g x)))] with x hx
    rw [hx]
    exact abs_add_le _ _
  apply (distribution_add_le μ hsub α).trans
  apply add_le_add le_rfl
  have hu : (univ : Set X) \ E = Eᶜ := by ext x; simp
  simpa only [Measure.restrict_univ, hu] using distribution_restrict_le_exception μ univ E hE
    (fun x => (T (hb.toLp (fun x => f x - g x))) x) (α / 2)

end RothschildStein.H2
