-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OffDiagonalL2
public import RothschildStein.H2.CancellationIntegral

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal Classical

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Off-diagonal representation and Ω₂ cancellation give the
cancelled integral over the entire bad ball, even when its centre lies
outside U (BB p. 320, using the L² off-diagonal bound). -/
theorem OffDiagonalL2.cancelled_representation (D : LocDoubling X)
    {U : Set X} (hU : MeasurableSet U) (hU₂ : U ⊆ D.Ω₂)
    {K : X → X → ℝ} {T : Lp ℝ 2 (D.μ.restrict U) →L[ℝ] Lp ℝ 2 (D.μ.restrict U)}
    (hos : OffDiagonalL2 D U K T)
    (hsupport : ∀ a b, a ∉ U ∨ b ∉ U → K a b = 0)
    {z : X} (hz : z ∈ D.Ω₁) {r : ℝ} (hr : 0 < r) (hcap : r ≤ D.κ / 5)
    (hB₂ : ball z r ⊆ D.Ω₂) (b : X → ℝ)
    (hb : IntegrableOn b D.Ω₂ D.μ) (hbU : MemLp b 2 (D.μ.restrict U))
    (hbzero : ∀ x, x ∉ ball z r → b x = 0)
    (hcancel : (∫ x in D.Ω₂, b x ∂D.μ) = 0) :
    ∀ᵐ y ∂D.μ.restrict U, y ∉ ball z (4 * r) →
      (T (hbU.toLp b)) y = ∫ x in ball z r, (K y x - K y z) * b x ∂D.μ := by
  have hvs : ∀ᵐ x ∂D.μ.restrict U, x ∉ ball z r → (hbU.toLp b) x = 0 := by
    filter_upwards [hbU.coeFn_toLp] with x hx hn
    rw [hx, hbzero x hn]
  filter_upwards [hos z hz r hr hcap (hbU.toLp b) hvs] with y hy hny
  obtain ⟨hki, hrepr⟩ := hy hny
  have hprod' : (fun x => K y x * (hbU.toLp b) x) =ᵐ[D.μ.restrict U] fun x => K y x * b x := by
    filter_upwards [hbU.coeFn_toLp] with x hx
    rw [hx]
  have hki' : IntegrableOn (fun x => K y x * b x) U D.μ := hki.congr hprod'
  have heq : U.indicator (fun x => K y x * b x) = fun x => K y x * b x := by
    funext x
    by_cases hx : x ∈ U
    · exact indicator_of_mem hx _
    · simp [hx, hsupport y x (Or.inr hx)]
  have hkg : Integrable (fun x => K y x * b x) D.μ := by
    rw [← heq]
    exact hki'.integrable_indicator hU
  have hkg₂ : IntegrableOn (fun x => K y x * b x) D.Ω₂ D.μ := hkg.restrict
  calc
    _ = ∫ x in U, K y x * b x ∂D.μ := hrepr.trans (integral_congr_ae hprod')
    _ = ∫ x in D.Ω₂, K y x * b x ∂D.μ := by
      symm
      calc
        _ = ∫ x in D.Ω₂, U.indicator (fun x => K y x * b x) x ∂D.μ := by rw [heq]
        _ = _ := by rw [integral_indicator hU, Measure.restrict_restrict_of_subset hU₂]
    _ = ∫ x in D.Ω₂, (K y x - K y z) * b x ∂D.μ :=
      (integral_kernel_cancel (D.μ.restrict D.Ω₂) (K y) b (K y z) hb hkg₂ hcancel).symm
    _ = ∫ x in ball z r, (K y x - K y z) * b x ∂D.μ := by
      have hm : MeasurableSet (ball z r) := isOpen_ball.measurableSet
      rw [← Measure.restrict_restrict_of_subset hB₂, ← integral_indicator hm]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        by_cases hx : x ∈ ball z r
        · rw [indicator_of_mem hx]
        · simp [hx, hbzero x hx]

end RothschildStein.H2
