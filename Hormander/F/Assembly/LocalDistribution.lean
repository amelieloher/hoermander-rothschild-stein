-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.Assembly.Hypotheses
public import Hormander.Statements.MemSobolevOfIntegrable
public import Hormander.Statements.ExistsContDiffOfMemSobolev
public import Hormander.F.AEIdentification

/-!
# Localized distributions and smooth representatives
-/

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap Topology Filter

namespace Hormander.F

/-- A smooth compactly supported real cutoff, viewed as a complex function, has temperate growth. -/
theorem cutoff_hasTemperateGrowth {N : ℕ} {ζ : E₂ N → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) :
    Function.HasTemperateGrowth (fun x => ((ζ x : ℝ) : ℂ)) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((ζ x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hζ
  have h2 : HasCompactSupport (fun x => ((ζ x : ℝ) : ℂ)) :=
    hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  exact h2.hasTemperateGrowth h1

/-- Multiplying the distribution of an integrable function by a smooth cutoff multiplies the
function. -/
theorem smulLeft_toTemperedDistribution {N : ℕ} {ζ : E₂ N → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) {v w : E₂ N → ℂ} (hv : Integrable v volume)
    (hw : Integrable w volume) (hvw : ∀ x, w x = (ζ x : ℂ) * v x) :
    TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ x : ℝ) : ℂ))
        (Lp.toTemperedDistribution (hv.toL1 v)) =
      Lp.toTemperedDistribution (hw.toL1 w) := by
  have hg := cutoff_hasTemperateGrowth hζ hc
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toL1, hw.coeFn_toL1] with x h1 h2
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, h1, h2, hvw x]
  simp only [smul_eq_mul]
  ring

/-- A bounded continuous cutoff preserves integrability. -/
theorem integrable_cutoff_mul {N : ℕ} {ζ : E₂ N → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) {v : E₂ N → ℂ} (hv : Integrable v volume) :
    Integrable (fun x => (ζ x : ℂ) * v x) volume := by
  have hcont : Continuous (fun x => ((ζ x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hζ.continuous
  obtain ⟨C, hC⟩ := hζ.continuous.bounded_above_of_compact_support hc
  exact hv.bdd_mul (c := C) hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by simpa using hC x)

/-- The localized input lies in `H^{-m}` for `m = N/2 + 1`, by the negative-order Sobolev
bound for integrable functions applied to `ζ' v`. -/
theorem localized_negative_sobolev {N : ℕ} {ζ : E₂ N → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) {v : E₂ N → ℂ} (hv : Integrable v volume) :
    TemperedDistribution.MemSobolev (-((N : ℝ) / 2 + 1)) 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ x : ℝ) : ℂ))
        (Lp.toTemperedDistribution (hv.toL1 v))) := by
  have hw := integrable_cutoff_mul hζ hc hv
  rw [smulLeft_toTemperedDistribution hζ hc hv hw (fun x => rfl)]
  exact Hormander.memSobolev_neg_of_integrable hw (by linarith)

/-- A real integrable function whose distribution lies in every Sobolev space agrees almost
everywhere with the real part of a smooth function. -/
theorem exists_smooth_realPart_ae {N : ℕ} {w : E₂ N → ℂ} (hw : Integrable w volume)
    {uR : E₂ N → ℝ} (hwR : ∀ y, w y = (uR y : ℂ))
    (hmem : ∀ t : ℝ, TemperedDistribution.MemSobolev t 2 (Lp.toTemperedDistribution (hw.toL1 w))) :
    ∃ F : E₂ N → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧ ∀ᵐ x ∂volume, uR x = (F x).re := by
  obtain ⟨F, hF, hFφ⟩ := Hormander.exists_contDiff_of_forall_memSobolev hmem
  refine ⟨F, hF, ?_⟩
  have huR : Integrable uR volume := by
    have := hw.re
    simpa [hwR] using this
  have hv : LocallyIntegrableOn uR Set.univ volume := huR.locallyIntegrable.locallyIntegrableOn _
  have key := ae_eq_realPart_of_complex_test_integrals isOpen_univ uR F hv hF.contDiffOn ?_
  · filter_upwards [key] with x hx using hx (Set.mem_univ x)
  · intro φ hφ hcs _
    have hφC : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((φ x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hφ
    have hcsC : HasCompactSupport (fun x => ((φ x : ℝ) : ℂ)) :=
      hcs.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    have h := (hFφ (hcsC.toSchwartzMap hφC)).2
    rw [Lp.toTemperedDistribution_apply] at h
    simp only [Measure.restrict_univ]
    have h2 : ∫ x, (hcsC.toSchwartzMap hφC) x • (hw.toL1 w) x = ∫ x, ((φ x : ℝ) : ℂ) * (uR x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hw.coeFn_toL1] with x hx
      rw [hx, hwR x]
      simp
    rw [h2] at h
    simpa using h.symm

end Hormander.F
