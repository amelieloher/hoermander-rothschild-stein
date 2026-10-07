-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.SobolevScale
public import Hormander.B.Order
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexInnerProductSpace FourierTransform

namespace Hormander.D

abbrev C9TestFunction (N : ℕ) := SchwartzMap (Hormander.A.Carrier N) ℂ

theorem integral_norm_sq_eq_schwartzToLp_norm_sq {N : ℕ}
    (f : C9TestFunction N) :
    ∫ x, ‖f x‖ ^ 2 = ‖f.toLp 2 volume‖ ^ 2 := by
  have hnorm : ‖f.toLp 2 volume‖ =
      (∫ x, ‖f x‖ ^ 2) ^ ((2 : ℝ)⁻¹) := by
    simpa [Real.rpow_two] using
      (SchwartzMap.norm_toLp' (f := f) (p := 2) (μ := volume)
        (hp₁ := by norm_num) (hp₂ := by norm_num))
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ 2 :=
    integral_nonneg (fun _ ↦ sq_nonneg _)
  calc
    ∫ x, ‖f x‖ ^ 2 = ((∫ x, ‖f x‖ ^ 2) ^ ((2 : ℝ)⁻¹)) ^ 2 := by
      symm
      exact Real.rpow_inv_natCast_pow hI (by norm_num)
    _ = ‖f.toLp 2 volume‖ ^ 2 := by rw [hnorm]

theorem besselSymbol_norm_sq {N : ℕ} (s : ℝ) (ξ : Hormander.A.Carrier N) :
    ‖Hormander.A.besselSymbol s ξ‖ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ s := by
  have hbase : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  calc
    ‖Hormander.A.besselSymbol s ξ‖ ^ 2 =
        ((1 + ‖ξ‖ ^ 2) ^ (s / 2)) ^ 2 := by
      simp [Hormander.A.besselSymbol, Complex.norm_real]
    _ = (1 + ‖ξ‖ ^ 2) ^ s := by
      rw [pow_two, ← Real.rpow_add hbase]
      congr 1
      ring

/-- The weighted Fourier integral is the squared bundled
Sobolev norm on Schwartz input. -/
theorem c9_weighted_fourier_eq_sobolev_norm_sq {N : ℕ} (s : ℝ)
    (v : C9TestFunction N) :
    ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 v ξ‖ ^ 2 =
      ‖Hormander.A.schwartzToSobolev s v‖ ^ 2 := by
  let w := Hormander.A.Lambda s v
  have hpoint (ξ : Hormander.A.Carrier N) :
      (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 v ξ‖ ^ 2 = ‖𝓕 w ξ‖ ^ 2 := by
    change (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 v ξ‖ ^ 2 =
      ‖𝓕 (Hormander.A.Lambda s v) ξ‖ ^ 2
    rw [Hormander.A.fourier_Lambda]
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (Hormander.A.besselSymbol_hasTemperateGrowth s)]
    rw [norm_smul, mul_pow, Hormander.D.besselSymbol_norm_sq]
  calc
    ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 v ξ‖ ^ 2 =
        ∫ ξ, ‖𝓕 w ξ‖ ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ‖(𝓕 w).toLp 2 volume‖ ^ 2 :=
      integral_norm_sq_eq_schwartzToLp_norm_sq (N := N) (𝓕 w)
    _ = ‖w.toLp 2 volume‖ ^ 2 := by
      have hnorm : ‖(𝓕 w).toLp 2 volume‖ = ‖w.toLp 2 volume‖ := by
        rw [← SchwartzMap.toLp_fourier_eq w, MeasureTheory.Lp.norm_fourier_eq]
      rw [hnorm]
    _ = Hormander.A.schwartzSobolevNorm s v ^ 2 := by
      rfl
    _ = ‖Hormander.A.schwartzToSobolev s v‖ ^ 2 := by
      rw [Hormander.A.schwartzSobolevNorm_eq_schwartzToSobolev_norm]

/-- State the Fourier identity in the shared B Sobolev norm. -/
theorem c9_weighted_fourier_eq_shared_sobolev_norm_sq {N : ℕ} (s : ℝ)
    (v : Hormander.B.TestFunction N) :
    ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 v ξ‖ ^ 2 =
      Hormander.B.sobolevNorm s v ^ 2 := by
  rw [c9_weighted_fourier_eq_sobolev_norm_sq]
  rw [Hormander.B.sobolevNorm_eq_schwartzToSobolev_norm]

end Hormander.D

end
