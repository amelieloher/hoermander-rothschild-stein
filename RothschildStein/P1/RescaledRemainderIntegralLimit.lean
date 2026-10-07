-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RescaledRemainderBound
public import RothschildStein.P1.RescaledChartParameters
public import RothschildStein.P1.PrincipalModelKernel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Every rescaled coordinate of the actual
input-chart remainder has zero shell integral limit. The compact majorant
is built from the actual chart and weighted jets, including lower coordinates. -/
theorem tendsto_rescaledInput_remainder_integral
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k) (j : Fin (n + m))
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (D : (Fin (n + m) → ℝ) → ℝ) (hD : Continuous D)
    (hsD : HasCompactSupport D) (h0D : (0 : Fin (n + m) → ℝ) ∉ tsupport D)
    (φ : (Fin (n + m) → ℝ) → ℝ) (hφ : Continuous φ) (hsφ : HasCompactSupport φ) :
    Tendsto (fun ε : ℝ => ∫ u, Ψ ξ ((C.e ξ).symm (-C.G.dilate ε u)) u *
      (ε ^ (((w i : ℕ) : ℝ) - C.G.weight j) * C.R [i] ξ (-C.G.dilate ε u) j) *
        D u * φ (C.G.dilate ε u)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let S := tsupport D
  have hS : IsCompact S := hsD.isCompact
  obtain ⟨L, hL, hp, _⟩ := C.exists_rescaledInput_parameter_range
    (isCompact_singleton (x := ξ)) (singleton_subset_iff.mpr hξ) hS
  obtain ⟨A, hA, hrem⟩ := C.exists_rescaled_remainder_coordinate_bound i j
    (isCompact_singleton (x := ξ)) (singleton_subset_iff.mpr hξ) hS
  have hne {u : Fin (n + m) → ℝ} (hu : u ∈ S) : u ≠ 0 := fun hz => h0D (hz ▸ hu)
  obtain ⟨M₀, hM₀⟩ := (hL.prod (hL.prod hS)).exists_bound_of_continuousOn
    (hΨ.mono (fun _ h => hne h.2.2))
  obtain ⟨B₀, hB₀⟩ := hsφ.exists_bound_of_continuous hφ
  let M : ℝ := max M₀ 0
  let B : ℝ := max B₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hB : 0 ≤ B := le_max_right _ _
  have hBφ (u : Fin (n + m) → ℝ) : ‖φ u‖ ≤ B := (hB₀ u).trans (le_max_left _ _)
  have hint : Integrable (fun u => ‖D u‖) := (hD.integrable_of_hasCompactSupport hsD).norm
  have hest : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ‖∫ u, Ψ ξ ((C.e ξ).symm (-C.G.dilate ε u)) u *
        (ε ^ (((w i : ℕ) : ℝ) - C.G.weight j) * C.R [i] ξ (-C.G.dilate ε u) j) *
          D u * φ (C.G.dilate ε u)‖ ≤ (M * A * B * ∫ u, ‖D u‖) * ε := by
    filter_upwards [hp, hrem, self_mem_nhdsWithin] with ε hεp hεr hε
    have hεpos : 0 < ε := hε
    have hdom : ∀ u, ‖Ψ ξ ((C.e ξ).symm (-C.G.dilate ε u)) u *
        (ε ^ (((w i : ℕ) : ℝ) - C.G.weight j) * C.R [i] ξ (-C.G.dilate ε u) j) *
          D u * φ (C.G.dilate ε u)‖ ≤ (M * A * B * ε) * ‖D u‖ := by
      intro u
      by_cases hu : u ∈ S
      · have hpars := (hεp ξ (mem_singleton ξ)).2 u hu
        have hkernel : ‖Ψ ξ ((C.e ξ).symm (-C.G.dilate ε u)) u‖ ≤ M :=
          (hM₀ (ξ, (C.e ξ).symm (-C.G.dilate ε u), u)
            ⟨hpars.1, hpars.2, hu⟩).trans (le_max_left _ _)
        simp only [norm_mul]
        rw [← norm_mul (ε ^ (((w i : ℕ) : ℝ) - C.G.weight j))
          (C.R [i] ξ (-C.G.dilate ε u) j)]
        calc
          _ ≤ (M * (A * ε)) * ‖D u‖ * B :=
            mul_le_mul (mul_le_mul_of_nonneg_right
              (mul_le_mul hkernel (hεr ξ (mem_singleton ξ) u hu)
                (norm_nonneg _) hM) (norm_nonneg _)) (hBφ _)
              (norm_nonneg _) (by positivity)
          _ = _ := by ring
      · rw [image_eq_zero_of_notMem_tsupport (f := D) hu, mul_zero, zero_mul, norm_zero]
        positivity
    have hh := norm_integral_le_of_norm_le (hint.const_mul (M * A * B * ε))
      (Eventually.of_forall hdom)
    rw [integral_const_mul] at hh
    convert hh using 1
    ring
  apply squeeze_zero_norm' hest
  have htε : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa only [mul_zero] using htε.const_mul (M * A * B * ∫ u, ‖D u‖)

end RothschildStein.P1.LiftedChart
