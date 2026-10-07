-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.UniformRescaledTransferRemainderBound
public import RothschildStein.P1.TransferInputParameterRange
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

/-- Every rescaled coordinate shell integral of the complete
transfer remainder is bounded by a uniform multiple of ε. The compact majorant
is built from the actual chart and weighted jets, including lower coordinates. -/
theorem exists_uniform_rescaledTransfer_integral_bound
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) (i : Fin k) (j : Fin (n + m))
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (D : (Fin (n + m) → ℝ) → ℝ) (hD : Continuous D)
    (hsD : HasCompactSupport D) (h0D : (0 : Fin (n + m) → ℝ) ∉ tsupport D)
    (φ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hBφ : ∀ ξ ∈ K, ∀ u, ‖φ ξ u‖ ≤ B) :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ξ ∈ K,
      ‖∫ u, Ψ ξ ((C.e ξ).symm (-C.G.dilate ε u)) u *
      (ε ^ (((w i : ℕ) : ℝ) - C.G.weight j) * C.generatorTransferRemainder i ξ ((C.e ξ).symm (-C.G.dilate ε u)) (C.G.dilate ε u) j) *
        D u * φ ξ (C.G.dilate ε u)‖ ≤ A₀ * ε := by
  let S := tsupport D
  have hS : IsCompact S := hsD.isCompact
  obtain ⟨L, hL, hLU, hp, _⟩ := C.exists_transferInput_parameter_range
    hK hKU hS
  obtain ⟨A, hA, hrem⟩ := C.exists_uniform_rescaled_transfer_remainder_coordinate_bound i j hL hLU hS
  have hne {u : Fin (n + m) → ℝ} (hu : u ∈ S) : u ≠ 0 := fun hz => h0D (hz ▸ hu)
  obtain ⟨M₀, hM₀⟩ := (hL.prod (hL.prod hS)).exists_bound_of_continuousOn
    (hΨ.mono (fun _ h => hne h.2.2))
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hint : Integrable (fun u => ‖D u‖) := (hD.integrable_of_hasCompactSupport hsD).norm
  refine ⟨M * A * B * ∫ u, ‖D u‖, by positivity, ?_⟩
  have hest : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ξ ∈ K,
      ‖∫ u, Ψ ξ ((C.e ξ).symm (-C.G.dilate ε u)) u *
        (ε ^ (((w i : ℕ) : ℝ) - C.G.weight j) * C.generatorTransferRemainder i ξ ((C.e ξ).symm (-C.G.dilate ε u)) (C.G.dilate ε u) j) *
          D u * φ ξ (C.G.dilate ε u)‖ ≤ (M * A * B * ∫ u, ‖D u‖) * ε := by
    filter_upwards [hp, hrem, self_mem_nhdsWithin] with ε hεp hεr hε
    intro ξ hξ
    have hεpos : 0 < ε := hε
    have hdom : ∀ u, ‖Ψ ξ ((C.e ξ).symm (-C.G.dilate ε u)) u *
        (ε ^ (((w i : ℕ) : ℝ) - C.G.weight j) * C.generatorTransferRemainder i ξ ((C.e ξ).symm (-C.G.dilate ε u)) (C.G.dilate ε u) j) *
          D u * φ ξ (C.G.dilate ε u)‖ ≤ (M * A * B * ε) * ‖D u‖ := by
      intro u
      by_cases hu : u ∈ S
      · have hpars := (hεp ξ hξ).2 u hu
        have hkernel : ‖Ψ ξ ((C.e ξ).symm (-C.G.dilate ε u)) u‖ ≤ M :=
          (hM₀ (ξ, (C.e ξ).symm (-C.G.dilate ε u), u)
            ⟨hpars.1, hpars.2, hu⟩).trans (le_max_left _ _)
        simp only [norm_mul]
        rw [← norm_mul (ε ^ (((w i : ℕ) : ℝ) - C.G.weight j))
          (C.generatorTransferRemainder i ξ ((C.e ξ).symm (-C.G.dilate ε u)) (C.G.dilate ε u) j)]
        calc
          _ ≤ (M * (A * ε)) * ‖D u‖ * B :=
            mul_le_mul (mul_le_mul_of_nonneg_right
              (mul_le_mul hkernel (hεr ξ hpars.1 ((C.e ξ).symm (-C.G.dilate ε u)) hpars.2 u hu)
                (norm_nonneg _) hM) (norm_nonneg _)) (hBφ ξ hξ _)
              (norm_nonneg _) (by positivity)
          _ = _ := by ring
      · rw [image_eq_zero_of_notMem_tsupport (f := D) hu, mul_zero, zero_mul, norm_zero]
        positivity
    have hh := norm_integral_le_of_norm_le (hint.const_mul (M * A * B * ε))
      (Eventually.of_forall hdom)
    rw [integral_const_mul] at hh
    convert hh using 1
    ring
  exact hest

end RothschildStein.P1.LiftedChart
