-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RestrictedErrorKernel
public import RothschildStein.P1.KernelEstimates

/-!
# Restricted-error bounds: the hypotheses follow from the kernel estimates

The kernel `K(ξ, η) = χ(Θ(η, ξ)) W^{ξ,η}(Θ(η, ξ))` of a `C¹`, homogeneous-of-degree-`1 - Q` family
`W` with a `C¹` cutoff `χ` of the group variable (`LiftedChart.kernelValue`) satisfies
`RestrictedKernelBounds` on every compact `K₀ ⊆ U`: the size and difference bounds are the
conclusion of `LiftedChart.exists_kernel_estimates_cutoff` at `ℓ = 1`, and the cut kernel is
continuous (`Θ(η, ξ) ≠ 0` off the diagonal of `U × U` by injectivity of the endpoint charts, `W` is
continuous off `u = 0`), hence measurable. These are the building blocks of the kernel of
`F_R^chart` (from the right pole computation).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The two-point map has no zero off the diagonal of `U × U`:
`Θ(η, ξ) = 0` forces `ξ = η` (injectivity of the endpoint chart `e η`). -/
theorem Θ_ne_zero {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : ξ ≠ η) :
    C.Θ η ξ ≠ 0 := by
  intro h0
  obtain ⟨hsrc, hval, -, -, hΘ⟩ := C.chart η hη
  apply hne
  refine (C.e η).injOn (by rw [hsrc]; exact hξ) (by rw [hsrc]; exact hη) ?_
  rw [hval ξ hξ, hval η hη, h0, hΘ]

/-- The kernel `χ(Θ(η, ξ)) W^{ξ,η}(Θ(η, ξ))` is continuous on
`K₀ × K₀` off the diagonal. -/
theorem continuousOn_kernelValue {K₀ : Set (Fin (n + m) → ℝ)} (hK₀U : K₀ ⊆ C.U)
    {χ : (Fin (n + m) → ℝ) → ℝ} (hχ : Continuous χ)
    {W : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hW : ContinuousOn (kernelUncurry W) {z | z.2.2 ≠ 0}) :
    ContinuousOn (Function.uncurry (C.kernelValue χ W))
      ((K₀ ×ˢ K₀) \ Set.diagonal (Fin (n + m) → ℝ)) := by
  have hΘ : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ z.2 z.1)
      (C.U ×ˢ C.U) :=
    C.theta_smooth.continuousOn.comp (continuous_snd.prodMk continuous_fst).continuousOn
      (fun z hz => ⟨hz.2, hz.1⟩)
  have hΘ' : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ z.2 z.1)
      ((K₀ ×ˢ K₀) \ Set.diagonal (Fin (n + m) → ℝ)) :=
    hΘ.mono (fun z hz => ⟨hK₀U hz.1.1, hK₀U hz.1.2⟩)
  have hT : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      (z.1, z.2, C.Θ z.2 z.1)) ((K₀ ×ˢ K₀) \ Set.diagonal (Fin (n + m) → ℝ)) :=
    continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.prodMk hΘ')
  have hW' : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      W z.1 z.2 (C.Θ z.2 z.1)) ((K₀ ×ˢ K₀) \ Set.diagonal (Fin (n + m) → ℝ)) :=
    hW.comp hT (fun z hz => C.Θ_ne_zero (hK₀U hz.1.1) (hK₀U hz.1.2)
      (fun h => hz.2 (Set.mem_diagonal_iff.mpr h)))
  exact (hχ.comp_continuousOn hΘ').mul hW'

variable {C}

end LiftedChart

end RothschildStein.P1
