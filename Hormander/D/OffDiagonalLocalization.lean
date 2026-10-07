-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.SupportFactorization
public import Hormander.B.OffDiagonal.Operators
public import Hormander.B.Order

@[expose] public section

noncomputable section

open SchwartzMap
open Hormander.B

namespace Hormander.D

/-- Splitting the full Bessel potential into its localized and separated pieces. -/
theorem localizedSobolev_norm_decomposition {N : ℕ}
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (σ ε : ℝ) (u : TestFunction N) :
    sobolevNorm (σ + ε) (realMultiplierOperator η₁ u) ≤
      sobolevNorm ε (localizedBesselOperator η₁ η' σ u) +
        sobolevNorm ε (offDiagonalTailOperator η' η₁ σ u) := by
  have hsplit :
      lambdaOperator σ (realMultiplierOperator η₁ u) =
      realMultiplierOperator η'
          (lambdaOperator σ (realMultiplierOperator η₁ u)) +
          offDiagonalTailOperator η' η₁ σ u := by
    ext x
    change _ = realMultiplierOperator η'
      (lambdaOperator σ (realMultiplierOperator η₁ u)) x +
        offDiagonalTailOperator η' η₁ σ u x
    rw [offDiagonalTailOperator_apply, realMultiplierOperator_apply]
    push_cast
    ring
  have hshift : sobolevNorm (σ + ε) (realMultiplierOperator η₁ u) =
      sobolevNorm ε (lambdaOperator σ (realMultiplierOperator η₁ u)) := by
    rw [sobolevNorm_lambdaOperator]
    congr 1
    ring
  rw [hshift, hsplit]
  calc
    sobolevNorm ε
        (realMultiplierOperator η'
          (lambdaOperator σ (realMultiplierOperator η₁ u)) +
          offDiagonalTailOperator η' η₁ σ u) ≤
        sobolevNorm ε
            (realMultiplierOperator η'
              (lambdaOperator σ (realMultiplierOperator η₁ u))) +
          sobolevNorm ε (offDiagonalTailOperator η' η₁ σ u) :=
      sobolevNorm_add_le _ _ _
    _ = sobolevNorm ε (localizedBesselOperator η₁ η' σ u) +
        sobolevNorm ε (offDiagonalTailOperator η' η₁ σ u) := by rfl

/-- A nested input cutoff transfers the separated Bessel tail to the
localized data norm, assuming the off-diagonal smoothing estimate. -/
theorem offDiagonalTail_localized_bound_of_B8 {N : ℕ}
    (hB8 : ∀ (φ ψ : SchwartzMap (Carrier N) ℝ) (σ τ r : ℝ),
      cutoffPrecedes (ψ : Carrier N → ℝ) (φ : Carrier N → ℝ) →
      ∃ C : NNReal, ∀ v : TestFunction N,
        sobolevNorm r (offDiagonalTailOperator φ ψ σ v) ≤
          (C : ℝ) * sobolevNorm (r - τ) v)
    (φ ψ η₂ : SchwartzMap (Carrier N) ℝ) (σ τ r : ℝ)
    (hψφ : cutoffPrecedes (ψ : Carrier N → ℝ) (φ : Carrier N → ℝ))
    (hψη₂ : cutoffPrecedes (ψ : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ C : NNReal, ∀ u : TestFunction N,
      sobolevNorm r (offDiagonalTailOperator φ ψ σ u) ≤
        (C : ℝ) * sobolevNorm (r - τ) (realMultiplierOperator η₂ u) := by
  obtain ⟨C, hC⟩ := hB8 φ ψ σ τ r hψφ
  refine ⟨C, fun u => ?_⟩
  have hmul (v : TestFunction N) :
      realMultiplierOperator ψ (realMultiplierOperator η₂ v) =
        realMultiplierOperator ψ v := by
    ext x
    simp only [realMultiplierOperator_apply]
    rw [← mul_assoc, ← Complex.ofReal_mul,
      cutoffPrecedes_mul_eq_self hψη₂ x]
  have hoff : offDiagonalTailOperator φ ψ σ u =
      offDiagonalTailOperator φ ψ σ (realMultiplierOperator η₂ u) := by
    simp [offDiagonalTailOperator, LinearMap.comp_apply, hmul]
  rw [hoff]
  exact hC (realMultiplierOperator η₂ u)

/-- The localized Sobolev norm splits into the input and an off-diagonal
remainder controlled by the larger data cutoff, under the off-diagonal smoothing hypothesis. -/
theorem localizedSobolev_offDiagonal_bound_of_B8 {N : ℕ}
    (hB8 : ∀ (φ ψ : SchwartzMap (Carrier N) ℝ) (σ τ r : ℝ),
      cutoffPrecedes (ψ : Carrier N → ℝ) (φ : Carrier N → ℝ) →
      ∃ C : NNReal, ∀ v : TestFunction N,
        sobolevNorm r (offDiagonalTailOperator φ ψ σ v) ≤
          (C : ℝ) * sobolevNorm (r - τ) v)
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (σ ε : ℝ)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ C : NNReal, ∀ u : TestFunction N,
      sobolevNorm (σ + ε) (realMultiplierOperator η₁ u) ≤
        sobolevNorm ε (localizedBesselOperator η₁ η' σ u) +
          (C : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ u) := by
  have hη₁η₂ := cutoffPrecedes.trans hη₁η' hη'η₂
  obtain ⟨C, hC⟩ := offDiagonalTail_localized_bound_of_B8 hB8
    η' η₁ η₂ σ (ε - σ) ε hη₁η' hη₁η₂
  refine ⟨C, fun u => ?_⟩
  calc
    sobolevNorm (σ + ε) (realMultiplierOperator η₁ u) ≤
        sobolevNorm ε (localizedBesselOperator η₁ η' σ u) +
          sobolevNorm ε (offDiagonalTailOperator η' η₁ σ u) :=
      localizedSobolev_norm_decomposition η₁ η' σ ε u
    _ ≤ sobolevNorm ε (localizedBesselOperator η₁ η' σ u) +
          (C : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ u) := by
      have hexp : ε - (ε - σ) = σ := by ring
      have hb := hC u
      rw [hexp] at hb
      exact add_le_add_right hb _

end Hormander.D

end
