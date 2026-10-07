-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DyadicPairingLimit
public import RothschildStein.H1.ScaledErrorVanish
public import RothschildStein.H1.FundamentalDictionary
public import RothschildStein.H1.ReversedOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open TopologicalSpace Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The complete local error pairing identity passes to the
fundamental identity for the global dyadic candidate (BB p. 266).
The error vanishes near zero, so its scaled pairing is eventually zero. -/
theorem StandingHypotheses.fundamentalDyadicLimit_pairing
    (H : StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ E ω : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) ω) (hs : HasCompactSupport ω)
    (hω : ∀ x ≠ 0, ω x = scaledFundamentalKernel G 2 Γ x - Γ x)
    (hE : E =ᶠ[𝓝 (0 : Fin N → ℝ)] 0)
    (hlocal : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0 + ∫ x, E x * φ x)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcompact : HasCompactSupport φ) :
    (∫ x, fundamentalDyadicLimit G Γ ω x * sumSquaresWithDriftTranspose H.fields φ x) =
      φ 0 := by
  let φtest : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) :=
    ⟨φ, hφ, hcompact, subset_univ _⟩
  let ψ := sumSquaresWithDriftTransposeTest ⊤ H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) φtest
  have hp : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDriftTranspose H.fields φ :=
    funext (H.transposeTest_apply G ⊤ φtest)
  have ht := tendsto_integral_scaledFundamentalKernel G hQ hΓ hsm hs hω
    (hp ▸ ψ.contDiff.continuous) (hp ▸ ψ.hasCompactSupport)
  have he : (fun n : ℕ => ∫ x, scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x *
      sumSquaresWithDriftTranspose H.fields φ x) =ᶠ[atTop] (fun _ => φ 0) := by
    filter_upwards [eventually_integral_scaledError_zero G E φ hcompact hE] with n hn
    rw [scaled_pairing_identity G (sumSquaresWithDriftTranspose H.fields)
      (H.transpose_homogeneous G) Γ E hlocal (pow_pos (by norm_num) n) φ hφ hcompact,
      hn, add_zero]
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)

end RothschildStein.H1
