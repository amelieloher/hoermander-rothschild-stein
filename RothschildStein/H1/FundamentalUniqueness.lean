-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ScaledDefect
public import RothschildStein.H1.FullHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- A locally integrable null solution with the fundamental
solution's negative dyadic degree vanishes almost everywhere. The proof uses
the local theorem for smooth representatives of weak solutions and BB
Theorem 6.18 (printed p. 264). -/
theorem StandingHypotheses.null_fundamental_degree_ae_zero
    (H : StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ))
    {u : (Fin N → ℝ) → ℝ} (hu : LocallyIntegrable u)
    (hc : ContinuousOn u ({(0 : Fin N → ℝ)}ᶜ))
    (hscale : ∀ x, x ≠ 0 → u (G.dilate 2 x) =
      (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)) * u x)
    (hnull : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * sumSquaresWithDriftTranspose H.fields φ x) = 0) :
    u =ᵐ[volume] 0 := by
  let : NeZero N := ⟨Nat.ne_of_gt G.dimension_pos⟩
  obtain ⟨f, hf, hef⟩ := H.exists_smooth_globalRepresentative G 0 u hu contDiff_const
    (fun φ hφ hs => by simpa only [Pi.zero_apply, zero_mul, integral_zero] using hnull φ hφ hs)
  have he : EqOn u f ({(0 : Fin N → ℝ)}ᶜ) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hef) isOpen_compl_singleton hc
      hf.continuous.continuousOn
  have hd (x : Fin N → ℝ) (hx : x ≠ 0) : G.dilate 2 x ≠ 0 := by
    intro hz
    apply hx
    apply (G2.dilate_bijective G (by norm_num : (2 : ℝ) ≠ 0)).injective
    simpa only [G2.dilate_zero] using hz
  have heq : (fun x => f (G.dilate 2 x)) =
      (fun x => (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)) * f x) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : Fin N → ℝ))
      (hf.continuous.comp (G2.continuous_dilate G 2)) (continuous_const.mul hf.continuous)
    intro x hx
    change f (G.dilate 2 x) = (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)) * f x
    rw [← he (hd x hx), ← he hx]
    exact hscale x hx
  have hz := eq_zero_of_fundamental_dyadic_degree G hQ hf.continuous.continuousAt
    (fun x => congrFun heq x)
  exact hef.trans (Filter.EventuallyEq.of_eq hz)

/-- Two locally integrable fundamental kernels, continuous off
zero and homogeneous of degree 2-Q, agree almost everywhere. Only the
scale two relation is needed (BB Theorem 6.18, printed p. 264). -/
theorem StandingHypotheses.fundamental_unique_ae
    (H : StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ Δ : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ) (hΔ : LocallyIntegrable Δ)
    (hcΓ : ContinuousOn Γ ({(0 : Fin N → ℝ)}ᶜ))
    (hcΔ : ContinuousOn Δ ({(0 : Fin N → ℝ)}ᶜ))
    (hsΓ : ∀ x, x ≠ 0 → Γ (G.dilate 2 x) =
      (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x)
    (hsΔ : ∀ x, x ≠ 0 → Δ (G.dilate 2 x) =
      (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)) * Δ x)
    (hfΓ : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0)
    (hfΔ : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, Δ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0) :
    Γ =ᵐ[volume] Δ := by
  have hnull : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, (Γ x - Δ x) * sumSquaresWithDriftTranspose H.fields φ x) = 0 := by
    intro φ hφ hs
    let φt : TestFunction (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) :=
      ⟨φ, hφ, hs, subset_univ _⟩
    let ψ := sumSquaresWithDriftTransposeTest ⊤ H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) φt
    have he : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDriftTranspose H.fields φ :=
      funext (H.transposeTest_apply G ⊤ φt)
    have hc : Continuous (sumSquaresWithDriftTranspose H.fields φ) := he ▸ ψ.contDiff.continuous
    have hs' : HasCompactSupport (sumSquaresWithDriftTranspose H.fields φ) := he ▸ ψ.hasCompactSupport
    have hiΓ : Integrable (fun x => Γ x * sumSquaresWithDriftTranspose H.fields φ x) :=
      hΓ.integrable_smul_right_of_hasCompactSupport hc hs'
    have hiΔ : Integrable (fun x => Δ x * sumSquaresWithDriftTranspose H.fields φ x) :=
      hΔ.integrable_smul_right_of_hasCompactSupport hc hs'
    simp_rw [sub_mul]
    rw [integral_sub hiΓ hiΔ, hfΓ φ hφ hs, hfΔ φ hφ hs, sub_self]
  have hz := H.null_fundamental_degree_ae_zero G hQ (hΓ.sub hΔ) (hcΓ.sub hcΔ)
    (fun x hx => by dsimp only [Pi.sub_apply]; rw [hsΓ x hx, hsΔ x hx]; ring) hnull
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

end RothschildStein.H1
