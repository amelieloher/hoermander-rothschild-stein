-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LocalDilationIntegrability
public import RothschildStein.H1.NegativeDegree
public import RothschildStein.H1.SmoothCompactRepresentative
public import RothschildStein.H1.FundamentalDictionary
public import RothschildStein.H1.ReversedOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

private theorem dilate_nonzero {s : ℝ} (hs : s ≠ 0) {x : Fin N → ℝ} (hx : x ≠ 0) :
    G.dilate s x ≠ 0 := by
  intro h
  apply hx
  apply (G2.dilate_bijective G hs).injective
  simpa only [G2.dilate_zero] using h

/-- Every scaled defect vanishes by local weak regularity and negative
dyadic rigidity. The hypotheses on Gamma give local integrability, smoothness
off zero, dyadic homogeneity, and the full fundamental pairing on every
compact smooth test (BB p. 266). -/
theorem StandingHypotheses.scaledFundamentalKernel_eq
    (H : StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({(0 : Fin N → ℝ)}ᶜ))
    (hdyadic : ∀ x, x ≠ 0 → Γ (G.dilate 2 x) =
      (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x)
    (hfund : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0)
    {s : ℝ} (hs : 0 < s) (x : Fin N → ℝ) (hx : x ≠ 0) :
    scaledFundamentalKernel G s Γ x = Γ x := by
  let : NeZero N := ⟨Nat.ne_of_gt G.dimension_pos⟩
  let c : ℝ := (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ))
  let u : (Fin N → ℝ) → ℝ := scaledFundamentalKernel G s Γ - Γ
  have hscaled := locallyIntegrable_scaledFundamentalKernel G hΓ hs
  have hu : LocallyIntegrable u := hscaled.sub hΓ
  have huc : ContinuousOn u ({(0 : Fin N → ℝ)}ᶜ) := by
    have hd : ContinuousOn (fun x => Γ (G.dilate s⁻¹ x)) ({(0 : Fin N → ℝ)}ᶜ) :=
      hc.continuousOn.comp (G2.continuous_dilate G s⁻¹).continuousOn
        (fun x hx => dilate_nonzero G (inv_ne_zero hs.ne') hx)
    exact (continuousOn_const.mul hd).sub hc.continuousOn
  have heq : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * sumSquaresWithDriftTranspose H.fields φ x) = ∫ x, (0 : ℝ) * φ x := by
    intro φ hφ hcomp
    let φtest : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) :=
      ⟨φ, hφ, hcomp, subset_univ _⟩
    let ψ := sumSquaresWithDriftTransposeTest ⊤ H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) φtest
    have hp : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDriftTranspose H.fields φ :=
      funext (H.transposeTest_apply G ⊤ φtest)
    have hpcont : Continuous (sumSquaresWithDriftTranspose H.fields φ) := hp ▸ ψ.contDiff.continuous
    have hpcompact : HasCompactSupport (sumSquaresWithDriftTranspose H.fields φ) := hp ▸ ψ.hasCompactSupport
    have hiΓ : Integrable (fun x => Γ x * sumSquaresWithDriftTranspose H.fields φ x) :=
      hΓ.integrable_smul_right_of_hasCompactSupport hpcont hpcompact
    have his : Integrable (fun x => scaledFundamentalKernel G s Γ x *
        sumSquaresWithDriftTranspose H.fields φ x) :=
      hscaled.integrable_smul_right_of_hasCompactSupport hpcont hpcompact
    have hsf := scaled_pairing_identity G (sumSquaresWithDriftTranspose H.fields)
      (H.transpose_homogeneous G) Γ 0
      (fun f hf hc => by simpa only [Pi.zero_apply, zero_mul, integral_zero, add_zero] using hfund f hf hc)
      hs φ hφ hcomp
    simp only [scaledErrorKernel, Pi.zero_apply, mul_zero, zero_mul, integral_zero, add_zero] at hsf
    change (∫ x, (scaledFundamentalKernel G s Γ x - Γ x) *
      sumSquaresWithDriftTranspose H.fields φ x) = _
    simp_rw [sub_mul]
    rw [integral_sub his hiΓ, hsf, hfund φ hφ hcomp]
    simp only [zero_mul, integral_zero, sub_self]
  obtain ⟨f, hf, hef⟩ := H.exists_smooth_globalRepresentative G 0 u hu contDiff_const heq
  have hepoint : EqOn u f ({(0 : Fin N → ℝ)}ᶜ) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hef) isOpen_compl_singleton huc hf.continuous.continuousOn
  have huscale (y : Fin N → ℝ) (hy : y ≠ 0) : u (G.dilate 2 y) = c * u y := by
    have hd : G.dilate s⁻¹ (G.dilate 2 y) = G.dilate 2 (G.dilate s⁻¹ y) := by
      rw [G2.dilate_dilate, G2.dilate_dilate, mul_comm]
    change (s ^ 2 * (s ^ G.homogeneousDimension)⁻¹) * Γ (G.dilate s⁻¹ (G.dilate 2 y)) -
      Γ (G.dilate 2 y) = _
    rw [hd, hdyadic _ (dilate_nonzero G (inv_ne_zero hs.ne') hy), hdyadic y hy]
    dsimp only [u, c, scaledFundamentalKernel, Pi.sub_apply]
    ring
  have hfscale : (fun y => f (G.dilate 2 y)) = (fun y => c * f y) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : Fin N → ℝ))
      (hf.continuous.comp (G2.continuous_dilate G 2)) (continuous_const.mul hf.continuous)
    intro y hy
    have hy0 : y ≠ 0 := hy
    change f (G.dilate 2 y) = c * f y
    rw [← hepoint (dilate_nonzero G (by norm_num : (2 : ℝ) ≠ 0) hy0), ← hepoint hy]
    exact huscale y hy0
  have hfzero := eq_zero_of_fundamental_dyadic_degree G hQ hf.continuous.continuousAt
    (fun y => congrFun hfscale y)
  have hux : u x = 0 := by rw [hepoint hx, hfzero]; rfl
  exact sub_eq_zero.mp hux

end RothschildStein.H1
