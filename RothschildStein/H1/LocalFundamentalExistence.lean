-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.StandingDistributionRegularity
public import RothschildStein.H1.StandingDistribution
public import RothschildStein.H1.OrderZeroIntegrableRepresentative
public import RothschildStein.H1.PuncturedIntegrabilityAdapter
public import RothschildStein.S.DistributionRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The local order-zero fundamental distribution is represented by an
integrable function that is smooth off zero. Local weak regularity and
L¹ exhaustion give this representation. -/
theorem StandingHypotheses.exists_localFundamentalFunction
    (H : StandingHypotheses G q) (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (hΩ : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ Ω, G.dilate t x ∈ Ω)
    (T : BoundedContinuousFunction (Fin N → ℝ) ℝ →L[ℝ] ℝ)
    (hfund : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      smoothOrderZeroDistribution Ω T (sumSquaresWithDriftTransposeTest Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) φ) = φ 0) :
    ∃ γ : (Fin N → ℝ) → ℝ, Integrable γ ∧
      ContDiffOn ℝ (⊤ : ℕ∞) γ ((Ω : Set (Fin N → ℝ)) ∩ {(0 : Fin N → ℝ)}ᶜ) ∧
      ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
        (∫ x, γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0 := by
  let U : Opens (Fin N → ℝ) := Ω ⊓ ⟨{(0 : Fin N → ℝ)}ᶜ, isOpen_compl_singleton⟩
  have hU : U ≤ Ω := inf_le_left
  let D := smoothOrderZeroDistribution Ω T
  let R := S.distributionRestrictionCLM Ω U D
  let castTest (φ : TestFunction U ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hU⟩
  have hR (φ : TestFunction U ℝ (⊤ : ℕ∞)) : R φ = D (castTest φ) :=
    S.distributionRestrictionCLM_apply Ω U hU D φ
  have hEq : ∀ φ : TestFunction U ℝ (⊤ : ℕ∞),
      R (sumSquaresWithDriftTransposeTest U H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) φ) = Distribution.ofFun U 0 volume (⊤ : ℕ∞) φ := by
    intro φ
    rw [hR]
    have he : castTest (sumSquaresWithDriftTransposeTest U H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) φ) =
        sumSquaresWithDriftTransposeTest Ω H.fields
          (fun i => (H.fields_smooth G i).contDiffOn) (castTest φ) := by
      ext x
      change sumSquaresWithDriftTransposeTest U H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) φ x =
        sumSquaresWithDriftTransposeTest Ω H.fields
          (fun i => (H.fields_smooth G i).contDiffOn) (castTest φ) x
      rw [H.transposeTest_apply G U, H.transposeTest_apply G Ω]
      have hc : ((castTest φ) : (Fin N → ℝ) → ℝ) = φ := rfl
      rw [hc]
    rw [he, hfund]
    have hz : φ (0 : Fin N → ℝ) = 0 := φ.zero_on_compl (by
      change ¬ ((0 : Fin N → ℝ) ∈ Ω ∧ (0 : Fin N → ℝ) ∈ {(0 : Fin N → ℝ)}ᶜ)
      simp)
    simpa only [castTest, hz, Distribution.ofFun_zero, map_zero]
  obtain ⟨f, hf, hrep⟩ := H.exists_smooth_distributionRepresentative G U R 0 contDiffOn_const hEq
  have hB (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
      (TestFunction.toBoundedContinuousFunctionCLM ℝ) (castTest φ) =
        (TestFunction.toBoundedContinuousFunctionCLM ℝ) φ := by
    ext x
    rfl
  have hb (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
      |R φ| ≤ ‖T‖ * ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖ := by
    rw [hR]
    simpa only [hB] using abs_smoothOrderZeroDistribution_le Ω T (le_refl ‖T‖) (castTest φ)
  have hi := integrableOn_of_smooth_orderZero_representation U hf R.toLinearMap
    (norm_nonneg T) hb (fun φ => by
      change (∫ x, f x * φ x) = R φ
      simpa only [mul_comm] using (hrep φ).symm)
  let γ := (Ω : Set (Fin N → ℝ)).indicator f
  have hγ : Integrable γ := integrable_zeroExtension_of_punctured G Ω hi
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) γ (U : Set (Fin N → ℝ)) := by
    apply hf.congr
    intro x hx
    exact indicator_of_mem hx.1 f
  have haway (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
      (hz : (0 : Fin N → ℝ) ∉ tsupport (φ : (Fin N → ℝ) → ℝ)) :
      D φ = ∫ x, γ x * φ x := by
    let ψ : TestFunction U ℝ (⊤ : ℕ∞) :=
      ⟨φ, φ.contDiff, φ.hasCompactSupport, fun x hx => ⟨φ.tsupport_subset hx, fun he => hz (he ▸ hx)⟩⟩
    have he := hrep ψ
    rw [hR] at he
    have hc : castTest ψ = φ := by ext x; rfl
    rw [hc] at he
    refine he.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
    change φ x * f x = (Ω : Set (Fin N → ℝ)).indicator f x * φ x
    by_cases hx : x ∈ Ω
    · rw [indicator_of_mem hx f]; exact mul_comm _ _
    · simp only [indicator_of_notMem hx, φ.zero_on_compl hx, Pi.zero_apply, zero_mul]
  obtain ⟨_, hlocal⟩ := H.localFundamental_from_orderZeroRepresentation G Ω h0 hΩ
    D.toLinearMap (norm_nonneg T) (fun φ => abs_smoothOrderZeroDistribution_le Ω T (le_refl ‖T‖) φ)
    hfund hγ haway
  exact ⟨γ, hγ, hs, hlocal⟩

end RothschildStein.H1
