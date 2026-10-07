-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PotentialEquation
public import RothschildStein.H1.PotentialDecay
public import RothschildStein.H1.StandingComparison
public import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The fundamental kernel is a two-sided inverse on compact
smooth functions. Solvability and decay imply this identity by Liouville,
with the original drift retained (BB (6.34), printed pp. 269–271). -/
theorem StandingHypotheses.fundamental_twoSidedInverse
    (H : StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    (hcΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({(0 : Fin N → ℝ)}ᶜ))
    (hhΓ : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      Γ (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x)
    (hfund : ∀ ψ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ y, Γ y * sumSquaresWithDriftTranspose H.fields ψ y) = ψ 0)
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcφ : HasCompactSupport φ) (x : Fin N → ℝ) :
    (∫ y, Γ (G.mul (G.inv y) x) * sumSquaresWithDrift H.fields φ y) = φ x := by
  let φt : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hcφ, subset_univ _⟩
  let ψ := sumSquaresTest ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn) φt
  have heψ : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDrift H.fields φ :=
    funext (fun y => sumSquaresTest_apply ⊤ H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) φt y)
  let u : (Fin N → ℝ) → ℝ := fun z => ∫ y, Γ (G.mul (G.inv y) z) * ψ y
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := contDiff_fundamentalPotential G hΓ ψ.contDiff ψ.hasCompactSupport
  have hLu : sumSquaresWithDrift H.fields u = ψ :=
    H.fundamentalPotential_equation G hΓ hfund ψ.contDiff ψ.hasCompactSupport
  have hdec := fundamentalPotential_decay G H.norm hQ hcΓ.continuousOn hhΓ
    ψ.contDiff.continuous ψ.hasCompactSupport
  let w : (Fin N → ℝ) → ℝ := u + fun z => (-1 : ℝ) * φ z
  have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun z => (-1 : ℝ) * φ z) := by
    simpa only [smul_eq_mul] using hφ.const_smul (-1 : ℝ)
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := hu.add hneg
  have hLw : ∀ z, sumSquaresWithDrift (driftCoefficientFields G H 1) w z = 0 := by
    intro z
    have hfields : driftCoefficientFields G H 1 = H.fields := by
      funext i
      simp only [driftCoefficientFields, one_smul]
      split_ifs with hi
      · rw [hi]
      · rfl
    rw [hfields]
    rw [sumSquares_add_at (hu.of_le (by simp)).contDiffAt
      (hneg.of_le (by simp)).contDiffAt
      (fun i => ((H.fields_smooth G i.succ).differentiable (by simp)).differentiableAt),
      sumSquares_const_mul, hLu, heψ]
    ring
  obtain ⟨B, hB⟩ := hcφ.isCompact.exists_bound_of_continuousOn continuous_id.continuousOn
  have hwdec : ∀ ε > 0, ∃ R : ℝ, ∀ z, R ≤ ‖z‖ → ‖w z‖ ≤ ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := hdec ε hε
    refine ⟨max R (B + 1), fun z hz => ?_⟩
    have hzero : φ z = 0 := by
      by_contra hn
      have hb := hB z (subset_closure hn)
      simp only [id_eq] at hb
      have hlarge := (le_max_right R (B + 1)).trans hz
      linarith
    simpa only [w, Pi.add_apply, hzero, mul_zero, add_zero] using
      hR z ((le_max_left _ _).trans hz)
  have hz := H.liouville G 1 (hw.of_le (by simp)) hLw hwdec
  have he := congrFun hz x
  change u x + (-1 : ℝ) * φ x = 0 at he
  have hex : u x = φ x := by linarith
  change (∫ y, Γ (G.mul (G.inv y) x) * ψ y) = φ x at hex
  rw [heψ] at hex
  exact hex

end RothschildStein.H1
