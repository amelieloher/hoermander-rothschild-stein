-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.OperatorAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ}

/-- Weak comparison from the exact exponential barrier identity
for either drift sign, without coefficient bounds (BB Thm 1.57,
pp. 37–38). The identity is stated for the sum-of-squares operator,
including its drift. -/
theorem weak_comparison_boundary_of_barrier
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (j : Fin N) (γ : ℝ)
    (hbar : ∀ z, sumSquaresWithDrift X (fun z => Real.exp (γ * z j)) z = Real.exp (γ * z j))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (hc : ContinuousOn f (closure U))
    (hX : ∀ i : Fin q, DifferentiableOn ℝ (X i.succ) U)
    (hP : ∀ z ∈ U, 0 ≤ sumSquaresWithDrift X f z)
    {M : ℝ} (hM : ∀ z ∈ frontier U, f z ≤ M)
    (x : Fin N → ℝ) (hx : x ∈ closure U) : f x ≤ M := by
  let b : (Fin N → ℝ) → ℝ := fun z => Real.exp (γ * z j)
  have hb : ContDiff ℝ 2 b := Real.contDiff_exp.comp (contDiff_const.mul (contDiff_apply ℝ ℝ j))
  have hK : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨B, hB⟩ := hK.bddAbove_image hb.continuous.continuousOn
  have H (ε : ℝ) (hε : 0 < ε) : f x ≤ M + ε * B := by
    let g : (Fin N → ℝ) → ℝ := fun z => ε * b z
    have hg : ContDiff ℝ 2 g := contDiff_const.mul hb
    have hp : ∀ z ∈ U, 0 < sumSquaresWithDrift X (f + g) z := by
      intro z hz
      rw [sumSquares_add_at (hf.contDiffAt (hU.mem_nhds hz)) hg.contDiffAt
        (fun i => (hX i z hz).differentiableAt (hU.mem_nhds hz))]
      have he : sumSquaresWithDrift X g z = ε * b z := by
        change sumSquaresWithDrift X (fun z => ε * b z) z = _
        rw [congrFun (sumSquares_const_mul X ε b) z]
        exact congrArg (fun v => ε * v) (hbar z)
      rw [he]
      exact add_pos_of_nonneg_of_pos (hP z hz) (mul_pos hε (Real.exp_pos _))
    obtain ⟨y, hy, hxy⟩ := strict_comparison_boundary hU hUb
      (hf.add hg.contDiffOn) (hc.add hg.continuous.continuousOn) hX hp x hx
    have hyB : b y ≤ B := hB ⟨y, frontier_subset_closure hy, rfl⟩
    calc
      f x ≤ (f + g) x := by
        change f x ≤ f x + ε * b x
        exact le_add_of_nonneg_right (mul_nonneg hε.le (Real.exp_pos _).le)
      _ ≤ (f + g) y := hxy
      _ ≤ M + ε * B := add_le_add (hM y hy) (mul_le_mul_of_nonneg_left hyB hε.le)
  have hcont : Continuous (fun ε : ℝ => M + ε * B) :=
    continuous_const.add (continuous_id.mul continuous_const)
  have ht : Tendsto (fun ε : ℝ => M + ε * B) (𝓝[>] 0) (𝓝 M) := by
    simpa only [zero_mul, add_zero] using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact H ε hε

end RothschildStein.H1
