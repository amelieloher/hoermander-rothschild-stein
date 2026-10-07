-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DyadicKernelFormula
public import RothschildStein.H1.NegativeDegree

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The global kernel candidate constructed from the local kernel
and its smooth dyadic correction (BB (6.28), p. 266). -/
def fundamentalDyadicLimit (Γ ω : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  Γ x + ∑' j : ℕ, ((2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ))) ^ j *
    ω (G.dilate ((1 / 2 : ℝ) ^ j) x)

/-- Exact partial sums after replacing the correction by its
smooth representative away from the origin (BB pp. 265–266). -/
theorem scaledFundamentalKernel_eq_partialSum
    {Γ ω : (Fin N → ℝ) → ℝ}
    (hω : ∀ x ≠ 0, ω x = scaledFundamentalKernel G 2 Γ x - Γ x)
    (n : ℕ) {x : Fin N → ℝ} (hx : x ≠ 0) :
    scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x = Γ x +
      ∑ j ∈ Finset.range n, ((2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ))) ^ j *
        ω (G.dilate ((1 / 2 : ℝ) ^ j) x) := by
  rw [scaledFundamentalKernel_dyadic_telescope]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [scaledFundamentalKernel_dyadic_eq]
  have hz : G.dilate ((1 / 2 : ℝ) ^ j) x ≠ 0 := by
    intro hz
    have he := (G2.dilate_bijective G (pow_ne_zero j (by norm_num))).injective
      (hz.trans (G2.dilate_zero G _).symm)
    exact hx he
  rw [hω _ hz]

/-- The scaled kernels converge uniformly on the entire
punctured group to the dyadic candidate (BB (6.28), p. 266). -/
theorem tendstoUniformlyOn_scaledFundamentalKernel
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ ω : (Fin N → ℝ) → ℝ} (hsm : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hs : HasCompactSupport ω)
    (hω : ∀ x ≠ 0, ω x = scaledFundamentalKernel G 2 Γ x - Γ x) :
    TendstoUniformlyOn (fun n : ℕ => scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ)
      (fundamentalDyadicLimit G Γ ω) Filter.atTop {x | x ≠ 0} := by
  let c : ℝ := (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ))
  have hc : 0 ≤ c := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨C, _, hb⟩ := hs.exists_bound_iteratedFDeriv hsm 0
  have hu : TendstoUniformly
      (fun m x => ∑ j ∈ Finset.range m, c ^ j * ω (G.dilate ((1 / 2 : ℝ) ^ j) x))
      (fun x => ∑' j : ℕ, c ^ j * ω (G.dilate ((1 / 2 : ℝ) ^ j) x))
      Filter.atTop := by
    apply tendstoUniformly_tsum_nat ((summable_geometric_of_lt_one hc hc1).mul_right C)
    intro j x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc j)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc j)
    simpa only [norm_iteratedFDeriv_zero] using hb 0 le_rfl (G.dilate ((1 / 2 : ℝ) ^ j) x)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with n hn x hx
  rw [scaledFundamentalKernel_eq_partialSum G hω n hx]
  simpa only [fundamentalDyadicLimit, dist_add_left] using hn x

end RothschildStein.H1
