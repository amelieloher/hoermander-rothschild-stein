-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DifferentialPowerJets
public import RothschildStein.G3.TaylorRemainder
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology BigOperators
namespace RothschildStein.G3

/-- The finite exponential polynomial is the actual flow pullback
Taylor polynomial; its remainder is controlled by the next field power along
the entire trajectory (BB (9.9), pp. 410–412). -/
theorem integralCurve_pullback_taylor_bound {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) {a b : ℝ}
    (α : ℝ → (Fin N → ℝ))
    (hODE : ∀ r ∈ Ioo a b, HasDerivAt α (V (α r)) r)
    (hmem : ∀ r ∈ Ioo a b, α r ∈ Ω)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (n : ℕ) {t M : ℝ} (hsegment : ∀ r ∈ Icc (0 : ℝ) 1, r * t ∈ Ioo a b)
    (hbound : ∀ r ∈ Icc (0 : ℝ) 1, ‖fieldPower V (n + 1) f (α (r * t))‖ ≤ M) :
    ‖f (α t) - ∑ k ∈ Finset.range (n + 1),
      (t ^ k / (k.factorial : ℝ)) * fieldPower V k f (α 0)‖ ≤ M * |t| ^ (n + 1) := by
  let g : ℝ → ℝ := fun r => f (α r)
  have hαsmooth := G1.integralCurve_contDiffOn V hV α hODE hmem
  have hgsmooth : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioo a b) := hf.comp hαsmooth hmem
  have h₀ : (0 : ℝ) ∈ Ioo a b := by simpa using hsegment 0 (by norm_num)
  have hj : ∀ k, iteratedDeriv k g 0 = fieldPower V k f (α 0) :=
    fun k => iteratedDeriv_pullback_integralCurve Ω V hV isOpen_Ioo α hODE hmem k f hf h₀
  have hm := norm_taylor_remainder_le (f := g) (x := (0 : ℝ)) (y := t) (n := n)
    (fun r hr => by
      simpa only [zero_add, smul_eq_mul] using
        (hgsmooth.contDiffAt (isOpen_Ioo.mem_nhds (hsegment r hr))).of_le (by simp))
    (fun r hr => by
      simp only [zero_add, smul_eq_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      rw [iteratedDeriv_pullback_integralCurve Ω V hV isOpen_Ioo α hODE hmem (n + 1) f hf
        (hsegment r hr)]
      exact hbound r hr)
  simpa only [g, zero_add, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, hj, smul_eq_mul,
    Real.norm_eq_abs, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hm
end RothschildStein.G3
