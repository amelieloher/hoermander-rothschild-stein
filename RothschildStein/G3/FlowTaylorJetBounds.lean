-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FlowTaylorExpansion
public import RothschildStein.G3.FieldPowerBounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Actual flow Taylor remainders have constants polynomial in finite
primitive and test-function jet bounds (BB (9.9), pp. 410–415). -/
theorem integralCurve_pullback_taylor_bound_of_jet_bounds {N R : ℕ}
    (Ω : Opens (Fin N → ℝ)) (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) {a b t B F : ℝ}
    (α : ℝ → (Fin N → ℝ))
    (hODE : ∀ r ∈ Ioo a b, HasDerivAt α (V (α r)) r)
    (hmem : ∀ r ∈ Ioo a b, α r ∈ Ω)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (n : ℕ) (hn : n + 1 ≤ R)
    (hsegment : ∀ r ∈ Icc (0 : ℝ) 1, r * t ∈ Ioo a b)
    (hVjet : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j ≤ R,
      ‖iteratedFDeriv ℝ j V (α (r * t))‖ ≤ B)
    (hfjet : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j ≤ R,
      ‖iteratedFDeriv ℝ j f (α (r * t))‖ ≤ F) :
    ‖f (α t) - ∑ k ∈ Finset.range (n + 1),
      (t ^ k / (k.factorial : ℝ)) * fieldPower V k f (α 0)‖ ≤
      ((2 ^ R * B) ^ (n + 1) * F) * |t| ^ (n + 1) := by
  apply integralCurve_pullback_taylor_bound Ω V hV α hODE hmem f hf n hsegment
  intro r hr
  have hh := norm_fieldPower_jet_le Ω V hV f hf (hmem _ (hsegment r hr))
    (hVjet r hr) (hfjet r hr) (n + 1) 0 (by simpa using hn)
  simpa only [norm_iteratedFDeriv_zero] using hh
end RothschildStein.G3
