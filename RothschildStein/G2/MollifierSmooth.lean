-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ConvolutionSmooth
public import RothschildStein.G2.MollifierIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}

/-- Every Lp input with p at least one has a smooth group
regularization (BB Prop 3.48, p. 121; BB kernel estimate). -/
theorem contDiff_groupRegularize (φ : GroupMollifier G ν) {ε : ℝ} (hε : 0 < ε)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : (Fin N → ℝ) → ℝ} (hf : MemLp f p volume) :
    ContDiff ℝ (⊤ : ℕ∞) (groupRegularize G φ f ε) :=
  contDiff_groupConvolution_left G (contDiff_groupMollifierScale G φ ε)
    (hasCompactSupport_groupMollifierScale G φ hε) (hf.locallyIntegrable hp)

/-- A compactly supported Lp input has a compact smooth
regularization (BB Prop 3.48, p. 121). -/
theorem contDiff_hasCompactSupport_groupRegularize (φ : GroupMollifier G ν)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : (Fin N → ℝ) → ℝ} (hf : MemLp f p volume) (hcf : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (groupRegularize G φ f ε) ∧
      HasCompactSupport (groupRegularize G φ f ε) :=
  ⟨contDiff_groupRegularize G φ hε hp hf, hasCompactSupport_groupRegularize G φ hε hcf⟩

end RothschildStein.G2
