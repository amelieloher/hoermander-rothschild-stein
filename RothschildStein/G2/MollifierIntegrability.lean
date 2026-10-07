-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierScale
public import RothschildStein.G2.YoungEndpoint
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}

/-- Every scaled group bump belongs to all Lp spaces
(BB p. 121; compact smoothness). -/
theorem memLp_groupMollifierScale (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) (p : ℝ≥0∞) : MemLp (groupMollifierScale G φ ε) p volume :=
  (contDiff_groupMollifierScale G φ ε).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_groupMollifierScale G φ hε)

/-- Regularization of any Lp function, p at least one, has an
absolutely convergent integral at every point (BB p. 121). -/
theorem groupRegularize_existsAt (φ : GroupMollifier G ν) {ε : ℝ} (hε : 0 < ε)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : (Fin N → ℝ) → ℝ} (hf : MemLp f p volume)
    (x : Fin N → ℝ) : GroupConvolutionExistsAt G (groupMollifierScale G φ ε) f x := by
  let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have hi : p⁻¹ ≤ 1 := by simpa using ENNReal.inv_le_inv.mpr hp
  let : q.HolderConjugate p := ENNReal.holderConjugate_iff.mpr (by
    change (1 - p⁻¹)⁻¹⁻¹ + p⁻¹ = 1
    simpa using tsub_add_cancel_of_le hi)
  exact groupConvolutionExistsAt_of_memLp_conjugate G
    (memLp_groupMollifierScale G φ hε q) hf x

/-- A compactly supported input has compactly supported
regularization (BB p. 121). -/
theorem hasCompactSupport_groupRegularize (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) {f : (Fin N → ℝ) → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (groupRegularize G φ f ε) :=
  hasCompactSupport_groupConvolution G (hasCompactSupport_groupMollifierScale G φ hε) hf

end RothschildStein.G2
