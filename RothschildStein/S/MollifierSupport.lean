-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierConvergence
public import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric
namespace RothschildStein.S
variable {n : ℕ}

/-- Nonzero regularized values lie within ε of the input support
(BB Lemma 2.8, pp. 72–73; explicit support calculation). -/
theorem support_euclideanRegularize_subset (hn : 0 < n)
    (f : (Fin n → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    support (euclideanRegularize n f ε) ⊆ cthickening ε (tsupport f) := by
  intro x hx
  rw [← additiveRegularize_eq hn] at hx
  have hs := RothschildStein.G2.support_groupConvolution_subset
    (additiveCoordinateGroup hn) _ f hx
  rcases hs with ⟨⟨y,z⟩, ⟨hy,hz⟩, rfl⟩
  have hyb : ‖y‖ < ε :=
    RothschildStein.G2.support_groupMollifierScale_subset
      (additiveCoordinateGroup hn) (euclideanGroupMollifier hn) hε hy
  apply mem_cthickening_of_dist_le _ z ε _ (subset_closure hz)
  change dist ((additiveCoordinateGroup hn).mul y z) z ≤ ε
  rw [additiveCoordinateGroup_mul,dist_eq_norm,add_sub_cancel_right]
  exact hyb.le

/-- Taking the closure preserves the closed thickening bound
(BB Lemma 2.8, pp. 72–73). -/
theorem tsupport_euclideanRegularize_subset (hn : 0 < n)
    (f : (Fin n → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    tsupport (euclideanRegularize n f ε) ⊆ cthickening ε (tsupport f) :=
  closure_minimal (support_euclideanRegularize_subset hn f hε) isClosed_cthickening

/-- Compact support strictly inside an open set stays inside it
for every sufficiently small mollification parameter (BB Lemma 2.8, pp. 72–73). -/
theorem exists_euclideanRegularize_support_inside (hn : 0 < n)
    {f : (Fin n → ℝ) → ℝ} (hcf : HasCompactSupport f)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hfΩ : tsupport f ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      tsupport (euclideanRegularize n f ε) ⊆ Ω := by
  obtain ⟨δ,hδ,hdΩ⟩ := hcf.isCompact.exists_cthickening_subset_open hΩ hfΩ
  refine ⟨δ,hδ,?_⟩
  intro ε hε he
  exact (tsupport_euclideanRegularize_subset hn f hε).trans
    ((cthickening_mono he (tsupport f)).trans hdΩ)

end RothschildStein.S
