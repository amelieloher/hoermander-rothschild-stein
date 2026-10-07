-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderFiniteCoverEstimate
public import RothschildStein.H3.BufferedGaugeCover

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The uniform interior estimate for actual fixed Holder
solutions. The compact buffered cover and its positive pair radius are
constructed from the domains; the constant precedes all inputs. -/
theorem interior_holder_estimate_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (μ : G2.GroupMollifier G H.norm) (φ : G2.GroupMollifier G C.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (U E : Opens (Fin N → ℝ))
    (hK : IsCompact (closure (E : Set (Fin N → ℝ))))
    (hKU : closure (E : Set (Fin N → ℝ)) ⊆ U)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ u f : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U 2 a u →
      holderENorm (controlDistance univ driftWeight H.fields) a (U : Set (Fin N → ℝ)) f < ⊤ →
      hasDistributionEquationWithDrift U H.fields (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun U u volume (⊤ : ℕ∞)) f →
      holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields) E 2 a u ≤
        ENNReal.ofReal B * (holderENorm (controlDistance univ driftWeight H.fields) a
          (U : Set (Fin N → ℝ)) f + eLpNorm u ⊤ (volume.restrict (U : Set (Fin N → ℝ)))) := by
  obtain ⟨c, b, hc, hb, hcmp⟩ := G2.gauges_equivalent C.norm.gauge ν.gauge
  let c' := min 1 c
  let b' := max 1 b
  have hc' : 0 < c' := lt_min zero_lt_one hc
  have hb' : 0 < b' := zero_lt_one.trans_le (le_max_left _ _)
  have hcmp' : ∀ x, c' * C.norm x ≤ ν x ∧ ν x ≤ b' * C.norm x := by
    intro x
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (C.norm.gauge.2.1 x)).trans (hcmp x).1,
      ((hcmp x).2).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (C.norm.gauge.2.1 x))⟩
  obtain ⟨r, ell, hr, _hr1, hell, S, hcover, hballs, hpairs⟩ :=
    buffered_quasiBall_cover_of_controlNorm C ν hc' hb' hcmp' hK U.isOpen hKU
  have hCb : 1 ≤ b' / c' := (le_div_iff₀ hc').mpr (by
    simpa only [one_mul] using (min_le_left 1 c).trans (le_max_left 1 b))
  have hrad : r / (2 * (b' / c')) ≤ r := div_le_self hr.le (by linarith)
  let centers : {z : closure (E : Set (Fin N → ℝ)) // z ∈ S} → Fin N → ℝ := fun z => z.val.val
  apply finite_cover_estimate_of_controlNorm G H K hQ C μ φ ν hν U E
    (subset_closure.trans hKU) ha ha1 centers hr hell
  · intro z
    exact hballs z.val z.property
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := hcover x (subset_closure hx)
    exact ⟨⟨z, hz⟩, hxz.trans_le hrad⟩
  · intro x hx y _hy hxy
    obtain ⟨z, hz, hxz, hyz⟩ := hpairs x (subset_closure hx) y hxy
    exact ⟨⟨z, hz⟩, hxz.trans_le hrad, hyz⟩

end RothschildStein.H3
