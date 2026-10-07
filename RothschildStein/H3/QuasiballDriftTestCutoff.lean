-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballCutoffLowOrder
public import RothschildStein.H3.QuasiballDomain
public import RothschildStein.H3.DriftCutoffCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- The smooth quasiball has an interior test cutoff with a bound for its
complete fixed drift operator. The constants are uniform in centers and
radii, with no operator cutoff estimate as an assumption. -/
theorem exists_quasiball_drift_test_cutoff {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ x₀ : Fin n → ℝ, ∀ t s : ℝ, 0 < t → t < s → s/2 ≤ t →
        ∃ φ : TestFunction (quasiballDomain G ν x₀ s) ℝ (⊤ : ℕ∞),
          EqOn φ 1 (G2.gaugeBall G ν x₀ t) ∧ eLpNorm φ ⊤ volume ≤ 1 ∧
          (∀ i : Fin q, eLpNorm (fieldDerivative (H.fields i.succ) φ) ⊤ volume ≤
            ENNReal.ofReal (c₁/(s-t))) ∧
          eLpNorm (sumSquaresWithDrift H.fields φ) ⊤ volume ≤
            (q+1 : ℝ≥0∞) * ENNReal.ofReal (c₂/(s-t)^2) := by
  obtain ⟨c₁,c₂,hc₁,hc₂,hcut⟩ := exists_quasiball_cutoff_lowOrder G H ν hν
  refine ⟨c₁,c₂,hc₁,hc₂,?_⟩
  intro x₀ t s ht hts hhalf
  obtain ⟨f,hf,hfc,hrange,hone,hsupp,hinside,hfirst,hdrift,hsecond⟩ :=
    hcut x₀ t s ht hts hhalf
  let φ : TestFunction (quasiballDomain G ν x₀ s) ℝ (⊤ : ℕ∞) :=
    ⟨f,hf,hfc,hsupp.trans hinside⟩
  refine ⟨φ,hone,?_,hfirst,?_⟩
  · change eLpNorm f ⊤ volume ≤ 1
    rw [eLpNorm_exponent_top hf.continuous.aestronglyMeasurable]
    have hb : eLpNormEssSup f volume ≤ ENNReal.ofReal 1 := by
      apply eLpNormEssSup_le_of_ae_bound
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hrange x).1]
        exact (hrange x).2
    simpa using hb
  · exact sumSquaresWithDrift_norm_le_of_field_bounds H.fields f volume ⊤ (by simp)
      (ENNReal.ofReal (c₂/(s-t)^2)) hdrift (fun i => hsecond i i)

end RothschildStein.H3
