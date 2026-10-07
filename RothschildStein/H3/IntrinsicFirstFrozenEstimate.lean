-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicWeakHolderExport
public import RothschildStein.S.HolderWeakLocality
public import RothschildStein.S.ContinuousCompactZeroExtension
public import RothschildStein.S.ZeroExtension
public import RothschildStein.Definitions.memHolderXCompact
public import RothschildStein.S.WeakIntrinsicWords
public import RothschildStein.S.WeakHolderRepresentatives
public import RothschildStein.S.GroupControlGeometry
public import RothschildStein.H3.ControlHolderFrozenBridge
public import RothschildStein.H3.FirstHolderNormFormula
public import RothschildStein.H3.IntrinsicFirstHolderInterpolation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- Actual global compact intrinsic jets satisfy the
interpolation estimate in the exact fixed first-order norm. The constant
is fixed before every center, input, jet family and parameter. -/
theorem intrinsic_first_holderX_estimate_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (μ : G2.GroupMollifier G H.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Fin N → ℝ,
      ∀ u : (Fin N → ℝ) → ℝ,
      ∀ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
      jet [] = u →
      (∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv H.fields ⊤ I u (jet I)) →
      (∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I)) →
      (∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I)) →
      (∀ I, wordWeight driftWeight I ≤ 2 → tsupport (jet I) ⊆ G2.gaugeBall G Hc.norm z ρ) →
      ∀ η : ℝ, 0 < η → η < 1 →
      let F := fun y => jet [0] y + ∑ i : Fin q, jet [i.succ, i.succ] y
      holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        ⊤ 1 (α : ℝ) u ≤
        ENNReal.ofReal (η * lpNorm F ∞ volume) +
        ENNReal.ofReal (C * η ^ (-(2 * (3 + (G.homogeneousDimension : ℝ)) /
          (1 - (α : ℝ)))) * lpNorm u ∞ volume) := by
  classical
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  obtain ⟨C, hC, hbound⟩ := intrinsic_first_holder_interpolation_of_controlNorm G H K Hc hQ μ ν hν hα hα1 hρ
  refine ⟨C, hC, ?_⟩
  intro z u₀ jet hzero hi hc hs hsupport
  have hb := hbound z u₀ jet hzero hi hc hs hsupport
  let normG := fun f : (Fin N → ℝ) → ℝ =>
    @H2.boundedHolderNorm (ControlCarrier N) metric α univ (fun x => f x)
  have hfinite : normG u₀ + (∑ i : Fin q, normG (jet [i.succ])) < ⊤ :=
    (hb (1 / 2) (by norm_num) (by norm_num)).trans_lt (ENNReal.add_lt_top.mpr
      ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
  have hnil : normG u₀ < ⊤ := (le_add_right le_rfl).trans_lt hfinite
  have hsum : (∑ i : Fin q, normG (jet [i.succ])) < ⊤ := (le_add_left le_rfl).trans_lt hfinite
  have hfirst (i : Fin q) : normG (jet [i.succ]) < ⊤ :=
    (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)).trans_lt hsum
  have hn := holderENorm_control_eq_of_controlNorm G Hc (H2.BoundedHolder.parts hnil).2
  have hf (i : Fin q) := holderENorm_control_eq_of_controlNorm G Hc (H2.BoundedHolder.parts (hfirst i)).2
  have hnorm : holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
      ⊤ 1 (α : ℝ) u₀ = normG u₀ + ∑ i : Fin q, normG (jet [i.succ]) := by
    rw [holderXENorm_drift_one_eq H.fields (controlDistance univ driftWeight H.fields)
      ⊤ (α : ℝ) u₀ (fun i => jet [i.succ]) (fun i => hi _ (by simp [wordWeight, driftWeight]))]
    change holderENorm (controlDistance univ driftWeight H.fields) (α : ℝ) univ u₀ +
      (∑ i : Fin q, holderENorm (controlDistance univ driftWeight H.fields) (α : ℝ) univ
        (jet [i.succ])) = normG u₀ + ∑ i : Fin q, normG (jet [i.succ])
    rw [hn]
    simp only [hf]
    rfl
  intro η hη hη1
  change holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
    ⊤ 1 (α : ℝ) u₀ ≤ _
  rw [hnorm]
  exact hb η hη hη1

end RothschildStein.H3
