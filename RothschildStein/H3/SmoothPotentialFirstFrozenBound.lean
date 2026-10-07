-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalPotentialFirstBound
public import RothschildStein.H3.SmoothFundamentalPotentialJets
public import RothschildStein.H3.FirstHolderNormFormula
public import RothschildStein.H3.ControlHolderFrozenBridge
public import RothschildStein.H3.QuasiballDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- A smooth compact source gives the exact full fixed
first-order Hölder bound for its actual fundamental potential on a
control ball. The potential itself may have noncompact support. -/
theorem smooth_potential_first_holderX_bound_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Fin N → ℝ, ∀ φ : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ G2.gaugeBall G Hc.norm z ρ →
      holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G Hc.norm z ρ) 1 (α : ℝ) (G2.groupConvolution G φ K) ≤
        ENNReal.ofReal (C * lpNorm φ ∞ volume) := by
  classical
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  obtain ⟨C, hC, hbound⟩ :=
    fundamental_potential_first_holder_bound_of_controlNorm G H K Hc hQ ν hν hα hα1 hρ
  refine ⟨C, hC, ?_⟩
  intro z φ hφ hsφ hsupport
  let U := quasiballDomain G Hc.norm z ρ
  let v := G2.groupConvolution G φ K
  let jet := fun I => wordDerivative H.fields I v
  let first := fun i : Fin q => G2.groupConvolution G φ (fieldDerivative (H.fields i.succ) K)
  let normA := fun f : (Fin N → ℝ) → ℝ =>
    @H2.boundedHolderNorm (ControlCarrier N) metric α (U : Set (Fin N → ℝ)) (fun x => f x)
  have hb := hbound z φ hφ.continuous hsφ hsupport
  change normA v + (∑ i : Fin q, normA (first i)) ≤ ENNReal.ofReal (C * lpNorm φ ∞ volume) at hb
  have ht : normA v + (∑ i : Fin q, normA (first i)) < ⊤ := hb.trans_lt ENNReal.ofReal_lt_top
  have hvnorm : normA v < ⊤ := (le_add_right le_rfl).trans_lt ht
  have hfnorm (i : Fin q) : normA (first i) < ⊤ :=
    (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)).trans_lt
      ((le_add_left le_rfl).trans_lt ht)
  have hp := (Classical.choose_spec (convolution_formulas_of_fundamental_kernel G H K hQ)).2 φ hφ hsφ
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hp.1
  have hX (i : Fin (q + 1)) := (H.fields_smooth G i).contDiffOn (s := (U : Set (Fin N → ℝ)))
  have hi (i : Fin q) : hasIntrinsicWordDeriv H.fields U [i.succ] v (first i) := by
    have hh := S.hasIntrinsicWordDeriv_of_continuous_weak_subwords U H.fields hX
      [i.succ] v jet rfl
      (fun J _ => S.hasWeakWordDeriv_classical U H.fields hX J v hv.contDiffOn)
      (fun J _ => (S.contDiffOn_wordDerivative U H.fields hX J v hv.contDiffOn).continuousOn)
    have he : jet [i.succ] = first i := hp.2.2.2.1 i
    rwa [he] at hh
  have hn := holderENorm_control_eq_of_controlNorm G Hc (H2.BoundedHolder.parts hvnorm).2
  have hf (i : Fin q) := holderENorm_control_eq_of_controlNorm G Hc (H2.BoundedHolder.parts (hfnorm i)).2
  rw [holderXENorm_drift_one_eq H.fields (controlDistance univ driftWeight H.fields)
    U (α : ℝ) v first hi]
  change holderENorm (controlDistance univ driftWeight H.fields) (α : ℝ) (U : Set (Fin N → ℝ)) v +
    (∑ i : Fin q, holderENorm (controlDistance univ driftWeight H.fields) (α : ℝ)
      (U : Set (Fin N → ℝ)) (first i)) ≤ _
  rw [hn]
  simp only [hf]
  exact hb

end RothschildStein.H3
