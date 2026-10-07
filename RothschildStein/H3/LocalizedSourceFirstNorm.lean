-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Standing
public import RothschildStein.H3.FrozenHolderMetricNorm
public import RothschildStein.H3.LocalizedSourceHolderNorm
public import RothschildStein.H3.WeakFirstHolderNormFormula
public import RothschildStein.H3.HolderJetSourcePointwise
public import RothschildStein.H3.ControlDistanceGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The actual fixed equation identifies the ordered source.
All lower-order cutoff products are controlled by the complete local
first-order norm of the original input, with both cross terms retained. -/
theorem localized_source_holder_norm_by_first_norm_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (U : Opens (Fin N → ℝ)) {a : ℝ≥0} (ha : 0 < a)
    (u f : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hz : jet [] = u)
    (hj : ∀ I, wordWeight driftWeight I ≤ 2 → hasWeakWordDeriv H.fields U I u (jet I) ∧
      holderENorm (controlDistance univ driftWeight H.fields) a (U : Set (Fin N → ℝ)) (jet I) < ⊤)
    (hf : holderENorm (controlDistance univ driftWeight H.fields) a (U : Set (Fin N → ℝ)) f < ⊤)
    (heq : hasDistributionEquationWithDrift U H.fields (fun i => (H.fields_smooth G i).contDiffOn)
      (Distribution.ofFun U u volume (⊤ : ℕ∞)) f)
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    let metric := gaugeMetric G C.norm C.constant_one C.symmetric
    let normG := fun g : (Fin N → ℝ) → ℝ => @H2.boundedHolderNorm (ControlCarrier N) metric a univ g
    let normU := fun g : (Fin N → ℝ) → ℝ => @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ)) g
    (∀ I, normG (wordDerivative H.fields I φ) < ⊤) →
    normG (fun x => S.leibnizWordValue H.fields [0] jet φ x +
      ∑ i : Fin q, S.leibnizWordValue H.fields [i.succ, i.succ] jet φ x) ≤
      normG φ * normU f +
      (2 * (∑ i : Fin q, normG (wordDerivative H.fields [i.succ] φ)) +
        normG (wordDerivative H.fields [0] φ) +
        (∑ i : Fin q, normG (wordDerivative H.fields [i.succ, i.succ] φ))) *
      holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields) U 1 a u := by
  classical
  let metric := gaugeMetric G C.norm C.constant_one C.symmetric
  let normG := fun g : (Fin N → ℝ) → ℝ => @H2.boundedHolderNorm (ControlCarrier N) metric a univ g
  let normU := fun g : (Fin N → ℝ) → ℝ => @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ)) g
  let ψ := holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields) U 1 a u
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  dsimp only
  intro hφ
  have hfc := S.continuousOn_of_holderENorm_lt_top_on_subset ⊤ D (subset_univ _)
    (show 0 < (a : ℝ) from ha) hf
  have hsource := holderJetSource_eqOn_of_frozen_equation ⊤ U D (subset_univ _) H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) (show 0 < (a : ℝ) from ha) u jet hj f hfc heq
  let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
  have hFnorm : normU F = normU f := by
    dsimp only [normU]
    rw [← frozen_holderENorm_eq_control_norm G driftWeight H.fields C,
      ← frozen_holderENorm_eq_control_norm G driftWeight H.fields C]
    exact S.holderENorm_congr _ a (U : Set (Fin N → ℝ)) F hsource
  have hfU : normU f < ⊤ := by
    dsimp only [normU]
    rw [← frozen_holderENorm_eq_control_norm G driftWeight H.fields C]
    exact hf
  have huU : normU u < ⊤ := by
    dsimp only [normU]
    rw [← frozen_holderENorm_eq_control_norm G driftWeight H.fields C, ← hz]
    exact (hj [] (by simp [wordWeight])).2
  have hji (i : Fin q) : normU (jet [i.succ]) < ⊤ := by
    dsimp only [normU]
    rw [← frozen_holderENorm_eq_control_norm G driftWeight H.fields C]
    exact (hj [i.succ] (by simp [wordWeight, driftWeight])).2
  have hb := localized_source_holder_norm_le_of_controlNorm G H.fields C u φ jet hz
    φ.hasCompactSupport (U : Set (Fin N → ℝ)) U.isOpen φ.tsupport_subset hφ huU hji
    (hFnorm.trans_lt hfU)
  have hfirst := holderXENorm_drift_one_eq_of_weak_jets ⊤ U D (subset_univ _) H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) (show 0 < (a : ℝ) from ha) u jet hz
    (fun I hI => hj I (by omega))
  dsimp only [D, controlDistanceGeometry_of_controlNorm] at hfirst
  simp_rw [frozen_holderENorm_eq_control_norm G driftWeight H.fields C] at hfirst
  have huψ : normU u ≤ ψ := by rw [show ψ = normU u + ∑ i : Fin q, normU (jet [i.succ]) from hfirst]; exact le_self_add
  have hiψ (i : Fin q) : normU (jet [i.succ]) ≤ ψ :=
    (Finset.single_le_sum (f := fun j : Fin q => normU (jet [j.succ]))
      (fun _ _ => zero_le) (Finset.mem_univ i)).trans
      (by rw [show ψ = normU u + ∑ i : Fin q, normU (jet [i.succ]) from hfirst]; exact le_add_self)
  have hcross : (∑ i : Fin q, normG (wordDerivative H.fields [i.succ] φ) * normU (jet [i.succ])) ≤
      (∑ i : Fin q, normG (wordDerivative H.fields [i.succ] φ)) * ψ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (hiψ i)
  change normG _ ≤ normG φ * normU F +
    2 * (∑ i : Fin q, normG (wordDerivative H.fields [i.succ] φ) * normU (jet [i.succ])) +
    (normG (wordDerivative H.fields [0] φ) +
      ∑ i : Fin q, normG (wordDerivative H.fields [i.succ, i.succ] φ)) * normU u at hb
  rw [hFnorm] at hb
  exact hb.trans ((add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hcross))
    (mul_le_mul' le_rfl huψ)).trans_eq (by dsimp only [normG, normU, ψ]; ring))

end RothschildStein.H3
