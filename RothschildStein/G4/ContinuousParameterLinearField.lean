-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LinearFieldDerivative
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Monoid

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- A finite coefficient-linear field is jointly continuous
in external parameters, coefficients and spatial coordinates whenever
its actual fields are jointly continuous (BB p. 452). -/
theorem parameter_linear_field_joint_continuousOn {P E : Type*} {m : ℕ}
    [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set P} {Ω : Set E} (Y : P → Fin m → E → E)
    (hY : ∀ J, ContinuousOn (fun q : P × E => Y q.1 J q.2) (U ×ˢ Ω)) :
    ContinuousOn (fun q : P × ((Fin m → ℝ) × E) => ∑ J, q.2.1 J • Y q.1 J q.2.2)
      (U ×ˢ (univ ×ˢ Ω)) := by
  have hmap : MapsTo (fun q : P × ((Fin m → ℝ) × E) => (q.1, q.2.2))
      (U ×ˢ (univ ×ˢ Ω)) (U ×ˢ Ω) := fun q hq => ⟨hq.1, hq.2.2⟩
  apply continuousOn_finsetSum
  intro J _hJ
  have hvalue := (hY J).comp (continuous_fst.prodMk continuous_snd.snd).continuousOn
    hmap
  exact ((continuous_apply J).comp continuous_snd.fst).continuousOn.smul hvalue

/-- The actual coefficient/state derivative of a finite
coefficient-linear field is jointly continuous under joint continuity
of the fields and their actual spatial derivatives. External parameters
are only topological; the derivative is solely in the state (BB p. 452). -/
theorem parameter_linear_field_state_derivative_joint_continuousOn {P E : Type*} {m : ℕ}
    [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set P} {Ω : Set E} (Y : P → Fin m → E → E)
    (hY : ∀ J, ContinuousOn (fun q : P × E => Y q.1 J q.2) (U ×ˢ Ω))
    (hDY : ∀ J, ContinuousOn (fun q : P × E => fderiv ℝ (Y q.1 J) q.2) (U ×ˢ Ω))
    (hDiff : ∀ p ∈ U, ∀ y ∈ Ω, ∀ J, DifferentiableAt ℝ (Y p J) y) :
    ContinuousOn
      (fun q : P × ((Fin m → ℝ) × E) =>
        fderiv ℝ (fun z : (Fin m → ℝ) × E => ∑ J, z.1 J • Y q.1 J z.2) q.2)
      (U ×ˢ (univ ×ˢ Ω)) := by
  have hmap : MapsTo (fun q : P × ((Fin m → ℝ) × E) => (q.1, q.2.2))
      (U ×ˢ (univ ×ˢ Ω)) (U ×ˢ Ω) := fun q hq => ⟨hq.1, hq.2.2⟩
  let C : Fin m → ((Fin m → ℝ) × E) →L[ℝ] ℝ := fun J =>
    (ContinuousLinearMap.proj J).comp (ContinuousLinearMap.fst ℝ (Fin m → ℝ) E)
  let L := (ContinuousLinearMap.compL ℝ ((Fin m → ℝ) × E) E E).flip
    (ContinuousLinearMap.snd ℝ (Fin m → ℝ) E)
  let R : Fin m → E →L[ℝ] ((Fin m → ℝ) × E) →L[ℝ] E := fun J =>
    ContinuousLinearMap.smulRightL ℝ ((Fin m → ℝ) × E) E (C J)
  let D : P × ((Fin m → ℝ) × E) → ((Fin m → ℝ) × E) →L[ℝ] E := fun q =>
    ∑ J, (q.2.1 J • L (fderiv ℝ (Y q.1 J) q.2.2) + R J (Y q.1 J q.2.2))
  have hD : ContinuousOn D (U ×ˢ (univ ×ˢ Ω)) := by
    dsimp only [D]
    apply continuousOn_finsetSum
    intro J _hJ
    have hvalue := (hY J).comp (continuous_fst.prodMk continuous_snd.snd).continuousOn
      hmap
    have hder := (hDY J).comp (continuous_fst.prodMk continuous_snd.snd).continuousOn
      hmap
    exact (((continuous_apply J).comp continuous_snd.fst).continuousOn.smul
      (L.continuous.comp_continuousOn hder)).add ((R J).continuous.comp_continuousOn hvalue)
  apply hD.congr
  intro q hq
  apply ContinuousLinearMap.ext
  intro z
  simp only [D, L, R, C, sum_apply, add_apply,
    smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.coe_snd']
  exact linear_field_family_fderiv (Y q.1) q.2 z (hDiff q.1 hq.1 q.2.2 hq.2.2)

end RothschildStein.G4
