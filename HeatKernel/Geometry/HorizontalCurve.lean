-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Definitions.horizontalL2Distance
public import HeatKernel.Geometry.CurveReparametrization

/-! Horizontal curves, reversal, and their control length. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace HeatKernel

/-- The Euclidean norm of a finite control vector. -/
def controlNorm {q : ℕ} (a : Fin q → ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (∑ i, a i t ^ 2)

/-- Absolute continuity and the almost-everywhere horizontal differential equation
on a closed parameter interval. -/
structure IsHorizontalCurveOn {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (γ : ℝ → (Fin N → ℝ)) (a : Fin q → ℝ → ℝ) (s t : ℝ) : Prop where
  absolutelyContinuous : AbsolutelyContinuousOnInterval γ s t
  aemeasurable : ∀ i, AEMeasurable (a i) (volume.restrict (Icc s t))
  integrable_norm : IntegrableOn (controlNorm a) (Icc s t)
  hasDerivAt : ∀ᵐ u ∂volume.restrict (Icc s t), HasDerivAt γ (∑ i, a i u • X i (γ u)) u

/-- A constant curve is horizontal with zero controls. -/
theorem isHorizontalCurveOn_const {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) (s t : ℝ) :
    IsHorizontalCurveOn X (fun _ => x) (fun _ _ => 0) s t := by
  refine ⟨(LipschitzWith.const x).lipschitzOnWith.absolutelyContinuousOnInterval,
    fun _ => aemeasurable_const, ?_, ?_⟩
  · have hz : controlNorm (fun (_ : Fin q) (_ : ℝ) => (0 : ℝ)) = fun _ => 0 := by
      funext u
      simp [controlNorm]
    rw [hz]
    exact integrableOn_zero
  · exact Filter.Eventually.of_forall fun u => by simpa using hasDerivAt_const u x

/-- Every horizontal competitor bounds the horizontal distance by its control length. -/
theorem horizontalL2Distance_le_controlLength {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} (h : IsHorizontalCurveOn X γ a 0 1) :
    horizontalL2Distance X (γ 0) (γ 1) ≤ ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, controlNorm a t) := by
  apply sInf_le
  exact ⟨γ, a, h.absolutelyContinuous, rfl, rfl, h.aemeasurable, h.integrable_norm,
    h.hasDerivAt, rfl⟩

/-- The horizontal control distance vanishes on the diagonal. -/
@[simp] theorem horizontalL2Distance_self {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) :
    horizontalL2Distance X x x = 0 := by
  apply le_antisymm _ bot_le
  simpa [controlNorm] using horizontalL2Distance_le_controlLength (isHorizontalCurveOn_const X x 0 1)

private theorem measurePreserving_reflection (s t : ℝ) :
    MeasurePreserving (fun u : ℝ => s + t - u)
      (volume.restrict (Icc s t)) (volume.restrict (Icc s t)) := by
  have hp : (fun u : ℝ => s + t - u) ⁻¹' Icc s t = Icc s t := by
    ext u
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simpa only [hp] using (volume.measurePreserving_sub_left (s + t)).restrict_preimage
    (measurableSet_Icc : MeasurableSet (Icc s t))

/-- Reversing a horizontal curve negates and reverses its controls. -/
theorem IsHorizontalCurveOn.reverse {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t : ℝ} (h : IsHorizontalCurveOn X γ a s t) :
    IsHorizontalCurveOn X (fun u => γ (s + t - u)) (fun i u => -a i (s + t - u)) s t := by
  let r : ℝ → ℝ := fun u => s + t - u
  have hmp : MeasurePreserving r (volume.restrict (Icc s t))
      (volume.restrict (Icc s t)) := measurePreserving_reflection s t
  have hK : LipschitzOnWith 1 r (uIcc s t) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u _ v _
    simp only [r, NNReal.coe_one, one_mul, Real.dist_eq]
    rw [show s + t - u - (s + t - v) = -(u - v) by ring, abs_neg]
  refine ⟨absolutelyContinuousOnInterval_comp_of_monotone h.absolutelyContinuous
    (Or.inr (by intro u v huv; change s + t - v ≤ s + t - u; linarith)) hK ?_, ?_, ?_, ?_⟩
  · intro u hu
    simp only [uIcc, mem_Icc] at hu ⊢
    change min s t ≤ s + t - u ∧ s + t - u ≤ max s t
    constructor <;> (simp only [min_def, max_def] at *; split_ifs at * <;> linarith)
  · intro i
    exact ((h.aemeasurable i).comp_quasiMeasurePreserving hmp.quasiMeasurePreserving).neg
  · change Integrable (fun u => Real.sqrt (∑ i, (-a i (s + t - u)) ^ 2))
      (volume.restrict (Icc s t))
    simpa only [controlNorm, neg_sq, Function.comp_def, r] using
      hmp.integrable_comp_of_integrable h.integrable_norm
  · filter_upwards [hmp.quasiMeasurePreserving.ae h.hasDerivAt] with u hu
    have hd := hu.scomp u ((hasDerivAt_id u).const_sub (s + t))
    simpa only [Function.comp_def, r, neg_smul, Finset.sum_neg_distrib,
      neg_one_smul, one_smul] using hd

/-- Reversal preserves the integral of the Euclidean control norm. -/
theorem controlLength_reverse {q : ℕ} (a : Fin q → ℝ → ℝ) (s t : ℝ) :
    (∫ u in Icc s t, controlNorm (fun i v => -a i (s + t - v)) u) =
      ∫ u in Icc s t, controlNorm a u := by
  simpa only [controlNorm, neg_sq] using
    (measurePreserving_reflection s t).integral_comp
      (Homeomorph.subLeft (s + t)).measurableEmbedding (controlNorm a)

/-- The horizontal control distance is symmetric, including when its value is infinite. -/
theorem horizontalL2Distance_comm {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (x y : Fin N → ℝ) :
    horizontalL2Distance X x y = horizontalL2Distance X y x := by
  have hle : ∀ x y, horizontalL2Distance X y x ≤ horizontalL2Distance X x y := by
    intro x y
    apply le_sInf
    rintro r ⟨γ, a, hac, hzero, hone, hmeas, hint, hderiv, rfl⟩
    have hc : IsHorizontalCurveOn X γ a 0 1 := ⟨hac, hmeas, hint, hderiv⟩
    have hbound := horizontalL2Distance_le_controlLength hc.reverse
    rw [controlLength_reverse] at hbound
    simpa only [zero_add, sub_zero, sub_self, hzero, hone, controlNorm] using hbound
  exact le_antisymm (hle y x) (hle x y)

end HeatKernel
