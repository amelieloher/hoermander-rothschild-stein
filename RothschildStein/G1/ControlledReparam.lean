-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledBasics
public import RothschildStein.G1.AffineAbsoluteContinuity
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology BigOperators ENNReal

namespace RothschildStein.G1

/-- Nondegenerate affine time changes are quasi-measure-preserving
on their restricted interval domains (BB pp. 18–19, 22). -/
theorem affine_quasiMeasurePreserving {c d : ℝ} (hd : d ≠ 0)
    (hmap : MapsTo (fun t => c + d * t) (Icc 0 1) (Icc 0 1)) :
    QuasiMeasurePreserving (fun t => c + d * t)
      (volume.restrict (Icc (0 : ℝ) 1)) (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hmul : QuasiMeasurePreserving (fun t : ℝ => d * t) volume volume :=
    quasiMeasurePreserving_smul volume hd
  exact ((quasiMeasurePreserving_add_left volume c).comp hmul).restrict hmap

/-- Actual affine reparameterization of a controlled absolutely
continuous curve. Controls become d*a_i(c+d*t); the weight-dependent scaling
is kept explicit (BB Rem 1.33, Prop 1.36, Rem 1.39). -/
theorem isControlledCurve_comp_affine {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ ε c d : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ)
    (hε : 0 < ε) (hd : d ≠ 0)
    (hmap : MapsTo (fun t => c + d * t) (Icc 0 1) (Icc 0 1))
    (hscale : ∀ i, |d| * δ ^ (w i : ℕ) ≤ ε ^ (w i : ℕ)) :
    isControlledCurve Ω w X ε (fun t => γ (c + d * t)) := by
  obtain ⟨hδ, hac, hrange, a, hmeas, ha⟩ := hγ
  have hq := affine_quasiMeasurePreserving hd hmap
  have hends : uIcc (c + d * 0) (c + d * 1) ⊆ uIcc (0 : ℝ) 1 := by
    have h0 := hmap (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    have h1 := hmap (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    simpa only [uIcc_of_le zero_le_one] using uIcc_subset_Icc h0 h1
  refine ⟨hε, absolutelyContinuousOnInterval_comp_affine hd (hac.mono hends),
    fun t ht => hrange (hmap ht), fun i t => d * a i (c + d * t),
    fun i => ((hmeas i).comp_quasiMeasurePreserving hq).const_mul d, ?_⟩
  filter_upwards [hq.ae ha] with t ht
  refine ⟨fun i => ?_, ?_⟩
  · rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (ht.1 i) (abs_nonneg d)).trans (hscale i)
  · have hdt : HasDerivAt (fun v : ℝ => c + d * v) d t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul d).const_add c
    have hh := ht.2.scomp t hdt
    simpa only [Function.comp_def, Finset.smul_sum, smul_smul, smul_eq_mul] using hh

/-- Reversing a controlled curve preserves its parameter and reverses
its endpoints, without a rank hypothesis (BB Prop 1.41, p. 22). -/
theorem isControlledCurve_reverse {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ) :
    isControlledCurve Ω w X δ (fun t => γ (1 - t)) := by
  have h := isControlledCurve_comp_affine (c := 1) (d := -1) hγ hγ.1 (by norm_num)
    (fun t ht => by constructor <;> dsimp <;> linarith [ht.1, ht.2])
    (fun i => by simp)
  simpa only [neg_one_mul, ← sub_eq_add_neg] using h

/-- Symmetry of the extended control distance follows from actual
curve reversal (BB Prop 1.41, p. 22). -/
theorem controlDistance_symm {m n : ℕ} (Ω : Set (Fin n → ℝ))
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x y : Fin n → ℝ) :
    controlDistance Ω w X x y = controlDistance Ω w X y x := by
  suffices ∀ x y, controlDistance Ω w X x y ≤ controlDistance Ω w X y x from
    le_antisymm (this x y) (this y x)
  intro x y
  apply le_sInf
  rintro r ⟨δ, rfl, γ, hγ, hzero, hone⟩
  have h := controlDistance_le_of_curve (isControlledCurve_reverse hγ)
  simpa only [sub_zero, sub_self, hzero, hone] using h

end RothschildStein.G1
