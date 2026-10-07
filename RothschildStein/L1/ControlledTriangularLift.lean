-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.TriangularVerticalConstruction
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators

namespace RothschildStein.L1

/-- Every already given admissible base curve has an admissible
triangular lift on the entire interval, starting at any vertical
point and with the same control radius. -/
theorem exists_controlled_triangularLift {q n m : ℕ} {Ω : Set (Fin n → ℝ)}
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin q → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hP : ∀ i l, ∀ j ∈ (P i l).vars, j.val < n + l.val)
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ)
    (z : Fin m → ℝ) :
    ∃ ξ : ℝ → (Fin (n + m) → ℝ),
      isControlledCurve (basePoint ⁻¹' Ω) w (triangularLift X P) δ ξ ∧
      ξ 0 = joinPoint (γ 0) z ∧ ∀ t, basePoint (ξ t) = γ t := by
  classical
  obtain ⟨c, hc, hd⟩ := hγ.2.2.2
  have hcc : ∀ i, AEMeasurable (c i) (volume.restrict (uIcc (0 : ℝ) 1)) := by
    simpa only [uIcc_of_le zero_le_one] using hc
  have hcb : ∀ i, ∀ᵐ t ∂volume.restrict (uIcc (0 : ℝ) 1),
      |c i t| ≤ δ ^ (w i : ℕ) := by
    intro i
    simpa only [uIcc_of_le zero_le_one] using hd.mono (fun t ht => ht.1 i)
  have hcont : ContinuousOn γ (uIcc (0 : ℝ) 1) := hγ.2.1.continuousOn
  obtain ⟨v, hv, hvz, hvd⟩ := exists_triangular_vertical_curve P hP γ hcont
    c (fun i => δ ^ (w i : ℕ)) hcc hcb z
  let ξ : ℝ → (Fin (n + m) → ℝ) := fun t => joinPoint (γ t) (v t)
  have hbase : ∀ t, basePoint (ξ t) = γ t := by
    intro t
    ext j
    simp only [ξ, joinPoint, basePoint, Fin.addCases_left]
  have hac : AbsolutelyContinuousOnInterval ξ 0 1 := by
    apply absolutelyContinuousOnInterval_of_coordinates
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      have hk := G1.absolutelyContinuousOnInterval_comp_contDiffOn isOpen_univ
        (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ).contDiff.contDiffOn
        hγ.2.1 (mapsTo_univ _ _)
      simpa only [ξ, joinPoint, Fin.addCases_left, Function.comp_def,
        ContinuousLinearMap.proj_apply] using hk
    · intro k
      simpa only [ξ, joinPoint, Fin.addCases_right] using hv k
  have hdv : ∀ᵐ t ∂volume, ∀ l, t ∈ uIcc (0 : ℝ) 1 →
      HasDerivAt (fun t => v t l)
        (∑ i, c i t * MvPolynomial.eval (ξ t) (P i l)) t := ae_all_iff.mpr hvd
  refine ⟨ξ, ⟨hγ.1, hac, ?_, c, hc, ?_⟩, ?_, hbase⟩
  · intro t ht
    change basePoint (ξ t) ∈ Ω
    rw [hbase t]
    exact hγ.2.2.1 ht
  · filter_upwards [hd, ae_restrict_of_ae hdv, ae_restrict_mem measurableSet_Icc]
      with t ht hvt htime
    refine ⟨ht.1, hasDerivAt_pi.mpr ?_⟩
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      have hk := (hasDerivAt_pi.mp ht.2) k
      simpa only [ξ, joinPoint, triangularLift, Fin.addCases_left,
        Finset.sum_apply, Pi.smul_apply, hbase t] using hk
    · intro k
      have hk := hvt k (by simpa only [uIcc_of_le zero_le_one] using htime)
      simpa only [ξ, joinPoint, triangularLift, Fin.addCases_right,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hk
  · simp only [ξ, hvz]

end RothschildStein.L1
