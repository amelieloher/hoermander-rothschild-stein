-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.AdjointTest
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

noncomputable section

open Filter Function Set Topology
open scoped BigOperators

namespace Hormander.F

/-- The divergence of a localized smooth vector field obeys the
pointwise product rule on the whole carrier, including points outside the smoothness domain. -/
theorem localizedDivergence_product_rule {N : ℕ} {Ω : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hK : tsupport φ ⊆ Ω) (x : Fin N → ℝ) :
    Hormander.Interface.euclideanDivergence (fun y => φ y • V y) x =
      fderiv ℝ φ x (V x) + φ x * Hormander.Interface.euclideanDivergence V x := by
  by_cases hxΩ : x ∈ Ω
  · have hφx : DifferentiableAt ℝ φ x := hφ.contDiffAt.differentiableAt (by simp)
    have hVx : DifferentiableAt ℝ V x :=
      (hV.contDiffAt (hΩ.mem_nhds hxΩ)).differentiableAt (by simp)
    have hdecomp : V x = ∑ i : Fin N, V x i • Hormander.Interface.basisVec i := by
      ext j
      simp [Hormander.Interface.basisVec, Pi.single_apply]
    change ∑ i : Fin N, fderiv ℝ (φ • V) x (Hormander.Interface.basisVec i) i =
      fderiv ℝ φ x (V x) + φ x *
        ∑ i : Fin N, fderiv ℝ V x (Hormander.Interface.basisVec i) i
    rw [fderiv_smul hφx hVx]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply, Pi.add_apply,
      smul_apply, Pi.smul_apply, smul_eq_mul]
    have hlinear :
        ∑ i : Fin N, fderiv ℝ φ x (Hormander.Interface.basisVec i) * V x i =
          fderiv ℝ φ x (V x) := by
      calc
        ∑ i : Fin N, fderiv ℝ φ x (Hormander.Interface.basisVec i) * V x i
            = ∑ i : Fin N,
                fderiv ℝ φ x (V x i • Hormander.Interface.basisVec i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [map_smul]
                  ring
        _ = fderiv ℝ φ x (∑ i : Fin N, V x i • Hormander.Interface.basisVec i) := by
              rw [map_sum]
        _ = fderiv ℝ φ x (V x) := congrArg (fderiv ℝ φ x) hdecomp.symm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hlinear]
    ring
  · have hxK : x ∉ tsupport φ := fun hxs => hxΩ (hK hxs)
    have hxS : x ∉ support φ := fun hxs => hxK (subset_closure hxs)
    have hφx : φ x = 0 := by
      simpa only [mem_support, not_not] using hxS
    have hφlocal : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      (notMem_tsupport_iff_eventuallyEq).mp hxK
    have hφderiv := hφlocal.fderiv_eq (𝕜 := ℝ)
    rw [localizedDivergence_zero_outside V φ hxK, hφderiv]
    simp [hφx]

/-- The first-order formal transpose equals both its divergence
formula and the expanded derivative formula at every point. -/
theorem firstOrderTranspose_formula {N : ℕ} {Ω : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hK : tsupport φ ⊆ Ω) (x : Fin N → ℝ) :
    -Hormander.Interface.euclideanDivergence (fun y => φ y • V y) x =
      -fderiv ℝ φ x (V x) - φ x * Hormander.Interface.euclideanDivergence V x := by
  rw [localizedDivergence_product_rule hΩ V hV φ hφ hK x]
  ring

end Hormander.F
