-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SmallScaleOptimalFrame
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- Strict suboptimality persists near the reference parameter
at one fixed radius. Lower-weight coefficients may be nonzero nearby
(BB (9.54), pp. 453–454). -/
theorem eventually_strict_weighted_suboptimality {P ι : Type*}
    [TopologicalSpace P] [Fintype ι] (coeff : P → ι → ℝ) (W : ι → ℤ)
    (p₀ : P) (B : ι) {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    (hcoeff : ∀ J, ContinuousAt (fun p => coeff p J) p₀)
    (hB : coeff p₀ B ≠ 0)
    (hopt : ∀ J, |coeff p₀ J| * R ^ W J ≤ |coeff p₀ B| * R ^ W B) :
    ∀ᶠ p in 𝓝 p₀, ∀ J, t * (|coeff p J| * R ^ W J) < |coeff p B| * R ^ W B := by
  have hbase : 0 < |coeff p₀ B| * R ^ W B := mul_pos (abs_pos.mpr hB) (zpow_pos hR _)
  apply Filter.eventually_all.mpr
  intro J
  have hstrict : t * (|coeff p₀ J| * R ^ W J) < |coeff p₀ B| * R ^ W B :=
    (mul_le_mul_of_nonneg_left (hopt J) ht.le).trans_lt
      (mul_lt_of_lt_one_left hbase ht1)
  exact (continuousAt_const.mul ((hcoeff J).abs.mul continuousAt_const)).eventually_lt
    ((hcoeff B).abs.mul continuousAt_const) hstrict

/-- Continuous evaluated frame columns give continuous actual
determinants in the joint spatial and family parameters
(BB Corollary 9.54 and (9.54), pp. 451–454). -/
theorem continuous_frameDet_family {P ι : Type*} [TopologicalSpace P] {n : ℕ}
    (Z : P → ι → (Fin n → ℝ) → (Fin n → ℝ)) (x : P → (Fin n → ℝ))
    (B : Fin n → ι) (hZ : ∀ J, Continuous (fun p => Z p J (x p))) :
    Continuous (fun p => frameDet (Z p) B (x p)) := by
  have hmatrix : Continuous (fun p => frameMatrix (Z p) B (x p)) :=
    continuous_pi (fun i => continuous_pi (fun j => (continuous_apply i).comp (hZ (B j))))
  exact hmatrix.matrix_det

/-- Actual t-suboptimality of the reference frame persists in
all joint parameters at its fixed reference radius, with only continuity
in the family parameter (BB (9.54), pp. 453–454). -/
theorem eventually_suboptimal_of_fixed_radius_optimal {P ι : Type*}
    [TopologicalSpace P] [Fintype ι] {n : ℕ}
    (Z : P → ι → (Fin n → ℝ) → (Fin n → ℝ)) (x : P → (Fin n → ℝ))
    (w : ι → ℕ+) (p₀ : P) (B : Fin n → ι) {t R : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    (hZ : ∀ J, Continuous (fun p => Z p J (x p)))
    (hB : frameDet (Z p₀) B (x p₀) ≠ 0)
    (hopt : IsSuboptimal (Z p₀) w B (x p₀) 1 R) :
    ∀ᶠ p in 𝓝 p₀, IsSuboptimal (Z p) w B (x p) t R := by
  have hdet : ∀ C : Fin n → ι, ContinuousAt (fun p => frameDet (Z p) C (x p)) p₀ :=
    fun C => (continuous_frameDet_family Z x C hZ).continuousAt
  have hstrict := eventually_strict_weighted_suboptimality
    (fun p C => frameDet (Z p) C (x p)) (frameWeight w) p₀ B ht ht1 hR hdet hB
    (fun C => by simpa only [one_mul] using hopt C)
  exact hstrict.mono (fun _ hp C => (hp C).le)

end RothschildStein.G4
