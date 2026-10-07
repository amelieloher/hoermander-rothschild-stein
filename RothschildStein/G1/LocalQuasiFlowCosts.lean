-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalQuasiFlowRegularity
public import RothschildStein.G1.QuasiExponentialCost

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Classical
open scoped Topology ENNReal
namespace RothschildStein.G1
open G3

/-- Both genuine primitive point schedules have the same scalar
cost throughout the package's original base-point domain. -/
theorem LocalQuasiFlowData.quasi_cost {a s n : ℕ} {p : Fin a → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    {D : FreeModelData a s p} {z : Fin n → ℝ} (P : LocalQuasiFlowData Ω X D z)
    (I : List (Fin a)) (hne : I ≠ []) (hI : wordWeight p I ≤ s)
    {x : Fin n → ℝ} (hx : x ∈ P.U) {t : ℝ} (ht : 0 < t) (htη : t < P.η) :
    controlDistance Ω p X x (quasiExponentialPointMap p (primitiveFlowFromLieFamily D P.Φ P.κ) I t x) ≤
      ENNReal.ofReal ((3 * 2 ^ (s - 1) : ℕ) * t) ∧
    controlDistance Ω p X x (inverseQuasiExponentialPointMap p (primitiveFlowFromLieFamily D P.Φ P.κ) I t x) ≤
      ENNReal.ofReal ((3 * 2 ^ (s - 1) : ℕ) * t) := by
  have htime : t ∈ Ioo (-P.η) P.η := ⟨by linarith [P.η_pos], htη⟩
  have had := P.admissible I hne hI x hx t htime
  have hdom := P.U_subset_V.trans P.V_subset_Ω hx
  constructor
  · simpa only [abs_of_pos ht] using
      controlDistance_quasiExponentialPoint p X (fun _ => P.V) (fun _ => P.V_subset_Ω)
        (fun _ => P.κ) (primitiveFlowFromLieFamily D P.Φ P.κ) P.smooth_primitive
        P.ode_primitive s I hne hI t ht.ne' x hdom had.1
  · simpa only [abs_of_pos ht] using
      controlDistance_inverseQuasiExponentialPoint p X (fun _ => P.V) (fun _ => P.V_subset_Ω)
        (fun _ => P.κ) (primitiveFlowFromLieFamily D P.Φ P.κ) P.smooth_primitive
        P.ode_primitive s I hne hI t ht.ne' x hdom had.2

/-- Signed root substitution gives the uniform step-gain cost
near the center, including zero time. Actual intermediate domains come
from the flow package's admissibility conclusions (BB p. 35). -/
theorem LocalQuasiFlowData.signedMap_eventually_cost {a s n : ℕ} {p : Fin a → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    {D : FreeModelData a s p} {z : Fin n → ℝ} (P : LocalQuasiFlowData Ω X D z)
    (hs : 1 ≤ s) (I : List (Fin a)) (hne : I ≠ []) (hI : wordWeight p I ≤ s) :
    ∀ᶠ q : ℝ × (Fin n → ℝ) in 𝓝 (0, z),
      controlDistance Ω p X q.2 (P.signedMap I q) ≤
        ENNReal.ofReal ((3 * 2 ^ (s - 1) : ℕ) * |q.1| ^ (1 / (s : ℝ))) := by
  have hk : 0 < wordWeight p I :=
    (List.length_pos_iff.mpr hne).trans_le (length_le_weight p I)
  let root := fun h : ℝ => |h| ^ (1 / (wordWeight p I : ℝ))
  have hroot : Continuous root := continuous_abs.rpow_const (fun _ => Or.inr (by positivity))
  have hroot₀ : root 0 = 0 := by
    dsimp [root]
    rw [abs_zero, Real.zero_rpow (by positivity : (1 / (wordWeight p I : ℝ)) ≠ 0)]
  have hbase := (continuous_snd.continuousAt (x := ((0 : ℝ), z))).preimage_mem_nhds
    (P.open_U.mem_nhds P.center)
  have hrη : {q : ℝ × (Fin n → ℝ) | root q.1 < P.η} ∈ 𝓝 (0, z) :=
    (hroot.comp continuous_fst).continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (by simpa only [Function.comp_apply, hroot₀] using P.η_pos))
  have hr1 : {q : ℝ × (Fin n → ℝ) | |q.1| < 1} ∈ 𝓝 (0, z) :=
    continuous_fst.abs.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [hbase, hrη, hr1] with q hq hηq h1q
  change q.2 ∈ P.U at hq
  change root q.1 < P.η at hηq
  change |q.1| < 1 at h1q
  by_cases hzero : q.1 = 0
  · have he : q = (0, q.2) := Prod.ext hzero rfl
    rw [he, P.signedMap_zero I, controlDistance_self (Ω := Ω) p X
      (P.V_subset_Ω (P.U_subset_V hq))]
    exact bot_le
  · have hrt : 0 < root q.1 := Real.rpow_pos_of_pos (abs_pos.mpr hzero) _
    have hcost := P.quasi_cost I hne hI hq hrt hηq
    have hmap : P.signedMap I q =
        if 0 ≤ q.1 then quasiExponentialPointMap p (primitiveFlowFromLieFamily D P.Φ P.κ) I (root q.1) q.2
        else inverseQuasiExponentialPointMap p (primitiveFlowFromLieFamily D P.Φ P.κ) I (root q.1) q.2 := by
      simp only [signedMap, ite_eq_left hq, signedRootEndpoint]
      split_ifs <;> abel
    have he : root q.1 ≤ |q.1| ^ (1 / (s : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) h1q.le (by positivity)
        (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < wordWeight p I) (by exact_mod_cast hI))
    rw [hmap]
    split_ifs
    · exact hcost.1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left he (by positivity)))
    · exact hcost.2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left he (by positivity)))

end RothschildStein.G1
