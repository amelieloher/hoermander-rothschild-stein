-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalQuasiFlowData
public import RothschildStein.G1.ActualSignedQuasiRegularity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Classical Metric
open scoped Topology
namespace RothschildStein.G1
open G3

/-- A local flow package's actual zero-time schedule fixes its
base point, with no global flow-domain assumption. -/
theorem LocalQuasiFlowData.quasi_zero {a s n : ℕ} {p : Fin a → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    {D : FreeModelData a s p} {z : Fin n → ℝ} (P : LocalQuasiFlowData Ω X D z)
    (I : List (Fin a)) {x : Fin n → ℝ} (hx : x ∈ P.U) :
    quasiExponentialPointMap p (primitiveFlowFromLieFamily D P.Φ P.κ) I 0 x = x := by
  have he : ∀ S : List (Fin a × Bool),
      runSchedule (fun b y => weightedPrimitiveArc p (primitiveFlowFromLieFamily D P.Φ P.κ) b (0, y)) S x = x := by
    intro S
    induction S with
    | nil => rfl
    | cons b S ih =>
      have ha : weightedPrimitiveArc p (primitiveFlowFromLieFamily D P.Φ P.κ) b (0, x) = x := by
        simpa only [weightedPrimitiveArc, flowArc, zero_pow (p b.1).pos.ne', neg_zero, ite_self] using
          (P.ode_primitive b.1 x (P.U_subset_V hx)).1
      simpa only [runSchedule, ha] using ih
  exact he (commutatorSchedule I)

/-- A harmless identity extension outside the initial-point
patch. On the actual patch this is the genuine signed quasiexponential. -/
def LocalQuasiFlowData.signedMap {a s n : ℕ} {p : Fin a → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    {D : FreeModelData a s p} {z : Fin n → ℝ} (P : LocalQuasiFlowData Ω X D z)
    (I : List (Fin a)) (q : ℝ × (Fin n → ℝ)) : Fin n → ℝ :=
  if q.2 ∈ P.U then
    signedRootEndpoint (wordWeight p I)
      (fun q : (Fin n → ℝ) × ℝ => quasiExponentialPointMap p (primitiveFlowFromLieFamily D P.Φ P.κ) I q.2 q.1 - q.1)
      (fun q : (Fin n → ℝ) × ℝ => inverseQuasiExponentialPointMap p (primitiveFlowFromLieFamily D P.Φ P.κ) I q.2 q.1 - q.1) q
  else q.2

/-- The extended actual signed map fixes every zero parameter. -/
theorem LocalQuasiFlowData.signedMap_zero {a s n : ℕ} {p : Fin a → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    {D : FreeModelData a s p} {z : Fin n → ℝ} (P : LocalQuasiFlowData Ω X D z)
    (I : List (Fin a)) (x : Fin n → ℝ) : P.signedMap I (0, x) = x := by
  classical
  by_cases hx : x ∈ P.U
  · by_cases hI : I = []
    · simp only [signedMap, hx, ite_true, signedRootEndpoint, le_refl, hI,
        quasiExponentialPointMap, commutatorSchedule, runSchedule, sub_self, add_zero]
    · have hw : 0 < wordWeight p I :=
        (List.length_pos_iff.mpr hI).trans_le (length_le_weight p I)
      have ht : |(0 : ℝ)| ^ (1 / (wordWeight p I : ℝ)) = 0 := by
        rw [abs_zero, Real.zero_rpow (by positivity : (1 / (wordWeight p I : ℝ)) ≠ 0)]
      simp only [signedMap, hx, ite_true, signedRootEndpoint, le_refl, ht,
        P.quasi_zero I hx, sub_self, add_zero]
  · simp only [signedMap, hx, ite_false]

/-- The package supplies actual C¹ signed maps and their
nested-bracket derivative at every base point of the original patch. -/
theorem LocalQuasiFlowData.signedMap_regular {a s n : ℕ} {p : Fin a → ℕ+}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {D : FreeModelData a s p} {z : Fin n → ℝ} (P : LocalQuasiFlowData Ω X D z)
    (hs : 1 ≤ s) (I : List (Fin a)) (hne : I ≠ []) (hI : wordWeight p I ≤ s)
    {x : Fin n → ℝ} (hx : x ∈ P.U) :
    ContDiffAt ℝ 1 (P.signedMap I) (0, x) ∧
      HasFDerivAt (P.signedMap I)
        ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) +
          (ContinuousLinearMap.toSpanSingleton ℝ (wordBracket X I x)).comp
            (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))) (0, x) := by
  let Gp := fun q : (Fin n → ℝ) × ℝ =>
    quasiExponentialPointMap p (primitiveFlowFromLieFamily D P.Φ P.κ) I q.2 q.1 - q.1
  let Gm := fun q : (Fin n → ℝ) × ℝ =>
    inverseQuasiExponentialPointMap p (primitiveFlowFromLieFamily D P.Φ P.κ) I q.2 q.1 - q.1
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) P.Φ
      ((ball 0 P.σ ×ˢ P.U) ×ˢ Ioo (-2 : ℝ) 2) :=
    P.smooth_Φ.mono (prod_mono (prod_mono Subset.rfl P.U_subset_V) Subset.rfl)
  have hh := actual_signed_quasi_regular_of_point_error D hs I hne hI hΩ P.open_U
    (P.U_subset_V.trans P.V_subset_Ω) X hX isOpen_ball (mem_ball_self P.σ_pos)
    P.Φ hΦ (fun f hf y hy => P.ode_Φ f hf y (P.U_subset_V hy))
    (primitiveFlowFromLieFamily D P.Φ P.κ) P.η_pos
    (P.smooth_points I hne hI).1 (P.smooth_points I hne hI).2
    (fun y hy t ht => (P.point_error I hne hI y hy t ht).1)
    (fun y hy t ht => (P.point_error I hne hI y hy t ht).2) hx
  have he : P.signedMap I =ᶠ[𝓝 (0, x)] signedRootEndpoint (wordWeight p I) Gp Gm := by
    have hm := (continuous_snd.continuousAt (x := ((0 : ℝ), x))).preimage_mem_nhds (P.open_U.mem_nhds hx)
    filter_upwards [hm] with q hq
    exact ite_eq_left hq
  exact ⟨hh.1.congr_of_eventuallyEq he, hh.2.congr_of_eventuallyEq he⟩

end RothschildStein.G1
