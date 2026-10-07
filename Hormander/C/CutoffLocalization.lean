-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.FrameAlgebra
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace Hormander.C

/-- Extend a frame coefficient by multiplying it with a cutoff on
the frame neighborhood and setting it to zero off that neighborhood. -/
noncomputable def cutoffFrameCoefficient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (U : Set E) (θ : E → ℝ) (γ : E → ℝ) (x : E) : ℝ := by
  classical
  exact θ x * if x ∈ U then γ x else 0

/-- A coefficient cut off inside an open frame neighborhood is smooth
when its local formula is smooth there. -/
theorem cutoffFrameCoefficient_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [T2Space E]
    {U : Set E} (hU : IsOpen U) (θ γ : E → ℝ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hγ : ContDiffOn ℝ (⊤ : ℕ∞) γ U)
    (ht : tsupport θ ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffFrameCoefficient U θ γ) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · have hUm : U ∈ 𝓝 x := hU.mem_nhds hx
    have hlocal : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => θ y * γ y) x :=
      hθ.contDiffAt.mul (hγ.contDiffAt hUm)
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [hUm] with y hy
    simp [cutoffFrameCoefficient, hy]
  · have hθnot : x ∉ tsupport θ := fun h => hx (ht h)
    have hθzero : θ =ᶠ[𝓝 x] 0 :=
      (notMem_tsupport_iff_eventuallyEq).mp hθnot
    have hzero : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : E => (0 : ℝ)) x :=
      contDiff_const.contDiffAt
    apply hzero.congr_of_eventuallyEq
    filter_upwards [hθzero] with y hy
    simp [cutoffFrameCoefficient, hy]

/-- The localized inverse coefficient is smooth and has support
contained in the cutoff support. -/
theorem cutoffFrameCoefficient_compactSupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [T2Space E]
    (U : Set E) (θ γ : E → ℝ) (hθ : HasCompactSupport θ) :
    HasCompactSupport (cutoffFrameCoefficient U θ γ) := by
  classical
  have hsub : tsupport (cutoffFrameCoefficient U θ γ) ⊆ tsupport θ := by
    change tsupport (fun y => θ y * (if y ∈ U then γ y else 0)) ⊆ tsupport θ
    exact tsupport_mul_subset_left
  exact HasCompactSupport.of_support_subset_isCompact hθ
    (fun x hx => hsub (subset_tsupport _ hx))

/-- On an open neighborhood, localize the inverse matrix coefficients
to compact support without changing the coordinate identities near the compact set. -/
theorem exists_localized_frame_coefficients {N : ℕ}
    (V : Fin N → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hV : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (V a))
    {K U : Set (EuclideanSpace ℝ (Fin N))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hdet : ∀ x ∈ U, (frameMatrixAt V x).det ≠ 0) :
    ∃ W : Set (EuclideanSpace ℝ (Fin N)), IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      ∃ γ : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ,
        (∀ j a, ContDiff ℝ (⊤ : ℕ∞) (γ j a)) ∧
        (∀ j a, HasCompactSupport (γ j a)) ∧
        (∀ j a, tsupport (γ j a) ⊆ U) ∧
        (∀ x ∈ W, ∀ i j : Fin N,
          ∑ a : Fin N, γ j a x *
            EuclideanSpace.proj (𝕜 := ℝ) i (V a x) = if i = j then 1 else 0) := by
  classical
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let W : Set (EuclideanSpace ℝ (Fin N)) := Metric.thickening (δ / 2) K
  let T : Set (EuclideanSpace ℝ (Fin N)) := Metric.cthickening (δ / 2) K
  let S : Set (EuclideanSpace ℝ (Fin N)) := Metric.thickening δ K
  have hWopen : IsOpen W := by
    dsimp [W]
    exact Metric.isOpen_thickening
  have hKW : K ⊆ W := by
    dsimp [W]
    exact Metric.self_subset_thickening (by linarith) K
  have hWU : W ⊆ U := by
    dsimp [W]
    exact (Metric.thickening_subset_cthickening_of_le (by linarith) K).trans hδU
  have hTclosed : IsClosed T := by
    dsimp [T]
    exact Metric.isClosed_cthickening
  have hTS : T ⊆ S := by
    dsimp [T, S]
    exact Metric.cthickening_subset_thickening' (δ₁ := δ / 2) (δ₂ := δ)
      hδ (by linarith) K
  obtain ⟨θ, hθ, -, hsupport, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      (s := S) (t := T) (by simpa [S] using Metric.isOpen_thickening)
      (by simpa [T] using Metric.isClosed_cthickening) hTS
  have hθcompact : HasCompactSupport θ := by
    apply HasCompactSupport.of_support_subset_isCompact (hK.cthickening (r := δ))
    rw [hsupport]
    exact Metric.thickening_subset_cthickening δ K
  have hθU : tsupport θ ⊆ U := by
    calc
      tsupport θ = closure (support θ) := rfl
      _ = closure (Metric.thickening δ K) := by rw [hsupport]
      _ ⊆ Metric.cthickening δ K := Metric.closure_thickening_subset_cthickening δ K
      _ ⊆ U := hδU
  let γ : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ := fun j a =>
    cutoffFrameCoefficient U θ (fun x => frameInverseCoefficient V j a x)
  have hγsmooth : ∀ j a, ContDiff ℝ (⊤ : ℕ∞) (γ j a) := by
    intro j a
    exact cutoffFrameCoefficient_contDiff hU θ _ hθ
      (frame_inverse_coefficient_contDiffOn V hV hdet j a) hθU
  have hγcompact : ∀ j a, HasCompactSupport (γ j a) := by
    intro j a
    exact cutoffFrameCoefficient_compactSupport U θ _ hθcompact
  have hγsupport : ∀ j a, tsupport (γ j a) ⊆ U := by
    intro j a
    have hsubset : tsupport (γ j a) ⊆ tsupport θ := by
      change tsupport (cutoffFrameCoefficient U θ
        (fun x => frameInverseCoefficient V j a x)) ⊆ tsupport θ
      change tsupport (fun x => θ x *
        (if x ∈ U then frameInverseCoefficient V j a x else 0)) ⊆ tsupport θ
      exact tsupport_mul_subset_left
    exact hsubset.trans hθU
  have hidentity : ∀ x ∈ W, ∀ i j : Fin N,
      ∑ a : Fin N, γ j a x *
        EuclideanSpace.proj (𝕜 := ℝ) i (V a x) = if i = j then 1 else 0 := by
    intro x hx i j
    have hxT : x ∈ T := by
      dsimp [T, W] at hx ⊢
      exact (Metric.thickening_subset_cthickening (δ / 2) K) hx
    have hxU : x ∈ U := hWU hx
    have hθx : θ x = 1 := (hone x).mp hxT
    have hformula : ∀ a, γ j a x = frameInverseCoefficient V j a x := by
      intro a
      simp [γ, cutoffFrameCoefficient, hxU, hθx]
    simp_rw [hformula]
    simpa [frameInverseCoefficient, frameMatrixAt] using
      (frame_inverse_coordinate_identity (fun a => V a x) (hdet x hxU) i j)
  exact ⟨W, hWopen, hKW, hWU, γ, hγsmooth, hγcompact, hγsupport, hidentity⟩

/-- The local frame coefficients, their compactly supported localization, and the compact
determinant bound can be chosen together. -/
theorem exists_frame_coefficients_and_determinant_bound {N : ℕ}
    (V : Fin N → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hV : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (V a))
    {K U : Set (EuclideanSpace ℝ (Fin N))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hdet : ∀ x ∈ U, (frameMatrixAt V x).det ≠ 0) :
    ∃ W : Set (EuclideanSpace ℝ (Fin N)), IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      ∃ γ : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ,
        (∀ j a, ContDiff ℝ (⊤ : ℕ∞) (γ j a)) ∧
        (∀ j a, HasCompactSupport (γ j a)) ∧
        (∀ j a, tsupport (γ j a) ⊆ U) ∧
        (∃ d : ℝ, 0 < d ∧ ∀ x ∈ K, d ≤ |(frameMatrixAt V x).det|) ∧
        (∀ x ∈ W, ∀ i j : Fin N,
          ∑ a : Fin N, γ j a x *
            EuclideanSpace.proj (𝕜 := ℝ) i (V a x) = if i = j then 1 else 0) := by
  have hframeEntry (i a : Fin N) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => frameMatrixAt V x i a) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => (EuclideanSpace.proj (𝕜 := ℝ) i) (V a x))
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (hV a)
  have hdetSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => (frameMatrixAt V x).det) := by
    simp_rw [Matrix.det_apply']
    fun_prop
  have hdetContinuous : Continuous fun x => (frameMatrixAt V x).det :=
    hdetSmooth.continuous
  have hdetK : ∀ x ∈ K, (frameMatrixAt V x).det ≠ 0 :=
    fun x hx => hdet x (hKU hx)
  obtain ⟨d, hd, hbound⟩ :=
    exists_positive_abs_lower_bound_on_compact hK _ hdetContinuous hdetK
  obtain ⟨W, hWopen, hKW, hWU, γ, hγsmooth, hγcompact, hγsupport, hidentity⟩ :=
    exists_localized_frame_coefficients V hV hK hU hKU hdet
  exact ⟨W, hWopen, hKW, hWU, γ, hγsmooth, hγcompact, hγsupport,
    ⟨d, hd, hbound⟩, hidentity⟩

end Hormander.C
