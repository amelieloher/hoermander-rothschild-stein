-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.JointChartInverse
public import RothschildStein.P1.ReflectedChartTransport
public import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Transported compact tests are jointly smooth
in the chart center and all model variables. Off the chart image, uniform
compact support gives a zero germ; no global inverse regularity is assumed. -/
theorem modelTransport_joint_contDiffOn
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.modelTransport p.1 ψ p.2)
      (C.U ×ˢ (univ : Set (Fin (n + m) → ℝ))) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  by_cases hu : p.2 ∈ (C.e p.1).target
  · have hT : p ∈ C.T := ⟨hp.1, hu⟩
    have hev : (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        C.modelTransport q.1 ψ q.2) =ᶠ[𝓝 p]
        fun q => ψ ((C.e q.1).symm q.2) * (C.c q.1 * (1 + C.ωp q.1 q.2)) := by
      filter_upwards [C.isOpen_T.mem_nhds hT] with q hq
      exact modelTransport_of_mem hq.2 ψ
    have hi := C.inverse_joint_contDiffOn.contDiffAt (C.isOpen_T.mem_nhds hT)
    have hd : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.c q.1) p :=
      (C.density_smooth.contDiffAt (C.isOpen_U.mem_nhds hp.1)).comp p contDiffAt_fst
    have hω := C.ωp_smooth.contDiffAt (C.isOpen_T.mem_nhds hT)
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact (ψ.contDiff.contDiffAt.comp p hi).mul (hd.mul (contDiffAt_const.add hω))
  · obtain ⟨L, hLn, hLU, hLc⟩ := local_compact_nhds (C.isOpen_U.mem_nhds hp.1)
    let H := fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (q.1, C.Θ q.1 q.2)
    let M := H '' (L ×ˢ tsupport (ψ : (Fin (n + m) → ℝ) → ℝ))
    have hH : ContinuousOn H (C.U ×ˢ C.U) :=
      (contDiffOn_fst.prodMk C.theta_smooth).continuousOn
    have hM : IsCompact M := (hLc.prod ψ.hasCompactSupport.isCompact).image_of_continuousOn
      (hH.mono (fun q hq => ⟨hLU hq.1, ψ.tsupport_subset hq.2⟩))
    have hpM : p ∉ M := by
      rintro ⟨q, hq, rfl⟩
      exact hu (C.theta_mem_target (hLU hq.1) (ψ.tsupport_subset hq.2))
    have hLnear : ∀ᶠ q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) in 𝓝 p, q.1 ∈ L :=
      continuous_fst.continuousAt.eventually hLn
    have hev : (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        C.modelTransport q.1 ψ q.2) =ᶠ[𝓝 p] fun _ => 0 := by
      filter_upwards [hLnear, hM.isClosed.isOpen_compl.mem_nhds hpM] with q hqL hqM
      apply modelTransport_eq_zero_of_notMem ψ
      rintro ⟨v, hv, he⟩
      apply hqM
      refine ⟨(q.1, v), ⟨hqL, hv⟩, ?_⟩
      change (q.1, C.Θ q.1 v) = q
      refine Prod.ext rfl ?_
      rw [← e_apply (hLU hqL) (ψ.tsupport_subset hv)]
      exact he
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- Joint smoothness also holds for the actual
reflected input density used by ambient principal-value truncations. -/
theorem reflectedTransport_joint_contDiffOn
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.reflectedTransport p.1 ψ p.2)
      (C.U ×ˢ (univ : Set (Fin (n + m) → ℝ))) := by
  exact (modelTransport_joint_contDiffOn ψ).comp
    (contDiffOn_fst.prodMk contDiffOn_snd.neg) (fun q hq => ⟨hq.1, mem_univ _⟩)

/-- A compact set of centers gives a single compact support for every
transported test in model coordinates. -/
theorem exists_uniform_modelTransport_support
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ M : Set (Fin (n + m) → ℝ), IsCompact M ∧
      ∀ ξ ∈ K, tsupport (C.modelTransport ξ ψ) ⊆ M := by
  let M := (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ q.1 q.2) ''
    (K ×ˢ tsupport (ψ : (Fin (n + m) → ℝ) → ℝ))
  have hM : IsCompact M := (hK.prod ψ.hasCompactSupport.isCompact).image_of_continuousOn
    (C.theta_smooth.continuousOn.mono
      (fun q hq => ⟨hKU hq.1, ψ.tsupport_subset hq.2⟩))
  refine ⟨M, hM, ?_⟩
  intro ξ hξ
  apply closure_minimal ?_ hM.isClosed
  intro u hu
  by_contra hn
  apply hu
  apply modelTransport_eq_zero_of_notMem ψ
  rintro ⟨v, hv, he⟩
  apply hn
  refine ⟨(ξ, v), ⟨hξ, hv⟩, ?_⟩
  change C.Θ ξ v = u
  rw [← e_apply (hKU hξ) (ψ.tsupport_subset hv)]
  exact he

end RothschildStein.P1.LiftedChart
