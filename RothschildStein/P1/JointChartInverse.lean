-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesChart
public import RothschildStein.L1.ParameterizedChartInverse
public import RothschildStein.L1.RightInverseLocalChart

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The actual supplied chart inverse is jointly
smooth in its center and model variable on T. This is derived from the
existing chart identities and fiber smoothness by L1's parameter inverse
theorem; no joint inverse regularity is assumed (BB pp. 549–551). -/
theorem inverse_joint_contDiffOn (C : LiftedChart w s Ω hΩ X x₀ m) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (C.e q.1).symm q.2) C.T := by
  let U := C.U ×ˢ C.U
  let V : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) := {q | (q.2, q.1) ∈ C.T}
  let Ψ := fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ q.2 q.1
  let θ := fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (C.e q.2).symm q.1
  have hU : IsOpen U := C.isOpen_U.prod C.isOpen_U
  have hV : IsOpen V := C.isOpen_T.preimage (continuous_snd.prodMk continuous_fst)
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ U :=
    C.theta_smooth.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hp => ⟨hp.2, hp.1⟩)
  have hinj : ∀ η, InjOn (fun ξ => Ψ (ξ, η)) {ξ | (ξ, η) ∈ U} := by
    intro η ξ hξ ζ hζ he
    obtain ⟨hsrc, heq, -, -, -⟩ := C.chart η hξ.2
    apply (C.e η).injOn (by rw [hsrc]; exact hξ.1) (by rw [hsrc]; exact hζ.1)
    simpa only [heq ξ hξ.1, heq ζ hζ.1] using he
  have hθ : ∀ q ∈ V, (θ q, q.2) ∈ U := by
    intro q hq
    change q.2 ∈ C.U ∧ q.1 ∈ (C.e q.2).target at hq
    obtain ⟨hsrc, -, -, -, -⟩ := C.chart q.2 hq.1
    refine ⟨?_, hq.1⟩
    rw [← hsrc]
    exact (C.e q.2).map_target hq.2
  have hΨθ : ∀ q ∈ V, Ψ (θ q, q.2) = q.1 := by
    intro q hq
    have hsource := (hθ q hq).1
    obtain ⟨-, heq, -, -, -⟩ := C.chart q.2 (hθ q hq).2
    change C.Θ q.2 ((C.e q.2).symm q.1) = q.1
    rw [← heq _ hsource]
    exact (C.e q.2).right_inv hq.2
  have hderiv : ∀ p ∈ U, ∃ H : (Fin (n + m) → ℝ) ≃L[ℝ] (Fin (n + m) → ℝ),
      (fderiv ℝ Ψ p).comp (ContinuousLinearMap.inl ℝ (Fin (n + m) → ℝ) (Fin (n + m) → ℝ)) =
        (H : (Fin (n + m) → ℝ) →L[ℝ] (Fin (n + m) → ℝ)) := by
    intro p hp
    obtain ⟨hsrc, heq, -, hsym, -⟩ := C.chart p.2 hp.2
    have hf : ContDiffAt ℝ (⊤ : ℕ∞) (C.Θ p.2) p.1 := by
      have hc := (hΨ.contDiffAt (hU.mem_nhds hp)).comp p.1
        (contDiffAt_id.prodMk (contDiffAt_const (c := p.2)))
      exact hc
    have htarget : C.Θ p.2 p.1 ∈ (C.e p.2).target := by
      rw [← heq _ hp.1]
      exact (C.e p.2).map_source (by rw [hsrc]; exact hp.1)
    have hK := (hsym.contDiffAt ((C.e p.2).open_target.mem_nhds htarget)).differentiableAt (by simp)
    have hright : ((C.e p.2).symm ∘ C.Θ p.2) =ᶠ[𝓝 p.1]
        (id : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)) := by
      filter_upwards [C.isOpen_U.mem_nhds hp.1] with ξ hξ
      change (C.e p.2).symm (C.Θ p.2 ξ) = ξ
      rw [← heq ξ hξ]
      exact (C.e p.2).left_inv (by rw [hsrc]; exact hξ)
    have hi := L1.coordinateDerivative_injective_of_right_inverse (C.Θ p.2) (C.e p.2).symm p.1
      (hf.differentiableAt (by simp)) hK hright
    let H := (LinearEquiv.ofInjectiveEndo (fderiv ℝ (C.Θ p.2) p.1).toLinearMap hi).toContinuousLinearEquiv
    refine ⟨H, ?_⟩
    have hslice := ((hΨ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp p.1
      ((hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) p.2 p.1))
    apply ContinuousLinearMap.ext
    intro v
    have he := congrArg (fun L : (Fin (n + m) → ℝ) →L[ℝ] (Fin (n + m) → ℝ) => L v) hslice.fderiv
    change (fderiv ℝ Ψ p) (v, 0) = (fderiv ℝ (C.Θ p.2) p.1) v
    simpa only [Function.comp_def, id_eq, Ψ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply] using he.symm
  have hInv := L1.contDiffOn_parameterized_chart_inverse hU hV Ψ θ hΨ hinj hθ hΨθ hderiv
  exact hInv.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hq => hq)

end RothschildStein.P1.LiftedChart
