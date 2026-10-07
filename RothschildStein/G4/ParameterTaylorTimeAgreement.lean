-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ParameterTransportedTaylorTime
public import RothschildStein.G4.ActualJointTransportedKernel

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RothschildStein.G4

/-- The ACTUAL transported Taylor remainder agrees with its exact
weighted next-adjoint integral on ONE parameter/initial-point neighborhood.
Compactness derives that neighborhood from the base reverse trajectory
(BB Lemma 9.48, pp. 442–443; NSW p. 127). -/
theorem parameterFlow_transported_taylor_remainder_eventuallyEq_at_time {P : Type*} {N : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [CompleteSpace P]
    {A : Set P} {Ω : Set (Fin N → ℝ)} {U : Set (P × (Fin N → ℝ))}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    (Z Y : P × (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (A ×ˢ Ω))
    {τ : ℝ} (hτ : 1 < τ) (Φ : (P × (Fin N → ℝ)) × ℝ → (Fin N → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (Z (p.1, Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    {p : P × (Fin N → ℝ)} (hp : p ∈ U)
    (hend : ∀ s ∈ Icc (0 : ℝ) 1, (p.1, Φ (p, -s)) ∈ U)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (q : ℕ) :
    (fun v => (fderiv ℝ (fun y => Φ ((v.1, y), t)) (Φ (v, -t)))
      (Y (v.1, Φ (v, -t))) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j * t ^ j / (j.factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) v)) =ᶠ[𝓝 p]
    (fun v => (q.factorial : ℝ)⁻¹ • ∫ s in (0 : ℝ)..1,
      ((1 - s) ^ q * t ^ (q + 1) * (-1 : ℝ) ^ (q + 1)) •
        (fderiv ℝ (fun y => Φ ((v.1, y), s * t)) (Φ (v, -(s * t))))
          (((spatialBracketFamily Z)^[q + 1] Y) (v.1, Φ (v, -(s * t))))) := by
  obtain ⟨hS, _⟩ := actual_parameterFlow_transported_kernel_contDiffOn
    hA hΩ hU hUA hZ (show 0 < τ by linarith) Φ hc hΦ Y (hY.mono hUA)
  let S := (U ×ˢ Ioo (-τ) τ) ∩ {v | (v.1.1, Φ (v.1, -v.2)) ∈ U}
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, (p, s) ∈ S := by
    intro s hs
    exact ⟨⟨hp, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩, hend s hs⟩
  have he : ∀ᶠ v in 𝓝 p, ∀ s ∈ Icc (0 : ℝ) 1, (v, s) ∈ S :=
    isCompact_Icc.eventually_forall_of_forall_eventually
      (fun s hs => hS.mem_nhds (hseg s hs))
  filter_upwards [he] with v hv
  have hvU : v ∈ U := (hv 0 (by norm_num)).1.1
  have hvEnd : ∀ s ∈ Icc (0 : ℝ) 1, (v.1, Φ (v, -s)) ∈ U :=
    fun s hs => (hv s hs).2
  rw [parameterFlow_transported_taylor_integral_at_time hΩ hU hUA Z Y hZ hY hτ Φ hc hΦ
    hvU hvEnd ht q, add_sub_cancel_left]

end RothschildStein.G4
