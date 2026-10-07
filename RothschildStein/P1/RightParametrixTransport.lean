-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.AdjointExpansionChart

/-!
# Transport of test functions and integrals to the model variable

For `η ∈ C.U` the endpoint chart `ξ ↦ Θ η ξ` is a diffeomorphism of `C.U` onto the open set
`(C.e η).target`, with Jacobian `dξ = c(η) (1 + ω₊(η, u)) du` for `u = Θ η ξ`
(`LiftedChart.jacobian`). The transported density of a function `ψ` of `ξ` is

`ψ̃(u) = ψ((e η)⁻¹ u) · c(η) (1 + ω₊(η, u))`  on `(e η).target`, `0` elsewhere

(`LiftedChart.modelTransport`; the right pole computation, "substitute `u = Θ(η, ξ)`"). Then
`∫_U F(Θ η ξ) ψ(ξ) dξ = ∫ F(u) ψ̃(u) du` for every `F`
(`LiftedChart.integral_comp_theta_mul`), `ψ̃(0) = c(η) ψ(η)`, and `ψ̃` is a test function on
`(e η).target` when `ψ` is a test function on `C.U` (`LiftedChart.modelTransportTest`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The chart domain `C.U` as an open set. -/
def chartOpens : Opens (Fin (n + m) → ℝ) := ⟨C.U, C.isOpen_U⟩

/-- The target of the endpoint chart `e η` (the image of `C.U` under
`Θ η`) as an open set. -/
def modelOpens (η : Fin (n + m) → ℝ) : Opens (Fin (n + m) → ℝ) :=
  ⟨(C.e η).target, (C.e η).open_target⟩

/-- The transported density `ψ̃(u) = ψ((e η)⁻¹ u) · c(η) (1 + ω₊(η, u))` on
`(e η).target`, extended by zero (the right pole computation). -/
def modelTransport (η : Fin (n + m) → ℝ) (ψ : (Fin (n + m) → ℝ) → ℝ) :
    (Fin (n + m) → ℝ) → ℝ :=
  (C.e η).target.indicator fun u => ψ ((C.e η).symm u) * (C.c η * (1 + C.ωp η u))

variable {C}

theorem e_source {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) : (C.e η).source = C.U :=
  (C.chart η hη).1

theorem e_apply {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) :
    C.e η ξ = C.Θ η ξ :=
  (C.chart η hη).2.1 ξ hξ

theorem symm_theta {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) :
    (C.e η).symm (C.Θ η ξ) = ξ := by
  rw [← e_apply hη hξ]
  exact (C.e η).left_inv (by rw [e_source hη]; exact hξ)

theorem theta_self {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) : C.Θ η η = 0 :=
  (C.chart η hη).2.2.2.2

theorem symm_zero {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) : (C.e η).symm 0 = η := by
  have h := symm_theta hη hη
  rwa [theta_self hη] at h

theorem zero_mem_target {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) : (0 : Fin (n + m) → ℝ) ∈ (C.e η).target := by
  have h := C.theta_mem_target hη hη
  rwa [theta_self hη] at h

theorem theta_image_U {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) : C.Θ η '' C.U = (C.e η).target := by
  have h := (C.e η).image_source_eq_target
  rw [e_source hη] at h
  rw [← h]
  exact image_congr (fun ξ hξ => (e_apply hη hξ).symm)

theorem injOn_theta {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) : InjOn (C.Θ η) C.U := by
  intro x hx y hy hxy
  have h := (C.e η).injOn (by rw [e_source hη]; exact hx) (by rw [e_source hη]; exact hy)
    (by rw [e_apply hη hx, e_apply hη hy]; exact hxy)
  exact h

theorem contDiffOn_symm {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.e η).symm (C.e η).target :=
  (C.chart η hη).2.2.2.1

theorem contDiffOn_omegaPlus {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.ωp η) (C.e η).target := by
  have hmap : MapsTo (fun u : Fin (n + m) → ℝ => (η, u)) (C.e η).target C.T :=
    fun u hu => ⟨hη, hu⟩
  exact C.ωp_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn hmap

theorem modelTransport_of_mem {η u : Fin (n + m) → ℝ} (hu : u ∈ (C.e η).target)
    (ψ : (Fin (n + m) → ℝ) → ℝ) :
    C.modelTransport η ψ u = ψ ((C.e η).symm u) * (C.c η * (1 + C.ωp η u)) :=
  indicator_of_mem hu _

theorem modelTransport_of_notMem {η u : Fin (n + m) → ℝ} (hu : u ∉ (C.e η).target)
    (ψ : (Fin (n + m) → ℝ) → ℝ) : C.modelTransport η ψ u = 0 :=
  indicator_of_notMem hu _

theorem modelTransport_theta {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U)
    (ψ : (Fin (n + m) → ℝ) → ℝ) :
    C.modelTransport η ψ (C.Θ η ξ) = ψ ξ * (C.c η * (1 + C.ωp η (C.Θ η ξ))) := by
  rw [modelTransport_of_mem (C.theta_mem_target hη hξ), symm_theta hη hξ]

/-- The diagonal value of the transported density is `c(η) ψ(η)`
(`ω₊(η, 0) = 0`, `Θ η η = 0`). -/
theorem modelTransport_zero {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (ψ : (Fin (n + m) → ℝ) → ℝ) :
    C.modelTransport η ψ 0 = C.c η * ψ η := by
  rw [modelTransport_of_mem (zero_mem_target hη), symm_zero hη, (C.ω_origin η hη).1]
  ring

/-- Change of variables `u = Θ η ξ` (the right pole computation: "test in `ξ`,
substitute `u = Θ(η, ξ)`"): `∫_U F(Θ η ξ) ψ(ξ) dξ = ∫ F(u) ψ̃(u) du`, the density being
`dξ = c(η) (1 + ω₊(η, u)) du` (`LiftedChart.jacobian`). -/
theorem integral_comp_theta_mul {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (F ψ : (Fin (n + m) → ℝ) → ℝ) :
    ∫ ξ in C.U, F (C.Θ η ξ) * ψ ξ = ∫ u, F u * C.modelTransport η ψ u := by
  have hmeas : MeasurableSet C.U := C.isOpen_U.measurableSet
  have hderiv : ∀ x ∈ C.U, HasFDerivWithinAt (C.Θ η) (fderiv ℝ (C.Θ η) x) C.U x :=
    fun x hx => (C.differentiableAt_theta hη hx).hasFDerivAt.hasFDerivWithinAt
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hmeas hderiv (injOn_theta hη)
    (fun u => F u * C.modelTransport η ψ u)
  rw [theta_image_U hη] at h
  have h2 : ∫ u in (C.e η).target, F u * C.modelTransport η ψ u =
      ∫ u, F u * C.modelTransport η ψ u :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by simp [modelTransport_of_notMem hu])
  rw [← h2, h]
  refine setIntegral_congr_fun hmeas (fun ξ hξ => ?_)
  obtain ⟨hp1, -, hjac, -⟩ := C.jacobian η hη ξ hξ
  have hdet : |(fderiv ℝ (C.Θ η) ξ).det| = (C.c η * (1 + C.ωp η (C.Θ η ξ)))⁻¹ := by
    rw [← hjac]
    unfold absoluteJacobian
    rw [LinearMap.det_toMatrix]
  have hc : C.c η ≠ 0 := (C.density_pos η hη).ne'
  have hp : 1 + C.ωp η (C.Θ η ξ) ≠ 0 := hp1.ne'
  simp only [smul_eq_mul]
  rw [hdet, modelTransport_theta hη hξ]
  field_simp

/-- Integrability transfers along the change of variables `u = Θ η ξ`. -/
theorem integrableOn_comp_theta_mul_iff {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (F ψ : (Fin (n + m) → ℝ) → ℝ) :
    IntegrableOn (fun ξ => F (C.Θ η ξ) * ψ ξ) C.U ↔
      Integrable (fun u => F u * C.modelTransport η ψ u) := by
  have hmeas : MeasurableSet C.U := C.isOpen_U.measurableSet
  have hderiv : ∀ x ∈ C.U, HasFDerivWithinAt (C.Θ η) (fderiv ℝ (C.Θ η) x) C.U x :=
    fun x hx => (C.differentiableAt_theta hη hx).hasFDerivAt.hasFDerivWithinAt
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hmeas hderiv
    (injOn_theta hη) (fun u => F u * C.modelTransport η ψ u)
  rw [theta_image_U hη] at h
  have h2 : IntegrableOn (fun u => F u * C.modelTransport η ψ u) (C.e η).target ↔
      Integrable (fun u => F u * C.modelTransport η ψ u) :=
    integrableOn_iff_integrable_of_support_subset (fun u hu => by
      by_contra hn
      exact hu (by simp [modelTransport_of_notMem hn]))
  rw [← h2, h]
  refine integrableOn_congr_fun (fun ξ hξ => ?_) hmeas |>.symm
  obtain ⟨hp1, -, hjac, -⟩ := C.jacobian η hη ξ hξ
  have hdet : |(fderiv ℝ (C.Θ η) ξ).det| = (C.c η * (1 + C.ωp η (C.Θ η ξ)))⁻¹ := by
    rw [← hjac]
    unfold absoluteJacobian
    rw [LinearMap.det_toMatrix]
  have hc : C.c η ≠ 0 := (C.density_pos η hη).ne'
  have hp : 1 + C.ωp η (C.Θ η ξ) ≠ 0 := hp1.ne'
  simp only [smul_eq_mul]
  rw [hdet, modelTransport_theta hη hξ]
  field_simp

section TestFunctions

/-- The transported density vanishes off the image `e η '' tsupport ψ` of the
support. -/
theorem modelTransport_eq_zero_of_notMem {η u : Fin (n + m) → ℝ}
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) (hu : u ∉ (C.e η) '' tsupport (ψ : (Fin (n + m) → ℝ) → ℝ)) :
    C.modelTransport η ψ u = 0 := by
  by_cases hut : u ∈ (C.e η).target
  · rw [modelTransport_of_mem hut]
    have hnot : (C.e η).symm u ∉ tsupport (ψ : (Fin (n + m) → ℝ) → ℝ) := fun hs =>
      hu ⟨_, hs, (C.e η).right_inv hut⟩
    rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]
  · exact modelTransport_of_notMem hut ψ

theorem isCompact_image_tsupport {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    IsCompact ((C.e η) '' tsupport (ψ : (Fin (n + m) → ℝ) → ℝ)) :=
  ψ.hasCompactSupport.image_of_continuousOn
    ((C.e η).continuousOn.mono (by rw [e_source hη]; exact ψ.tsupport_subset))

theorem image_tsupport_subset_target {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    (C.e η) '' tsupport (ψ : (Fin (n + m) → ℝ) → ℝ) ⊆ (C.e η).target := by
  rintro _ ⟨ξ, hξ, rfl⟩
  exact (C.e η).map_source (by rw [e_source hη]; exact ψ.tsupport_subset hξ)

theorem contDiff_modelTransport {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    ContDiff ℝ (⊤ : ℕ∞) (C.modelTransport η ψ) := by
  have hK := isCompact_image_tsupport hη ψ
  refine contDiff_iff_contDiffAt.2 (fun u => ?_)
  by_cases hut : u ∈ (C.e η).target
  · have hev : C.modelTransport η ψ =ᶠ[𝓝 u]
        fun u => ψ ((C.e η).symm u) * (C.c η * (1 + C.ωp η u)) :=
      Filter.eventuallyEq_of_mem ((C.e η).open_target.mem_nhds hut)
        (fun v hv => modelTransport_of_mem hv ψ)
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (C.e η).symm u :=
      (contDiffOn_symm hη).contDiffAt ((C.e η).open_target.mem_nhds hut)
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (C.ωp η) u :=
      (contDiffOn_omegaPlus hη).contDiffAt ((C.e η).open_target.mem_nhds hut)
    exact (ψ.contDiff.contDiffAt.comp u h1).mul
      (contDiffAt_const.mul (contDiffAt_const.add h2))
  · have hu' : u ∉ (C.e η) '' tsupport (ψ : (Fin (n + m) → ℝ) → ℝ) :=
      fun h => hut (image_tsupport_subset_target hη ψ h)
    have hev : ∀ᶠ v in 𝓝 u, C.modelTransport η ψ v = 0 := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hu'] with v hv
      exact modelTransport_eq_zero_of_notMem ψ hv
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem hasCompactSupport_modelTransport {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) : HasCompactSupport (C.modelTransport η ψ) :=
  HasCompactSupport.intro (isCompact_image_tsupport hη ψ)
    (fun _ hu => modelTransport_eq_zero_of_notMem ψ hu)

theorem tsupport_modelTransport_subset {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    tsupport (C.modelTransport η ψ) ⊆ (C.e η).target := by
  have hK := isCompact_image_tsupport hη ψ
  refine (closure_minimal (fun u hu => ?_) hK.isClosed).trans (image_tsupport_subset_target hη ψ)
  by_contra hn
  exact hu (modelTransport_eq_zero_of_notMem ψ hn)

/-- The transported density of a test function on `C.U` is a test function on
the target of `e η` (the right pole computation: "the transformed test is compactly supported"). -/
def modelTransportTest {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) :=
  ⟨C.modelTransport η ψ, contDiff_modelTransport hη ψ, hasCompactSupport_modelTransport hη ψ,
    tsupport_modelTransport_subset hη ψ⟩

end TestFunctions

/-- If `F · ψ̃` is integrable on the target of `e η`, then
`ξ ↦ F(Θ η ξ) ψ(ξ)` is integrable on `C.U` and the two integrals agree. -/
theorem integrableOn_integral_comp_theta_mul {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {F ψ : (Fin (n + m) → ℝ) → ℝ}
    (hF : IntegrableOn (fun u => F u * C.modelTransport η ψ u) (C.e η).target) :
    IntegrableOn (fun ξ => F (C.Θ η ξ) * ψ ξ) C.U ∧
      ∫ ξ in C.U, F (C.Θ η ξ) * ψ ξ = ∫ u in (C.e η).target, F u * C.modelTransport η ψ u := by
  have hfull : Integrable (fun u => F u * C.modelTransport η ψ u) :=
    (integrableOn_iff_integrable_of_support_subset (fun u hu => by
      by_contra hn
      exact hu (by simp [modelTransport_of_notMem hn]))).1 hF
  refine ⟨(integrableOn_comp_theta_mul_iff hη F ψ).2 hfull, ?_⟩
  rw [integral_comp_theta_mul hη F ψ]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun u hu => by simp [modelTransport_of_notMem hu])).symm

/-- The change of variables for a locally integrable `F` on the target and a
test function `ψ` on `C.U`. -/
theorem integrableOn_integral_comp_theta_mul_test {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {F : (Fin (n + m) → ℝ) → ℝ} (hF : LocallyIntegrableOn F (C.e η).target)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun ξ => F (C.Θ η ξ) * ψ ξ) C.U ∧
      ∫ ξ in C.U, F (C.Θ η ξ) * ψ ξ = ∫ u in (C.e η).target, F u * C.modelTransport η ψ u :=
  integrableOn_integral_comp_theta_mul hη
    (S.integrable_mul_test (C.modelOpens η) hF (modelTransportTest hη ψ)).integrableOn

end LiftedChart

end RothschildStein.P1
