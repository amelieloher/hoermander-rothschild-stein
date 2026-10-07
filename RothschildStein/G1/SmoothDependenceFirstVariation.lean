-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceAssembly

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Identify an independently given fundamental solution as
the initial-data derivative, uniformly over a closed forward time interval.
The field is only `C¹` on its original open domain. No initial-data derivative
is assumed in any hypothesis (BB Proposition 1.2, p. 3). -/
theorem flow_hasFDerivAt_initial_of_fundamental_solution
    {Ω : Set E} (hΩ : IsOpen Ω) {Z : E → E} (hZ : ContDiffOn ℝ 1 Z Ω)
    {Φ : E → ℝ → E} {x : E} {a b B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ᶠ y in 𝓝 x, ContinuousOn (Φ y) (Icc a b))
    (hsol : ∀ᶠ y in 𝓝 x, ∀ t ∈ Ico a b, HasDerivAt (Φ y) (Z (Φ y t)) t)
    (hinit : ∀ᶠ y in 𝓝 x, Φ y a = y)
    (hmem : ∀ t ∈ Icc a b, Φ x t ∈ Ω)
    (hLip : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b, ‖Φ y t - Φ x t‖ ≤ B * ‖y - x‖)
    {J : ℝ → E →L[ℝ] E}
    (hJ : ContinuousOn J (Icc a b))
    (hJ' : ∀ t ∈ Ico a b,
      HasDerivAt J ((fderiv ℝ Z (Φ x t)).comp (J t)) t)
    (hJinit : J a = ContinuousLinearMap.id ℝ E) :
    ∀ t ∈ Icc a b, HasFDerivAt (fun y => Φ y t) (J t) x := by
  have hcA : ContinuousOn (fun t => fderiv ℝ Z (Φ x t)) (Icc a b) :=
    (hZ.continuousOn_fderiv_of_isOpen hΩ le_rfl).comp hc.self_of_nhds hmem
  obtain ⟨K, hK⟩ := (isCompact_Icc.image_of_continuousOn hcA).isBounded.exists_norm_le
  have hKA : ∀ t ∈ Ico a b, ‖fderiv ℝ Z (Φ x t)‖ ≤ K := by
    intro t ht
    exact hK _ (mem_image_of_mem _ (Ico_subset_Icc_self ht))
  have hr := flow_uniform_linearized_residual hΩ hZ hB hc.self_of_nhds hmem hLip
  intro t ht
  apply hasFDerivAt_flow_of_linearized_residual ht hc hsol hinit hJ hJ' hJinit hKA
  intro ε hε
  exact (hr ε hε).mono (fun y hy v hv => hy v (Ico_subset_Icc_self hv))

end RothschildStein.G1
