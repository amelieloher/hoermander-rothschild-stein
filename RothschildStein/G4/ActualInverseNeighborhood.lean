-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SmoothLocalChartInverse

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- An actual smooth chart with nonzero Jacobian has an open
inverse neighborhood inside the prescribed coefficient box. The inverse
is C¹ on that whole neighborhood, which is sufficient for the AC chain
rule; both inverse identities are retained (BB Prop 9.52, p. 448). -/
theorem exists_actual_inverse_neighborhood {n : ℕ}
    {Q : Set (Fin n → ℝ)} (hQ : IsOpen Q)
    (F : (Fin n → ℝ) → (Fin n → ℝ)) {u : Fin n → ℝ} (hu : u ∈ Q)
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F u)
    (hdet : Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0) :
    ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ), ∃ V : Set (Fin n → ℝ),
      IsOpen V ∧ F u ∈ V ∧ ContDiffOn ℝ 1 Ψ V ∧ Ψ (F u) = u ∧
      MapsTo Ψ V Q ∧ EqOn (F ∘ Ψ) id V ∧
      ((fun a => Ψ (F a)) =ᶠ[𝓝 u] (fun a => a)) := by
  obtain ⟨Ψ, hΨ, hpoint, hright, hleft⟩ := exists_smooth_local_chart_inverse F hF hdet
  obtain ⟨V₀, hV₀, hΨ₀⟩ := hΨ.contDiffOn (m := 1) (by simp) (by simp)
  have hpre : Ψ ⁻¹' Q ∈ 𝓝 (F u) :=
    hΨ.continuousAt.preimage_mem_nhds (by rw [hpoint]; exact hQ.mem_nhds hu)
  let V := interior ((V₀ ∩ Ψ ⁻¹' Q) ∩ {y | F (Ψ y) = y})
  have hVmem : F u ∈ V :=
    mem_interior_iff_mem_nhds.mpr (inter_mem (inter_mem hV₀ hpre) hright)
  refine ⟨Ψ, V, isOpen_interior, hVmem,
    hΨ₀.mono (fun y hy => (interior_subset hy).1.1), hpoint, ?_, ?_, hleft⟩
  · intro y hy
    exact (interior_subset hy).1.2
  · intro y hy
    exact (interior_subset hy).2

end RothschildStein.G4
