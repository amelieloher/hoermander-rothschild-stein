-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.GroupWeakConvolution
public import HeatKernel.Poincare.GroupInteriorSupport
public import HeatKernel.Poincare.GroupDerivativeApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal Topology
namespace HeatKernel

/-- Interior group regularization converges in Lp together with each weak invariant
derivative, using the compact interior support condition. -/
theorem tendsto_fieldDerivative_groupRegularize_zeroExtension
    {N : ℕ} (G : HomogeneousGroup N) {ν : G2.HomogeneousNorm G}
    (φ : G2.GroupMollifier G ν) (Ω : Opens (Fin N → ℝ))
    {D : Set (Fin N → ℝ)} (hD : IsCompact D) (hDΩ : D ⊆ Ω)
    (v : Fin N → ℝ) {f g : (Fin N → ℝ) → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ω : Set (Fin N → ℝ))))
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict (Ω : Set (Fin N → ℝ))))
    (hw : hasWeakWordDeriv (fun _ : Fin 1 => G2.leftField G v) Ω [0] f g) :
    Tendsto (fun ε : ℝ => eLpNorm
      (fun x => fieldDerivative (G2.leftField G v)
        (G2.groupRegularize G φ ((Ω : Set (Fin N → ℝ)).indicator f) ε) x - g x)
      (ENNReal.ofReal p) (volume.restrict D)) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_fieldDerivative_groupRegularize_of_local_commutation G φ Ω
    hD.measurableSet hDΩ hp hg
  obtain ⟨δ, hδ, hs⟩ := exists_groupMollifierScale_kernel_interior_support G φ
    hD Ω.isOpen hDΩ
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
  exact fieldDerivative_groupConvolution_zeroExtension_of_support G v x Ω
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    hf hw (G2.contDiff_groupMollifierScale G φ ε)
    (G2.hasCompactSupport_groupMollifierScale G φ hε.1) (hs ε hε.1 hε.2 x hx)

/-- A finite family of weak invariant derivatives admits a common smooth interior
approximation with strong Lp convergence of the function and every derivative. -/
theorem exists_smooth_weak_group_approximation
    {N q : ℕ} (G : HomogeneousGroup N) (ν : G2.HomogeneousNorm G)
    (Ω : Opens (Fin N → ℝ)) {D : Set (Fin N → ℝ)}
    (hD : IsCompact D) (hDΩ : D ⊆ Ω) (v : Fin q → (Fin N → ℝ))
    {f : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ}
    {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ω : Set (Fin N → ℝ))))
    (hg : ∀ i, MemLp (g i) (ENNReal.ofReal p) (volume.restrict (Ω : Set (Fin N → ℝ))))
    (hw : ∀ i, hasWeakWordDeriv (fun _ : Fin 1 => G2.leftField G (v i)) Ω [0] f (g i)) :
    ∃ u : ℕ → (Fin N → ℝ) → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n)) ∧
      Tendsto (fun n => eLpNorm (u n - f) (ENNReal.ofReal p) (volume.restrict D))
        atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => eLpNorm
        (fun x => fieldDerivative (G2.leftField G (v i)) (u n) x - g i x)
        (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0) := by
  obtain ⟨φ, hs, hv⟩ := exists_smooth_group_approximation G ν Ω hp hf
  refine ⟨fun n => G2.groupRegularize G φ ((Ω : Set (Fin N → ℝ)).indicator f)
    (1 / ((n : ℝ) + 1)), hs, hv D hD.measurableSet hDΩ, ?_⟩
  intro i
  exact (tendsto_fieldDerivative_groupRegularize_zeroExtension G φ Ω hD hDΩ
    (v i) hp hf (hg i) (hw i)).comp
    (tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n : ℕ => by
        change 0 < 1 / ((n : ℝ) + 1)
        positivity)⟩)

end HeatKernel
