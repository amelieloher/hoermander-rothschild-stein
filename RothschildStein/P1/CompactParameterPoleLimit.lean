-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesHomogeneous
public import RothschildStein.G2.HomogeneousDivergence
public import RothschildStein.G2.DilationMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.P1
variable {N : ℕ}

/-- On a fixed compact annulus, a parameterized
punctured kernel and a dilated test converge under the integral. The
dominator is constructed from the actual compact parameter range. -/
theorem tendsto_compactParameter_poleIntegral
    (G : HomogeneousGroup N)
    (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (D : (Fin N → ℝ) → ℝ) (hD : Continuous D) (hsD : HasCompactSupport D)
    (h0D : (0 : Fin N → ℝ) ∉ tsupport D)
    (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) × (Fin N → ℝ))
    (p₀ : (Fin N → ℝ) × (Fin N → ℝ))
    {K : Set (Fin N → ℝ)} (hK : IsCompact K)
    (hp : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ContinuousOn (p ε) (tsupport D) ∧
      ∀ u ∈ tsupport D, (p ε u).1 ∈ K ∧ (p ε u).2 ∈ K)
    (htp : ∀ u ∈ tsupport D, Tendsto (fun ε => p ε u) (𝓝[>] (0 : ℝ)) (𝓝 p₀))
    (φ : (Fin N → ℝ) → ℝ) (hφ : Continuous φ) (hsφ : HasCompactSupport φ) :
    Tendsto (fun ε : ℝ => ∫ u, Ψ (p ε u).1 (p ε u).2 u * D u * φ (G.dilate ε u))
      (𝓝[>] (0 : ℝ)) (𝓝 (φ 0 * ∫ u, Ψ p₀.1 p₀.2 u * D u)) := by
  let S := tsupport D
  have hS : IsCompact S := hsD.isCompact
  have hne {u : Fin N → ℝ} (hu : u ∈ S) : u ≠ 0 := fun hz => h0D (hz ▸ hu)
  have hc : ContinuousOn (kernelUncurry Ψ) (K ×ˢ (K ×ˢ S)) :=
    hΨ.mono (fun _ h => hne h.2.2)
  obtain ⟨A, hbA⟩ := (hK.prod (hK.prod hS)).exists_bound_of_continuousOn hc
  obtain ⟨B, hbB⟩ := hsφ.exists_bound_of_continuous hφ
  let M := max A 0
  let L := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hL : 0 ≤ L := le_max_right _ _
  have hB (u : Fin N → ℝ) : ‖φ u‖ ≤ L := (hbB u).trans (le_max_left _ _)
  have hDom : IntegrableOn (fun u => (M * L) * ‖D u‖) S volume :=
    ((hD.integrable_of_hasCompactSupport hsD).norm.const_mul (M * L)).integrableOn
  have ht : Tendsto (fun ε : ℝ => ∫ u in S,
      Ψ (p ε u).1 (p ε u).2 u * D u * φ (G.dilate ε u))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ u in S, Ψ p₀.1 p₀.2 u * D u * φ 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun u => (M * L) * ‖D u‖)
    · filter_upwards [hp] with ε hε
      have hbody := hΨ.comp
        (hε.1.fst.prodMk (hε.1.snd.prodMk continuousOn_id))
        (fun u hu => hne hu)
      exact ((hbody.mul hD.continuousOn).mul
        (hφ.comp (G2.continuous_dilate G ε)).continuousOn).aestronglyMeasurable hS.measurableSet
    · filter_upwards [hp] with ε hε
      filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
      have ha : ‖Ψ (p ε u).1 (p ε u).2 u‖ ≤ M :=
        (hbA ((p ε u).1, (p ε u).2, u) ⟨(hε.2 u hu).1, (hε.2 u hu).2, hu⟩).trans
          (le_max_left _ _)
      simp only [norm_mul]
      calc
        ‖Ψ (p ε u).1 (p ε u).2 u‖ * ‖D u‖ * ‖φ (G.dilate ε u)‖ ≤ M * ‖D u‖ * L :=
          mul_le_mul (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) (hB _)
            (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))
        _ = (M * L) * ‖D u‖ := by ring
    · exact hDom
    · filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
      have hpole : ContinuousAt (kernelUncurry Ψ) (p₀.1, p₀.2, u) :=
        hΨ.continuousAt (isOpen_kernelDomain.mem_nhds (hne hu))
      have hp₁ := (continuous_fst.tendsto p₀).comp (htp u hu)
      have hp₂ := (continuous_snd.tendsto p₀).comp (htp u hu)
      have hparams : Tendsto (fun ε : ℝ => ((p ε u).1, (p ε u).2, u))
          (𝓝[>] (0 : ℝ)) (𝓝 (p₀.1, p₀.2, u)) :=
        hp₁.prodMk_nhds (hp₂.prodMk_nhds tendsto_const_nhds)
      have huT := (G2.continuousAt_dilate_parameter_zero G u).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rw [G2.zero_dilate] at huT
      have htest : Tendsto (fun ε : ℝ => φ (G.dilate ε u)) (𝓝[>] (0 : ℝ)) (𝓝 (φ 0)) :=
        hφ.continuousAt.tendsto.comp huT
      exact ((hpole.tendsto.comp hparams).mul tendsto_const_nhds).mul htest
  have he (ε : ℝ) : (∫ u in S, Ψ (p ε u).1 (p ε u).2 u * D u * φ (G.dilate ε u)) =
      ∫ u, Ψ (p ε u).1 (p ε u).2 u * D u * φ (G.dilate ε u) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      rw [image_eq_zero_of_notMem_tsupport hu, mul_zero, zero_mul])
  have he₀ : (∫ u in S, Ψ p₀.1 p₀.2 u * D u * φ 0) =
      φ 0 * ∫ u, Ψ p₀.1 p₀.2 u * D u := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by rw [image_eq_zero_of_notMem_tsupport hu, mul_zero, zero_mul]), integral_mul_const]
    exact mul_comm _ _
  simpa only [he, he₀] using ht

end RothschildStein.P1
