-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.SmoothSumSquaresIntegral
import Mathlib.Tactic

/-! # Classical heat equations for smooth compact-data evolutions

Joint second-order kernel regularity and the kernel section heat equation
imply the classical heat equation for every compact integrable scalar datum.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set RothschildStein
namespace HeatKernel.Gaussian

/-- Time differentiation commutes with a compact-data kernel integral under
joint continuous differentiability. -/
theorem deriv_kernel_integral_of_contDiff {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {I : Set ℝ} (hI : IsOpen I) {t : ℝ} (ht : t ∈ I)
    (k : ℝ × Z → ℝ) (hk : ContDiffOn ℝ 1 k (I ×ˢ univ)) :
    deriv (fun s ↦ ∫ z, f z * k (s, z) ∂μ) t =
      ∫ z, f z * deriv (fun s ↦ k (s, z)) t ∂μ := by
  simpa only [fderiv_apply_one_eq_deriv, smul_eq_mul] using
    fderiv_kernel_integral_apply_of_contDiff μ hf hK hsupp hI ht k hk (1 : ℝ)

/-- A jointly second-order kernel satisfying the classical horizontal heat
equation passes that equation to every compact integrable scalar datum. -/
theorem deriv_integrated_heat_equation_of_contDiff {N q : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ 1 (X i))
    (p : ℝ → (Fin N → ℝ) → Z → ℝ)
    (hp : ContDiffOn ℝ 2 (fun w : ℝ × ((Fin N → ℝ) × Z) ↦ p w.1 w.2.1 w.2.2)
      (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x z, deriv (fun s ↦ p s x z) t =
      sumSquares X (fun y ↦ p t y z) x)
    {t : ℝ} (ht : 0 < t) (x : Fin N → ℝ) :
    deriv (fun s ↦ ∫ z, f z * p s x z ∂μ) t =
      sumSquares X (fun y ↦ ∫ z, f z * p t y z ∂μ) x := by
  have htime : ContDiffOn ℝ 1 (fun w : ℝ × Z ↦ p w.1 x w.2) (Ioi 0 ×ˢ univ) :=
    (hp.of_le (by norm_num)).comp
      (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)).contDiffOn
      (fun w hw ↦ ⟨hw.1, mem_univ _⟩)
  have hspace : ContDiffOn ℝ 2 (fun w : (Fin N → ℝ) × Z ↦ p t w.1 w.2) (univ ×ˢ univ) :=
    hp.comp (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)).contDiffOn
      (fun _ _ ↦ ⟨ht, mem_univ _⟩)
  rw [deriv_kernel_integral_of_contDiff μ hf hK hsupp isOpen_Ioi ht _ htime,
    sumSquares_kernel_integral_of_contDiff μ hf hK hsupp isOpen_univ (mem_univ x)
      _ hspace X (fun i ↦ (hX i).contDiffOn)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z ↦ by dsimp only; rw [hheat t ht x z])

end HeatKernel.Gaussian
