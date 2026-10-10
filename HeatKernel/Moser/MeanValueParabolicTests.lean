-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueParabolicCoordinates
import Mathlib.Tactic

/-! # Smooth compact tests in parabolic group coordinates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein RothschildStein.G2
namespace HeatKernel

/-- The inverse parabolic coordinate map is smooth. -/
theorem contDiff_parabolicGroupHomeomorph_symm {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (parabolicGroupHomeomorph G t₀ x₀ r hr).symm := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (Fin N → ℝ) =>
    ((r ^ 2)⁻¹ * (-t₀ + z.1), G.dilate r⁻¹ (G.mul (G.inv x₀) z.2)))
  exact (contDiff_const.mul (contDiff_const.add contDiff_fst)).prodMk
    ((contDiff_dilate G r⁻¹).comp
      ((contDiff_leftTranslation G (G.inv x₀)).comp contDiff_snd))

/-- A test in the rescaled coordinates is transported to the original coordinates
by composition with the inverse parabolic map. -/
def parabolicTestTransport {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    (φ : ℝ × (Fin N → ℝ) → ℝ) : ℝ × (Fin N → ℝ) → ℝ :=
  φ ∘ (parabolicGroupHomeomorph G t₀ x₀ r hr).symm

/-- Transport preserves smoothness of a spacetime test. -/
theorem contDiff_parabolicTestTransport {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {φ : ℝ × (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (parabolicTestTransport G t₀ x₀ r hr φ) :=
  hφ.comp (contDiff_parabolicGroupHomeomorph_symm G t₀ x₀ r hr)

/-- Transport preserves compact support of a spacetime test. -/
theorem hasCompactSupport_parabolicTestTransport {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {φ : ℝ × (Fin N → ℝ) → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (parabolicTestTransport G t₀ x₀ r hr φ) :=
  hφ.comp_homeomorph (parabolicGroupHomeomorph G t₀ x₀ r hr).symm

/-- A test supported in the inverse image of a spacetime domain transports to a test
supported in the original domain. -/
theorem tsupport_parabolicTestTransport_subset {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {φ : ℝ × (Fin N → ℝ) → ℝ} {O : Set (ℝ × (Fin N → ℝ))}
    (hφ : tsupport φ ⊆ (parabolicGroupHomeomorph G t₀ x₀ r hr) ⁻¹' O) :
    tsupport (parabolicTestTransport G t₀ x₀ r hr φ) ⊆ O := by
  intro z hz
  have hz' : (parabolicGroupHomeomorph G t₀ x₀ r hr).symm z ∈ tsupport φ := by
    rw [parabolicTestTransport, tsupport_comp_eq_preimage] at hz
    exact hz
  simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hφ hz'

end HeatKernel
