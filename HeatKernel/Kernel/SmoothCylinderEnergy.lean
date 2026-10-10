-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ClassicalHorizontalSlices
public import HeatKernel.Kernel.CompactCylinderBounds

/-! # Local energy of smooth functions on cylinders

Joint smoothness makes the classical horizontal gradient jointly smooth. The
function and its gradient therefore satisfy the local energy bounds on compact cylinders.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open RothschildStein

namespace HeatKernel

/-- The spatial differential of a slice is the joint differential in the spatial direction. -/
theorem fderiv_spatial_slice_apply {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}
    {t : ℝ} {x : Fin n → ℝ}
    (hu : DifferentiableAt ℝ (fun z : ℝ × (Fin n → ℝ) => u z.1 z.2) (t, x))
    (v : Fin n → ℝ) :
    fderiv ℝ (u t) x v =
      fderiv ℝ (fun z : ℝ × (Fin n → ℝ) => u z.1 z.2) (t, x) (0, v) := by
  have h := hu.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L v) h.fderiv

/-- The classical horizontal gradient of a jointly smooth function is jointly smooth. -/
theorem contDiffOn_horizontal_spatial_slices {n : ℕ}
    (I : Opens ℝ) (U : Opens (Fin n → ℝ))
    {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × (Fin n → ℝ) => u z.1 z.2)
      ((I : Set ℝ) ×ˢ (U : Set (Fin n → ℝ))))
    (V : (Fin n → ℝ) → Fin n → ℝ) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × (Fin n → ℝ) => fieldDerivative V (u z.1) z.2)
      ((I : Set ℝ) ×ˢ (U : Set (Fin n → ℝ))) := by
  have hopen := I.isOpen.prod U.isOpen
  have hd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fderiv ℝ (fun z : ℝ × (Fin n → ℝ) => u z.1 z.2))
      ((I : Set ℝ) ×ˢ (U : Set (Fin n → ℝ))) :=
    hu.fderiv_of_isOpen hopen (by simp)
  have hv : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × (Fin n → ℝ) => ((0 : ℝ), V z.2)) :=
    contDiff_const.prodMk (hV.comp contDiff_snd)
  apply (hd.clm_apply hv.contDiffOn).congr
  intro z hz
  exact fderiv_spatial_slice_apply
    ((hu.contDiffAt (hopen.mem_nhds hz)).differentiableAt (by simp)) (V z.2)

/-- Smooth cylinder functions and their horizontal gradients satisfy local L² energy bounds. -/
theorem local_energy_bounds_of_contDiffOn {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (I : Opens ℝ) (U : Opens (Fin n → ℝ))
    {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × (Fin n → ℝ) => u z.1 z.2)
      ((I : Set ℝ) ×ˢ (U : Set (Fin n → ℝ))))
    {J : Set ℝ} {K : Set (Fin n → ℝ)}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin n → ℝ))) :
    essSup (fun t => eLpNorm (u t) 2 (volume.restrict K)) (volume.restrict J) < ⊤ ∧
      ∀ i, MemLp (fun z : ℝ × (Fin n → ℝ) => fieldDerivative (X i) (u z.1) z.2)
        2 (volume.restrict (J ×ˢ K)) := by
  have hsub : J ×ˢ K ⊆ (I : Set ℝ) ×ˢ (U : Set (Fin n → ℝ)) :=
    Set.prod_mono hJI hKU
  refine ⟨essSup_spatial_eLpNorm_lt_top_of_continuousOn hJ hK
    (hu.continuousOn.mono hsub), fun i => ?_⟩
  exact memLp_two_restrict_of_continuousOn_compact (hJ.prod hK)
    ((contDiffOn_horizontal_spatial_slices I U hu (X i) (hX i)).continuousOn.mono hsub)

end HeatKernel
