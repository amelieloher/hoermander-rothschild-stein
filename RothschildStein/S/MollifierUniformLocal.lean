-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ContinuousTestProducts
public import RothschildStein.S.MollifierUniformAllDimensions
public import RothschildStein.S.InteriorTubeTranslations
public import RothschildStein.S.BaseKernelAllDimensions
public import RothschildStein.S.WeakKernelTransferPatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- On an interior compact patch, zero-extended ordinary
mollifiers of continuous local data converge uniformly. A plateau
on the coefficient tube supplies a global continuous extension;
no global integrability of the original input is required
(BB Thm 2.20, p. 86; cutoff extension). -/
theorem tendstoUniformlyOn_regularize_zeroExtension_local
    (Ω : Opens (Fin n → ℝ)) {U : Set (Fin n → ℝ)}
    (hc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω)
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (Ω : Set (Fin n → ℝ))) :
    TendstoUniformlyOn (fun ε : ℝ => euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε)
      f (𝓝[>] 0) U := by
  obtain ⟨δ,hd,hδ⟩ := exists_friedrichs_interior_radius Ω hc hUΩ
  obtain ⟨χ,W,hW,hKW,hWΩ,hχ⟩ := exists_test_plateau Ω
    ⟨cthickening δ (closure U),hc.cthickening⟩ hδ
  let g := fun x => f x*χ x
  have hct : Continuous g := continuous_mul_test_of_continuousOn Ω hf χ
  have hcc : HasCompactSupport g := χ.hasCompactSupport.mul_left
  have he : EqOn g f U := by
    intro x hx
    have hi : χ x = 1 := hχ (hKW (subset_interior_cthickening hd hx))
    exact (show f x*χ x = f x by rw [hi,mul_one])
  have ht := (tendstoUniformly_euclideanRegularize_compact_all_dimensions hct hcc).tendstoUniformlyOn (s := U)
  apply (ht.congr_right he).congr
  filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
  intro x hx
  rw [← smoothBaseFriedrichsKernel_op g hε.1,
    ← smoothBaseFriedrichsKernel_op ((Ω : Set (Fin n → ℝ)).indicator f) hε.1]
  unfold friedrichsKernelOp
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change (smoothBaseFriedrichsKernel n).family ε x y*g (x+ε • y) =
    (smoothBaseFriedrichsKernel n).family ε x y*((Ω : Set (Fin n → ℝ)).indicator f) (x+ε • y)
  by_cases hy : y ∈ closedBall (0 : Fin n → ℝ) 1
  · have hs := add_smul_mem_interior_cthickening hε hx hy
    have hi : χ (x+ε • y) = 1 := hχ (hKW hs)
    simp only [g,hi,mul_one,indicator_of_mem (hδ hs)]
  · have hn : ¬ ‖y‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hy
    have hz : (smoothBaseFriedrichsKernel n).family ε x y = 0 :=
      (smoothBaseFriedrichsKernel n).vanish ((x,y),ε) (lt_of_not_ge hn)
    rw [hz]
    simp only [zero_mul]

end RothschildStein.S
