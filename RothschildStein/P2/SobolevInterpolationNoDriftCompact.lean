-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationNoDriftLp
public import RothschildStein.P2.SobolevInterpolationCompact

/-!
# Sobolev interpolation without drift, compact form: `‖F L̃v‖_p ≤ C ε ‖L̃v‖_p + C ε^{-1} ‖v‖_p`

For a type-1 operator `F` of a lifted no-drift frame (alphabet `Fin q`, all weights one,
`L̃ = sumSquares`), the near part (`exists_nearPart_lp_bound`, alphabet-generic) and the far part
(`exists_farPart_lp_bound_noDrift`) of the splitting `F g = II + I` (`exists_apply_eq_near_add_far`) give
`‖F L̃v‖_p ≤ Cn ε ‖L̃v‖_p + Kf ε^{-1} ‖v‖_p` for `0 < ε < ε₀` (BB pp. 581-583).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

section Combine

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The Lie derivatives `L̃ v` (no drift) of a test function are bounded and measurable on `V`. -/
theorem sumSquares_test_props_noDrift (hF : C.IsLiftedFrame F) (v : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    ∀ p : ℝ, MemLp (sumSquares C.Xl v) (ENNReal.ofReal p)
        (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ∧
      ∃ Mg : ℝ, ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |sumSquares C.Xl v y| ≤ Mg := by
  intro p
  have hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.contDiffOn_Xl_U i).mono hF.subset_U
  let g := repSumSquaresTest F C.Xl hXV v
  have hg : (g : (Fin (n + m) → ℝ) → ℝ) = sumSquares C.Xl v := coe_repSumSquaresTest hXV v
  refine ⟨?_, ?_⟩
  · have := testFunction_memLp F.V hF.volume_lt_top g (ENNReal.ofReal p)
    rwa [hg] at this
  · obtain ⟨M, hM⟩ := g.continuous.bounded_above_of_compact_support g.hasCompactSupport
    refine ⟨M, fun y _ => ?_⟩
    have := hM y
    rw [hg, Real.norm_eq_abs] at this
    exact this

/-- **`F L̃v` is `O(ε)‖L̃v‖_p + O(ε^{-1})‖v‖_p`, no drift**: for a type-1 operator `T` of a lifted
no-drift frame there are `ε₀ ∈ (0, 1]`, `Cn, Kf > 0` (independent of `p`) such that for `0 < ε < ε₀`,
`1 ≤ p < ∞` and `v ∈ C_c^∞(V)` the function `T (L̃ v)` is a.e.-measurable and
`‖T (L̃ v)‖_p ≤ Cn ε ‖L̃ v‖_p + Kf ε^{-1} ‖v‖_p` (near part plus far part). -/
theorem exists_eLpNorm_apply_le_noDrift (hF : C.IsLiftedFrame F)
    (hw : ∀ j, (w j : ℕ) = 1) (T : TypeOperator F 1)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) :
    ∃ ε₀ Cn Kf : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < Cn ∧ 0 < Kf ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ p : ℝ, 1 ≤ p → ∀ v : TestFunction F.V ℝ (⊤ : ℕ∞),
        AEStronglyMeasurable (T.apply (sumSquares C.Xl v))
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ∧
        eLpNorm (T.apply (sumSquares C.Xl v)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
          ENNReal.ofReal (Cn * ε) * eLpNorm (sumSquares C.Xl v) (ENNReal.ofReal p)
              (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
            ENNReal.ofReal (Kf / ε) *
              eLpNorm v (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
  have hVm : MeasurableSet (F.V : Set (Fin (n + m) → ℝ)) := F.V.isOpen.measurableSet
  have hker := TypeOperator.patchKernel hF (le_refl 1) T
  obtain ⟨ε₁, Cn, hε₁, hε₁1, hCn, hnear⟩ := exists_nearPart_lp_bound hF T ν hν
  obtain ⟨ε₂, Kf, hε₂, hε₂1, hKf, hfar⟩ := exists_farPart_lp_bound_noDrift hF hw T ν hν
  obtain ⟨ε₃, hε₃, hε₃1, hsplit⟩ := exists_apply_eq_near_add_far hF T ν hν
  refine ⟨min ε₁ (min ε₂ ε₃), Cn, Kf, lt_min hε₁ (lt_min hε₂ hε₃),
    (min_le_left _ _).trans hε₁1, hCn, hKf, fun ε hε hεr p hp v => ?_⟩
  have h1 : ε < ε₁ := lt_of_lt_of_le hεr (min_le_left _ _)
  have h2 : ε < ε₂ := lt_of_lt_of_le hεr ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : ε < ε₃ := lt_of_lt_of_le hεr ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hgmem, Mg, hMg⟩ := sumSquares_test_props_noDrift hF v p
  set g : (Fin (n + m) → ℝ) → ℝ := sumSquares C.Xl v with hg
  have hgm : AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
    hgmem.aestronglyMeasurable
  have hnm := aestronglyMeasurable_nearPart T hker ν ε hgm
  have hfm : AEStronglyMeasurable (farPart C ν T ε g)
      (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := aestronglyMeasurable_farPart T hker ν ε hgm
  have heq : T.apply g =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))]
      fun ξ => nearPart C ν T ε g ξ + farPart C ν T ε g ξ := by
    filter_upwards [ae_restrict_mem hVm] with ξ hξ
    exact hsplit ε hε h3 g hgm ⟨Mg, hMg⟩ ξ hξ
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  refine ⟨(hnm.add hfm).congr heq.symm, ?_⟩
  calc eLpNorm (T.apply g) (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
      = eLpNorm (fun ξ => nearPart C ν T ε g ξ + farPart C ν T ε g ξ) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := eLpNorm_congr_ae heq
    _ ≤ eLpNorm (nearPart C ν T ε g) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
        eLpNorm (farPart C ν T ε g) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := eLpNorm_add_le hp1
    _ ≤ _ := add_le_add (hnear ε hε h1 p hp g hgmem ⟨Mg, hMg⟩) (hfar ε hε h2 p hp v)

end Combine

end RothschildStein.P2
