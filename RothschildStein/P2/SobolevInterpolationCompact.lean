-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationLp
public import RothschildStein.P1.RepresentationFirstOrder
public import RothschildStein.P1.ContinuityTheorem
public import RothschildStein.P1.StandardFrame

/-!
# Sobolev interpolation, compact form: `‖Dv‖_p ≤ ε ‖L̃v‖_p + C ε^{-1} ‖v‖_p`

Assembly of the compact Sobolev interpolation inequality of BB Prop 11.38 (p. 580) from

* the first-order representation `X̃_l v = F_l L̃v + S_l v` (`representation_firstOrder_of`, for a
  cutoff `a ∈ C_c^∞(V)` with `a = 1` near `supp v`; hypotheses `LeftDifferentiation`, `SignedParametrix`),
* the near and far estimates of `SobolevInterpolationLp` for the type-1 operator `F_l`
  (`‖F_l L̃v‖_p ≤ C ε ‖L̃v‖_p + C ε^{-1} ‖v‖_p`),
* the `L^p` bound of the type-0 operator `S_l` (the continuity theorem, `TypeOperator.exists_lp_bound_standard`),
* the rescaling `ε ↦ ε / C` that gives the coefficient `1` before `‖L̃v‖_p`.

The statement is conditional exactly on the hypotheses of `representation_firstOrder_of`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

/-- A finite family of positive thresholds has a common positive lower bound. -/
theorem exists_pos_le_forall_fin {q : ℕ} (f : Fin q → ℝ) (hf : ∀ l, 0 < f l) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l, δ ≤ f l := by
  have hS : 0 ≤ ∑ l, 1 / f l := Finset.sum_nonneg (fun l _ => (one_div_pos.2 (hf l)).le)
  refine ⟨1 / (1 + ∑ l, 1 / f l), by positivity, fun l => ?_⟩
  have h1 : 1 / f l ≤ ∑ l, 1 / f l :=
    Finset.single_le_sum (f := fun l => 1 / f l) (fun l _ => (one_div_pos.2 (hf l)).le)
      (Finset.mem_univ l)
  rw [div_le_iff₀ (by positivity)]
  have : f l * (1 / f l) = 1 := mul_one_div_cancel (hf l).ne'
  nlinarith [hf l]

section Combine

variable {n q s m : ℕ} {w : Fin (q + 1) → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The Lie derivatives `L̃ v` of a test function are bounded and measurable on `V`. -/
theorem sumSquaresWithDrift_test_props (hF : C.IsLiftedFrame F) (v : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    ∀ p : ℝ, MemLp (sumSquaresWithDrift C.Xl v) (ENNReal.ofReal p)
        (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ∧
      ∃ Mg : ℝ, ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |sumSquaresWithDrift C.Xl v y| ≤ Mg := by
  intro p
  have hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.contDiffOn_Xl_U i).mono hF.subset_U
  let g := sumSquaresWithDriftTest F.V C.Xl hXV v
  have hg : (g : (Fin (n + m) → ℝ) → ℝ) = sumSquaresWithDrift C.Xl v :=
    sumSquaresWithDriftTest_coe F.V C.Xl hXV v
  refine ⟨?_, ?_⟩
  · have := testFunction_memLp F.V hF.volume_lt_top g (ENNReal.ofReal p)
    rwa [hg] at this
  · obtain ⟨M, hM⟩ := g.continuous.bounded_above_of_compact_support g.hasCompactSupport
    refine ⟨M, fun y _ => ?_⟩
    have := hM y
    rw [hg, Real.norm_eq_abs] at this
    exact this

/-- **`F L̃v` is `O(ε)‖L̃v‖_p + O(ε^{-1})‖v‖_p`**: for a type-1 operator `T` of a lifted drift frame
there are `ε₀ ∈ (0, 1]`, `Cn, Kf > 0` (independent of `p`) such that for `0 < ε < ε₀`, `1 ≤ p < ∞` and
`v ∈ C_c^∞(V)` the function `T (L̃ v)` is a.e.-measurable and
`‖T (L̃ v)‖_p ≤ Cn ε ‖L̃ v‖_p + Kf ε^{-1} ‖v‖_p` (near part plus far part). -/
theorem exists_eLpNorm_apply_le (hF : C.IsLiftedFrame F)
    (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hw0 : (w 0 : ℕ) = 2) (T : TypeOperator F 1)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) :
    ∃ ε₀ Cn Kf : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < Cn ∧ 0 < Kf ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ p : ℝ, 1 ≤ p → ∀ v : TestFunction F.V ℝ (⊤ : ℕ∞),
        AEStronglyMeasurable (T.apply (sumSquaresWithDrift C.Xl v))
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ∧
        eLpNorm (T.apply (sumSquaresWithDrift C.Xl v)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
          ENNReal.ofReal (Cn * ε) * eLpNorm (sumSquaresWithDrift C.Xl v) (ENNReal.ofReal p)
              (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
            ENNReal.ofReal (Kf / ε) *
              eLpNorm v (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
  have hVm : MeasurableSet (F.V : Set (Fin (n + m) → ℝ)) := F.V.isOpen.measurableSet
  have hker := TypeOperator.patchKernel hF (le_refl 1) T
  obtain ⟨ε₁, Cn, hε₁, hε₁1, hCn, hnear⟩ := exists_nearPart_lp_bound hF T ν hν
  obtain ⟨ε₂, Kf, hε₂, hε₂1, hKf, hfar⟩ := exists_farPart_lp_bound hF hw hw0 T ν hν
  obtain ⟨ε₃, hε₃, hε₃1, hsplit⟩ := exists_apply_eq_near_add_far hF T ν hν
  refine ⟨min ε₁ (min ε₂ ε₃), Cn, Kf, lt_min hε₁ (lt_min hε₂ hε₃),
    (min_le_left _ _).trans hε₁1, hCn, hKf, fun ε hε hεr p hp v => ?_⟩
  have h1 : ε < ε₁ := lt_of_lt_of_le hεr (min_le_left _ _)
  have h2 : ε < ε₂ := lt_of_lt_of_le hεr ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : ε < ε₃ := lt_of_lt_of_le hεr ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hgmem, Mg, hMg⟩ := sumSquaresWithDrift_test_props hF v p
  set g : (Fin (n + m) → ℝ) → ℝ := sumSquaresWithDrift C.Xl v with hg
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
