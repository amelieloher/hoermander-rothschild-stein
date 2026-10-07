-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationNoDriftFarPart
public import RothschildStein.P2.SobolevInterpolationLp
public import RothschildStein.P1.RepresentationHigher

/-!
# Sobolev interpolation without drift, far part: the `L^p` bound `‖I‖_p ≤ C ε^{-1} ‖v‖_p`

For a type-1 operator `T` of a lifted no-drift frame, after integrating `L̃` off `v` (the contributions
of BB p. 581 without drift, of size `K / max(d̃, c₁ ε)^(Q+1)`), the row and column integrals are
`≤ C ε^{-1}` (`exists_far_row_bound`), so `‖I‖_p ≤ C ε^{-1} ‖v‖_p`
(`exists_farPart_lp_bound_noDrift`). The near part and the splitting `T g = II + I` are
alphabet-generic (`exists_nearPart_lp_bound`, `exists_apply_eq_near_add_far`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **The far part is `O(ε^{-1})` in `L^p`, no drift.** For a type-1 operator `T` of a
lifted no-drift frame there are `ε₀ ∈ (0, 1]` and `Kf > 0` (independent of `p`) such that for
`0 < ε < ε₀`, `1 ≤ p < ∞` and every test function `v ∈ C_c^∞(V)`,
`‖I‖_{L^p(V)} ≤ Kf ε^{-1} ‖v‖_{L^p(V)}`, where `I = ∫ k (1 - φ_ε) L̃ v` (BB pp. 581-583). -/
theorem exists_farPart_lp_bound_noDrift (hF : C.IsLiftedFrame F)
    (hw : ∀ j, (w j : ℕ) = 1) (T : TypeOperator F 1)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) :
    ∃ ε₀ Kf : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < Kf ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ p : ℝ, 1 ≤ p → ∀ v : TestFunction F.V ℝ (⊤ : ℕ∞),
        eLpNorm (farPart C ν T ε (sumSquares C.Xl v)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
          ENNReal.ofReal (Kf / ε) *
            eLpNorm v (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
  have hL : IsCompact (closure (F.V : Set (Fin (n + m) → ℝ))) := hF.isCompact_closure
  have hLU : closure (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := hF.closure_subset
  have hVm : MeasurableSet (F.V : Set (Fin (n + m) → ℝ)) := F.V.isOpen.measurableSet
  have hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.contDiffOn_Xl_U i).mono hF.subset_U
  have hker := TypeOperator.patchKernel hF (le_refl 1) T
  obtain ⟨ε₀, K₀, c₁, hε₀, hε₀1, hK0, hc₁, hfar⟩ :=
    exists_farPart_integral_bound_noDrift hF hw T ν hν
  obtain ⟨Cf, hCf, hrow⟩ := exists_far_row_bound C hL hLU
  refine ⟨ε₀, Cf * (K₀ + 1) / c₁, hε₀, hε₀1, by positivity, fun ε hε hεr p hp v => ?_⟩
  have hb : 0 < c₁ * ε := mul_pos hc₁ hε
  have hΛ : 0 < Cf * (K₀ + 1) / c₁ / ε := by positivity
  have hrow' : ∀ x ∈ closure (F.V : Set (Fin (n + m) → ℝ)),
      ∫⁻ y in closure (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal (interpFarProfile K₀ (c₁ * ε)
        (C.G.homogeneousDimension - 1) (C.dl x y).toReal) ≤
        ENNReal.ofReal (Cf * (K₀ + 1) / c₁ / ε) := by
    intro x hx
    refine (hrow K₀ (c₁ * ε) hK0 hb x hx).trans (ENNReal.ofReal_le_ofReal ?_)
    have e : Cf * (K₀ + 1) / c₁ / ε = Cf * (K₀ + 1) / (c₁ * ε) := by
      rw [div_div]
    rw [e]
    exact div_le_div_of_nonneg_right (by nlinarith) hb.le
  have hgmeas : AEStronglyMeasurable (sumSquares C.Xl v)
      (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
    have := (repSumSquaresTest F C.Xl hXV v).continuous.aestronglyMeasurable
      (μ := volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
    rwa [coe_repSumSquaresTest] at this
  have hvp : MemLp v (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
    testFunction_memLp F.V hF.volume_lt_top v _
  have := eLpNorm_le_of_dl_dominated (C := C) (S := closure (F.V : Set (Fin (n + m) → ℝ)))
    (V := (F.V : Set (Fin (n + m) → ℝ))) hL hLU subset_closure hVm
    (measurable_interpFarProfile K₀ (c₁ * ε) (C.G.homogeneousDimension - 1))
    (fun t ht => interpFarProfile_nonneg hK0 hb _ ht) hΛ hrow' hp hvp
    (aestronglyMeasurable_farPart T hker ν ε hgmeas)
    (fun x hx => hfar ε hε hεr v x hx)
  exact this

end RothschildStein.P2
