-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationNoDriftFar
public import RothschildStein.P2.SobolevInterpolationFarPart

/-!
# Sobolev interpolation without drift, far part: the far integral, after integrating `L̃` off `v`

For a type-1 operator `T` of a lifted no-drift frame, a test function `v ∈ C_c^∞(V)` and `ξ ∈ V`, the
far part `∫ T.kernel ξ η (1 - φ_ε(ξ, η)) (L̃ v)(η) dη` equals `∫_V (L̃ᵀ κ_{ξ,ε}) v`
(`integral_mul_sumSquares_noDrift`, integration by parts against a `C²` kernel: the kernel is `C²` and `L̃ v` is supported in `V`) and is
bounded by `∫_V K₀ max(d̃(ξ, η), c₁ ε)^(-(Q+1)) |v(η)| dη` (`exists_farKernel_bound_noDrift`), the
dominating operator of `SobolevInterpolationShell` (`exists_farPart_integral_bound_noDrift`). (BB pp.
581-583, no drift.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

section Support

variable {N q : ℕ}

/-- `L̃ v` (no drift) vanishes outside the topological support of `v`. -/
theorem sumSquares_eq_zero_of_notMem_noDrift (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (v : (Fin N → ℝ) → ℝ) {x : Fin N → ℝ} (hx : x ∉ tsupport v) :
    sumSquares X v x = 0 := by
  have hz : ∀ I : List (Fin q), wordDerivative X I v x = 0 := fun I =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (S.tsupport_wordDerivative_subset X I v h))
  have h1 : ∀ i : Fin q, fieldDerivative (X i) (fieldDerivative (X i) v) x = 0 :=
    fun i => hz [i, i]
  simp [sumSquares, h1]

end Support

section FarPart

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **The far integral is bounded by the far kernel, no drift.** For a type-1 operator
`T` of a lifted no-drift frame there are `ε₀ ∈ (0, 1]`, `K₀ ≥ 0`, `c₁ > 0` such that for `0 < ε < ε₀`,
every test function `v ∈ C_c^∞(V)` and `ξ ∈ V`,
`|∫ T.kernel ξ η (1 - φ_ε(ξ, η)) (L̃ v)(η) dη| ≤ ∫_V K₀ max(d̃(ξ, η), c₁ ε)^(-(Q+1)) |v(η)| dη`. -/
theorem exists_farPart_integral_bound_noDrift (hF : C.IsLiftedFrame F)
    (hw : ∀ j, (w j : ℕ) = 1) (T : TypeOperator F 1)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) :
    ∃ ε₀ K₀ c₁ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 ≤ K₀ ∧ 0 < c₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ v : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
        |∫ η, T.kernel ξ η * (1 - radialCutoff C ν ξ (ε / 4) ε η) * sumSquares C.Xl v η| ≤
          ∫ η in (F.V : Set (Fin (n + m) → ℝ)),
            interpFarProfile K₀ (c₁ * ε) (C.G.homogeneousDimension - 1) (C.dl ξ η).toReal *
              |v η| := by
  have hL : IsCompact (closure (F.V : Set (Fin (n + m) → ℝ))) := hF.isCompact_closure
  have hLU : closure (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := hF.closure_subset
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := hF.subset_U
  have hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.contDiffOn_Xl_U i).mono hVU
  obtain ⟨ε₀, K₀, c₁, hε₀, hε₀1, hK0, hc₁, hfar⟩ := exists_farKernel_bound_noDrift hF hw T ν hν
  obtain ⟨Cf, hCf, hrow⟩ := exists_far_row_bound C hL hLU
  refine ⟨ε₀, K₀, c₁, hε₀, hε₀1, hK0, hc₁, fun ε hε hεr v ξ hξ => ?_⟩
  obtain ⟨hκ, hbd⟩ := hfar ε hε hεr ξ hξ
  have hb : 0 < c₁ * ε := mul_pos hc₁ hε
  have hVm : MeasurableSet (F.V : Set (Fin (n + m) → ℝ)) := F.V.isOpen.measurableSet
  obtain ⟨Mv, hMv⟩ := v.continuous.bounded_above_of_compact_support v.hasCompactSupport
  have hint := integrable_dl_profile_mul (C := C) hL hLU subset_closure hVm
    (measurable_interpFarProfile K₀ (c₁ * ε) (C.G.homogeneousDimension - 1))
    (fun t ht => interpFarProfile_nonneg hK0 hb _ ht)
    (hrow K₀ (c₁ * ε) hK0 hb) (subset_closure hξ)
    v.continuous.aestronglyMeasurable (Mg := Mv) (fun y _ => by simpa using hMv y)
  have hF0 : ∀ η ∉ (F.V : Set (Fin (n + m) → ℝ)),
      T.kernel ξ η * (1 - radialCutoff C ν ξ (ε / 4) ε η) * sumSquares C.Xl v η = 0 := by
    intro η hη
    rw [sumSquares_eq_zero_of_notMem_noDrift C.Xl v (fun h => hη (v.tsupport_subset h)),
      mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF0]
  have hibp := integral_mul_sumSquares_noDrift F.V C.Xl hXV
    (fun η => T.kernel ξ η * (1 - radialCutoff C ν ξ (ε / 4) ε η)) hκ v
  rw [hibp, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hint ?_
  filter_upwards [ae_restrict_mem hVm] with η hη
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hbd η hη) (abs_nonneg _)

end FarPart

end RothschildStein.P2
