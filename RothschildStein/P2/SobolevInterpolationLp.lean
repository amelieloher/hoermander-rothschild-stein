-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationMeasure
public import RothschildStein.P1.LeftParametrixAlgebra

/-!
# Sobolev interpolation, near and far parts: the `L^p` bounds `‖II‖_p ≤ C ε ‖L̃v‖_p`, `‖I‖_p ≤ C ε^{-1} ‖v‖_p`

For a type-1 operator `T` of a lifted drift frame, `T g(ξ) = ∫ k(ξ, η) g(η) dη` splits at the scale
`ε` with the cutoff `φ_ε(ξ, ·)` of the radial cutoff construction into the near part `II = nearPart` and the far part
`I = farPart`.

* `exists_nearPart_lp_bound` (the kernel route): the near kernel has size `A d̃^(1-Q)` on
  `d̃ ≤ c₂ ε`; the dyadic balls and the volume growth give row and column integrals `≤ C ε`
  (`exists_near_row_bound`) and Schur's test (Hölder in the kernel measure, then Fubini)
  gives `‖II‖_p ≤ C ε ‖g‖_p`.
* `exists_farPart_lp_bound`: after integrating `L̃` off `v` (the six contributions, size
  `K / max(d̃, c₁ ε)^(Q+1)`), the row and column integrals are `≤ C ε^{-1}`
  (`exists_far_row_bound`), so `‖I‖_p ≤ C ε^{-1} ‖v‖_p`.
* `exists_apply_eq_near_add_far`: `T g = II + I` pointwise on `V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

section Splitting

/-- A type-1 kernel against a function that is bounded and measurable on `V` is integrable
in the integration variable (size `A d̃^(1-Q)` and the volume growth). -/
theorem integrable_kernel_mul (hF : C.IsLiftedFrame F) (T : TypeOperator F 1)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ)))
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : AEStronglyMeasurable g (volume.restrict (F.V : Set _)))
    {Mg : ℝ} (hM : ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |g y| ≤ Mg) :
    Integrable (fun η => T.kernel ξ η * g η) := by
  have hL : IsCompact (closure (F.V : Set (Fin (n + m) → ℝ))) := hF.isCompact_closure
  have hLU : closure (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := hF.closure_subset
  have hVm : MeasurableSet (F.V : Set (Fin (n + m) → ℝ)) := F.V.isOpen.measurableSet
  have hQ1 : 1 ≤ C.G.homogeneousDimension := G2.homogeneousDimension_pos C.G
  have hker := TypeOperator.patchKernel hF (le_refl 1) T
  obtain ⟨A, S₀, hA, hS₀, hsz, -⟩ := hker.bounds
  obtain ⟨D₀, hD₀, hD⟩ := LiftedChart.exists_dl_bound (C := C) hL hLU
  obtain ⟨Cn, hCn, hrow⟩ := exists_near_row_bound C hL hLU
  have hint := integrable_dl_profile_mul (C := C) hL hLU subset_closure hVm
    (measurable_interpNearProfile A D₀ (C.G.homogeneousDimension - 1))
    (fun t ht => interpNearProfile_nonneg hA _ ht) (hrow A D₀ hA hD₀) (subset_closure hξ)
    (g := fun _ => (1 : ℝ)) aestronglyMeasurable_const (Mg := 1) (fun _ _ => by simp)
  have hslice : Measurable (sliceKernel (closure (F.V : Set (Fin (n + m) → ℝ))) T.kernel ξ) :=
    hker.measurable.of_uncurry_left (x := ξ)
  have hk : AEStronglyMeasurable (T.kernel ξ) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
    refine hslice.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_of_ae (C.ae_ne ξ), ae_restrict_mem hVm] with η hηξ hη
    exact sliceKernel_of_mem (subset_closure hξ) (subset_closure hη) (Ne.symm hηξ)
  have hIO : IntegrableOn (fun η => T.kernel ξ η * g η) (F.V : Set (Fin (n + m) → ℝ)) := by
    refine Integrable.mono' (hint.mul_const (max Mg 0)) (hk.mul hg) ?_
    filter_upwards [ae_restrict_of_ae (C.ae_ne ξ), ae_restrict_mem hVm] with η hηξ hη
    have hd : (C.dl ξ η).toReal ≤ D₀ := hD ξ (subset_closure hξ) η (subset_closure hη)
    have hdpos : 0 < (C.dl ξ η).toReal :=
      C.dl_toReal_pos (hLU (subset_closure hξ)) (hLU (subset_closure hη)) hηξ
    have hk' : |T.kernel ξ η| ≤ A * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ)) := by
      have := hsz ξ (subset_closure hξ) η (subset_closure hη) hηξ.symm
      simpa only [Nat.cast_one] using this
    have hg' : |g η| ≤ max Mg 0 := (hM η hη).trans (le_max_left _ _)
    rw [zpow_one_sub_dim _ hQ1] at hk'
    rw [Real.norm_eq_abs, abs_mul]
    unfold interpNearProfile
    rw [interpCut_eq_one hD₀ hd]
    calc |T.kernel ξ η| * |g η|
        ≤ (A * ((C.dl ξ η).toReal ^ (C.G.homogeneousDimension - 1))⁻¹) * max Mg 0 :=
          mul_le_mul hk' hg' (abs_nonneg _) (by positivity)
      _ = A * 1 / (C.dl ξ η).toReal ^ (C.G.homogeneousDimension - 1) * |(1 : ℝ)| * max Mg 0 := by
          rw [abs_one]
          ring
  have hsupp : Function.support (fun η => T.kernel ξ η * g η) ⊆ (F.V : Set (Fin (n + m) → ℝ)) := by
    intro η hη
    by_contra hηV
    have hne : ξ ≠ η := fun e => hηV (e ▸ hξ)
    exact hη (by
      show T.kernel ξ η * g η = 0
      rw [hker.support ξ η hne (Or.inr hηV), zero_mul])
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hIO

/-- **`T g = II + I`**: for a type-1 operator, `0 < ε < ε₀`, `g` bounded and measurable on
`V` and `ξ ∈ V`, the integral `T g(ξ) = ∫ k(ξ, η) g(η) dη` is the sum of the near part and the far
part (both are integrable since `0 ≤ φ_ε ≤ 1` is continuous). -/
theorem exists_apply_eq_near_add_far (hF : C.IsLiftedFrame F) (T : TypeOperator F 1)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ g : (Fin (n + m) → ℝ) → ℝ,
        AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →
        (∃ Mg : ℝ, ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |g y| ≤ Mg) →
        ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
          T.apply g ξ = nearPart C ν T ε g ξ + farPart C ν T ε g ξ := by
  have hL : IsCompact (closure (F.V : Set (Fin (n + m) → ℝ))) := hF.isCompact_closure
  have hLU : closure (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := hF.closure_subset
  obtain ⟨ε₀, c₁, c₂, B, hε₀, hε₀1, hc₁, hc₂, hB, hcut⟩ := exists_centredCutoff C ν hν hL hLU
  refine ⟨ε₀, hε₀, hε₀1, fun ε hε hεr g hg ⟨Mg, hM⟩ ξ hξ => ?_⟩
  obtain ⟨hsm, hrange, -⟩ := hcut ξ (subset_closure hξ) ε hε hεr
  have hkg := integrable_kernel_mul hF T hξ hg hM
  have hφm : AEStronglyMeasurable (radialCutoff C ν ξ (ε / 4) ε) volume :=
    hsm.continuous.aestronglyMeasurable
  have hnear : Integrable (fun η => T.kernel ξ η * radialCutoff C ν ξ (ε / 4) ε η * g η) := by
    refine (hkg.bdd_mul (f := radialCutoff C ν ξ (ε / 4) ε) (c := 1) hφm
      (ae_of_all _ fun η => ?_)).congr (ae_of_all _ fun η => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (hrange η).1]
      exact (hrange η).2
    · beta_reduce
      ring
  have hfar : Integrable (fun η => T.kernel ξ η * (1 - radialCutoff C ν ξ (ε / 4) ε η) * g η) := by
    refine (hkg.bdd_mul (f := fun η => 1 - radialCutoff C ν ξ (ε / 4) ε η) (c := 1)
      (aestronglyMeasurable_const.sub hφm) (ae_of_all _ fun η => ?_)).congr
      (ae_of_all _ fun η => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(hrange η).2])]
      linarith [(hrange η).1]
    · beta_reduce
      ring
  unfold TypeOperator.apply nearPart farPart
  rw [ite_eq_right one_ne_zero, ← integral_add hnear hfar]
  refine integral_congr_ae (ae_of_all _ fun η => ?_)
  beta_reduce
  ring

end Splitting

section Bounds

/-- **The near part is `O(ε)` in `L^p`.** For a type-1
operator `T` of a lifted frame there are `ε₀ ∈ (0, 1]` and `Cn > 0` (independent of `p`) such that for
`0 < ε < ε₀`, `1 ≤ p < ∞` and `g ∈ L^p(V)` bounded on `V`,
`‖II‖_{L^p(V)} ≤ Cn ε ‖g‖_{L^p(V)}` (BB p. 583, with the erratum that `g = L̃ v`: the integral
immediately above the printed maximal-function bound proves the corrected statement). -/
theorem exists_nearPart_lp_bound (hF : C.IsLiftedFrame F) (T : TypeOperator F 1)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) :
    ∃ ε₀ Cn : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < Cn ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ p : ℝ, 1 ≤ p → ∀ g : (Fin (n + m) → ℝ) → ℝ,
        MemLp g (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →
        (∃ Mg : ℝ, ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |g y| ≤ Mg) →
        eLpNorm (nearPart C ν T ε g) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
          ENNReal.ofReal (Cn * ε) *
            eLpNorm g (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
  have hL : IsCompact (closure (F.V : Set (Fin (n + m) → ℝ))) := hF.isCompact_closure
  have hLU : closure (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := hF.closure_subset
  have hVm : MeasurableSet (F.V : Set (Fin (n + m) → ℝ)) := F.V.isOpen.measurableSet
  have hker := TypeOperator.patchKernel hF (le_refl 1) T
  obtain ⟨ε₀, A, c₂, hε₀, hε₀1, hA, hc₂, hnear⟩ := exists_nearPart_bound hF T ν hν
  obtain ⟨Cn, hCn, hrow⟩ := exists_near_row_bound C hL hLU
  refine ⟨ε₀, Cn * (A + 1) * c₂, hε₀, hε₀1, by positivity, fun ε hε hεr p hp g hgp hbd => ?_⟩
  obtain ⟨Mg, hMg⟩ := hbd
  have hb : 0 < c₂ * ε := mul_pos hc₂ hε
  have hΛ : 0 < Cn * (A + 1) * c₂ * ε := by positivity
  have hrow' : ∀ x ∈ closure (F.V : Set (Fin (n + m) → ℝ)),
      ∫⁻ y in closure (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal (interpNearProfile A (c₂ * ε)
        (C.G.homogeneousDimension - 1) (C.dl x y).toReal) ≤
        ENNReal.ofReal (Cn * (A + 1) * c₂ * ε) := by
    intro x hx
    refine (hrow A (c₂ * ε) hA hb x hx).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ Cn * (c₂ * ε) := by positivity
    nlinarith
  have := eLpNorm_le_of_dl_dominated (C := C) (S := closure (F.V : Set (Fin (n + m) → ℝ)))
    (V := (F.V : Set (Fin (n + m) → ℝ))) hL hLU subset_closure hVm
    (measurable_interpNearProfile A (c₂ * ε) (C.G.homogeneousDimension - 1))
    (fun t ht => interpNearProfile_nonneg hA _ ht) hΛ hrow' hp hgp
    (aestronglyMeasurable_nearPart T hker ν ε hgp.aestronglyMeasurable)
    (fun x hx => hnear ε hε hεr x hx g hgp.aestronglyMeasurable Mg hMg)
  exact this

end Bounds

section FarBounds

variable {n q s m : ℕ} {w : Fin (q + 1) → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **The far part is `O(ε^{-1})` in `L^p`.** For a type-1 operator `T` of a lifted drift
frame there are `ε₀ ∈ (0, 1]` and `Kf > 0` (independent of `p`) such that for `0 < ε < ε₀`,
`1 ≤ p < ∞` and every test function `v ∈ C_c^∞(V)`, `‖I‖_{L^p(V)} ≤ Kf ε^{-1} ‖v‖_{L^p(V)}`, where
`I = ∫ k (1 - φ_ε) L̃ v` (BB pp. 581-583: the six contributions are each `≤ C ε^{-1}`). -/
theorem exists_farPart_lp_bound (hF : C.IsLiftedFrame F)
    (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hw0 : (w 0 : ℕ) = 2) (T : TypeOperator F 1)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) :
    ∃ ε₀ Kf : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < Kf ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ p : ℝ, 1 ≤ p → ∀ v : TestFunction F.V ℝ (⊤ : ℕ∞),
        eLpNorm (farPart C ν T ε (sumSquaresWithDrift C.Xl v)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
          ENNReal.ofReal (Kf / ε) *
            eLpNorm v (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
  have hL : IsCompact (closure (F.V : Set (Fin (n + m) → ℝ))) := hF.isCompact_closure
  have hLU : closure (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := hF.closure_subset
  have hVm : MeasurableSet (F.V : Set (Fin (n + m) → ℝ)) := F.V.isOpen.measurableSet
  have hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.contDiffOn_Xl_U i).mono hF.subset_U
  have hker := TypeOperator.patchKernel hF (le_refl 1) T
  obtain ⟨ε₀, K₀, c₁, hε₀, hε₀1, hK0, hc₁, hfar⟩ := exists_farPart_integral_bound hF hw hw0 T ν hν
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
  have hgmeas : AEStronglyMeasurable (sumSquaresWithDrift C.Xl v)
      (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
    have := (sumSquaresWithDriftTest F.V C.Xl hXV v).continuous.aestronglyMeasurable
      (μ := volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
    rwa [sumSquaresWithDriftTest_coe] at this
  have hvp : MemLp v (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
    testFunction_memLp F.V hF.volume_lt_top v _
  have := eLpNorm_le_of_dl_dominated (C := C) (S := closure (F.V : Set (Fin (n + m) → ℝ)))
    (V := (F.V : Set (Fin (n + m) → ℝ))) hL hLU subset_closure hVm
    (measurable_interpFarProfile K₀ (c₁ * ε) (C.G.homogeneousDimension - 1))
    (fun t ht => interpFarProfile_nonneg hK0 hb _ ht) hΛ hrow' hp hvp
    (aestronglyMeasurable_farPart T hker ν ε hgmeas)
    (fun x hx => hfar ε hε hεr v x hx)
  exact this

end FarBounds

end RothschildStein.P2
