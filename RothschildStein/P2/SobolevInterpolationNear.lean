-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationCutoff
public import RothschildStein.P2.SobolevInterpolationShell
public import RothschildStein.P1.ContinuityTheorem

/-!
# Sobolev interpolation, near part: the near part is `O(ε)`

For a type-1 operator `T` of a lifted frame and the cutoff `φ_ε(ξ, ·)` centred at `ξ`
(`SobolevInterpolationCutoff`, `φ_ε = 0` for `d̃ > c₂ ε`), the near part
`II(ξ) = ∫ T.kernel ξ η φ_ε(ξ, η) g(η) dη` is dominated, through the kernel size bound
`|T.kernel| ≤ A d̃^(1-Q)`, by the integral operator with kernel `A θ_{c₂ε}(d̃) d̃^(1-Q)`
(`exists_nearPart_bound`), whose row and column integrals are `≤ C A ε` by the dyadic balls and the
volume growth (`exists_near_row_bound`), so that `‖II‖_p ≤ C ε ‖g‖_p` by Schur (Hölder in the kernel
measure followed by Fubini; `eLpNorm_le_of_dl_dominated`). (BB p. 583,
corrected: the bound there must contain `g = L̃ v`.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

section Integrable

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}
  {S V : Set (Fin (n + m) → ℝ)} {φ : ℝ → ℝ}

/-- A row `η ↦ φ(d̃(ξ, η)) |g(η)|` of a dominating kernel against a bounded measurable `g` is
integrable on `V` when the row integral of the kernel is finite. -/
theorem integrable_dl_profile_mul (hS : IsCompact S) (hSU : S ⊆ C.U) (hVS : V ⊆ S)
    (hV : MeasurableSet V) (hφm : Measurable φ) (hφ0 : ∀ t, 0 ≤ t → 0 ≤ φ t) {Λ : ℝ}
    (hrow : ∀ x ∈ S, ∫⁻ y in S, ENNReal.ofReal (φ (C.dl x y).toReal) ≤ ENNReal.ofReal Λ)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ S) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict V)) {Mg : ℝ} (hM : ∀ y ∈ V, |g y| ≤ Mg) :
    Integrable (fun η => φ (C.dl ξ η).toReal * |g η|) (volume.restrict V) := by
  have hK := measurable_dlKernel (C := C) hS.measurableSet hSU hφm
  have hslice : Measurable (dlKernel C S φ ξ) := hK.of_uncurry_left (x := ξ)
  have hae : (fun η => φ (C.dl ξ η).toReal) =ᵐ[volume.restrict V] dlKernel C S φ ξ := by
    filter_upwards [ae_restrict_mem hV] with η hη
    rw [dlKernel_of_mem hξ (hVS hη)]
  have hasm : AEStronglyMeasurable (fun η => φ (C.dl ξ η).toReal) (volume.restrict V) :=
    hslice.aestronglyMeasurable.congr hae.symm
  refine ⟨hasm.mul hg.norm, ?_⟩
  have hMg' : (0 : ℝ) ≤ max Mg 0 := le_max_right _ _
  unfold HasFiniteIntegral
  calc ∫⁻ η, ‖φ (C.dl ξ η).toReal * |g η|‖ₑ ∂(volume.restrict V)
      ≤ ∫⁻ η, ENNReal.ofReal (φ (C.dl ξ η).toReal) * ENNReal.ofReal (max Mg 0)
          ∂(volume.restrict V) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hV] with η hη
        rw [enorm_mul, Real.enorm_eq_ofReal (hφ0 _ ENNReal.toReal_nonneg),
          Real.enorm_eq_ofReal_abs, abs_abs]
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ((hM η hη).trans (le_max_left _ _)))
    _ ≤ ∫⁻ η, ENNReal.ofReal (φ (C.dl ξ η).toReal) * ENNReal.ofReal (max Mg 0)
          ∂(volume.restrict S) := lintegral_mono' (Measure.restrict_mono hVS le_rfl) le_rfl
    _ = (∫⁻ η in S, ENNReal.ofReal (φ (C.dl ξ η).toReal)) * ENNReal.ofReal (max Mg 0) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (max Mg 0) := mul_le_mul' (hrow ξ hξ) le_rfl
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end Integrable

section Near

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The size `d^(1-Q)` as `1 / d^(Q-1)`. -/
theorem zpow_one_sub_dim {d : ℝ} (Q : ℕ) (hQ : 1 ≤ Q) :
    d ^ ((1 : ℤ) - (Q : ℤ)) = (d ^ (Q - 1))⁻¹ := by
  rw [show (1 : ℤ) - (Q : ℤ) = -((Q - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]

/-- **The near part is dominated by the near kernel.** For a type-1
operator `T` of a lifted frame there are `ε₀ ∈ (0, 1]`, `A ≥ 0`, `c₂ > 0` such that for `0 < ε < ε₀`,
`ξ ∈ V` and every `g` measurable and bounded on `V`,
`|∫ T.kernel ξ η φ_ε(ξ, η) g(η) dη| ≤ ∫_V A θ_{c₂ε}(d̃(ξ, η)) d̃(ξ, η)^(1-Q) |g(η)| dη`. -/
theorem exists_nearPart_bound (hF : C.IsLiftedFrame F) (T : TypeOperator F 1)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) :
    ∃ ε₀ A c₂ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 ≤ A ∧ 0 < c₂ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), ∀ g : (Fin (n + m) → ℝ) → ℝ,
        AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →
        ∀ Mg : ℝ, (∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |g y| ≤ Mg) →
          |∫ η, T.kernel ξ η * radialCutoff C ν ξ (ε / 4) ε η * g η| ≤
            ∫ η in (F.V : Set (Fin (n + m) → ℝ)),
              interpNearProfile A (c₂ * ε) (C.G.homogeneousDimension - 1) (C.dl ξ η).toReal *
                |g η| := by
  have hL : IsCompact (closure (F.V : Set (Fin (n + m) → ℝ))) := hF.isCompact_closure
  have hLU : closure (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := hF.closure_subset
  have hQ1 : 1 ≤ C.G.homogeneousDimension := G2.homogeneousDimension_pos C.G
  have hker := TypeOperator.patchKernel hF (le_refl 1) T
  obtain ⟨A₀, S₀, hA₀, hS₀, hsz, -⟩ := hker.bounds
  obtain ⟨ε₀, c₁, c₂, B, hε₀, hε₀1, hc₁, hc₂, hB, hcut⟩ := exists_centredCutoff C ν hν hL hLU
  obtain ⟨Cn, hCn, hrow⟩ := exists_near_row_bound C hL hLU
  refine ⟨ε₀, A₀, c₂, hε₀, hε₀1, hA₀, hc₂, fun ε hε hεr ξ hξ g hgm Mg hMg => ?_⟩
  obtain ⟨hsm, hrange, -, hfar0, -⟩ := hcut ξ (subset_closure hξ) ε hε hεr
  set φ : (Fin (n + m) → ℝ) → ℝ := radialCutoff C ν ξ (ε / 4) ε with hφ
  have hb : 0 < c₂ * ε := mul_pos hc₂ hε
  have hVm : MeasurableSet (F.V : Set (Fin (n + m) → ℝ)) := F.V.isOpen.measurableSet
  have hint := integrable_dl_profile_mul (C := C) hL hLU subset_closure hVm
    (measurable_interpNearProfile A₀ (c₂ * ε) (C.G.homogeneousDimension - 1))
    (fun t ht => interpNearProfile_nonneg hA₀ _ ht)
    (hrow A₀ (c₂ * ε) hA₀ hb) (subset_closure hξ) hgm hMg
  have hF0 : ∀ η ∉ (F.V : Set (Fin (n + m) → ℝ)), T.kernel ξ η * φ η * g η = 0 := by
    intro η hη
    have hne : ξ ≠ η := fun h => hη (h ▸ hξ)
    rw [hker.support ξ η hne (Or.inr hη), zero_mul, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF0, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hint ?_
  filter_upwards [ae_restrict_mem hVm, ae_restrict_of_ae (C.ae_ne ξ)] with η hη hηξ
  have hηU : η ∈ C.U := hLU (subset_closure hη)
  have hdpos : 0 < (C.dl ξ η).toReal := C.dl_toReal_pos (hLU (subset_closure hξ)) hηU hηξ
  set d : ℝ := (C.dl ξ η).toReal with hd
  have hk : |T.kernel ξ η| ≤ A₀ * d ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ)) := by
    have := hsz ξ (subset_closure hξ) η (subset_closure hη) hηξ.symm
    simpa only [Nat.cast_one] using this
  have hφθ : φ η ≤ interpCut (c₂ * ε) d := by
    by_cases hdc : d ≤ c₂ * ε
    · rw [interpCut_eq_one hb hdc]
      exact (hrange η).2
    · rw [hfar0 η hηU (not_le.mp hdc)]
      exact interpCut_nonneg _ _
  have hφ0 : 0 ≤ φ η := (hrange η).1
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hφ0, zpow_one_sub_dim _ hQ1] at *
  unfold interpNearProfile
  have hP : 0 < d ^ (C.G.homogeneousDimension - 1) := pow_pos hdpos _
  calc |T.kernel ξ η| * φ η * |g η|
      ≤ (A₀ * (d ^ (C.G.homogeneousDimension - 1))⁻¹) * interpCut (c₂ * ε) d * |g η| := by
        gcongr
    _ = A₀ * interpCut (c₂ * ε) d / d ^ (C.G.homogeneousDimension - 1) * |g η| := by
        rw [div_eq_mul_inv]
        ring

end Near

end RothschildStein.P2
