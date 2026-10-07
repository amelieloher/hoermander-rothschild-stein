-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsOps
public import RothschildStein.P1.SingularSplitEstimatesProduct
public import RothschildStein.P1.RestrictedErrorEstimates

/-!
# Kernel estimates of a symbol-class family

A family `A(ξ, η, u)` in the weighted symbol class `WtSym` of degree `d` (`ParametrixKernelBoundsClass`)
on every compact parameter set gives, with the kernel-estimate machinery,

* the size bound `|A(ξ, η, Θ(η, ξ))| ≤ M d̃(ξ, η)^d` on a compact `L ⊆ U` (`exists_size_bound_of_wtSym`);
* the kernel bounds `HasKernelBounds L ℓ` for `d = ℓ - Q` (`hasKernelBounds_of_wtSym`);
* the hypotheses `RestrictedKernelBounds` of the restricted-error bounds for `ℓ = 1` once the kernel agrees with
  `A(ξ, η, Θ(η, ξ))` off the diagonal (`exists_restrictedKernelBounds_of_wtSym`).

Kernel bounds only see the off-diagonal values (`HasKernelBounds.congr_of_ne`), so the value of the
fundamental kernel at the origin plays no role.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- **Size of a symbol-class kernel.** If `B ∈ WtSym` of degree `d` on `L × L` for every
radius, then `|B(ξ, η, Θ(η, ξ))| ≤ M d̃(ξ, η)^d` for `ξ ≠ η` in a compact `L ⊆ U` (the comparison
`ρ ≍ d̃` of the lifted chart). -/
theorem exists_size_bound_of_wtSym {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLU : L ⊆ C.U) {d : ℤ} {B : KZ (n + m) → ℝ}
    (hB : ∀ R : ℝ, 0 < R → WtSym C.G (L ×ˢ L) R 0 d B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ L, ∀ η ∈ L, ξ ≠ η →
      |B (ξ, η, C.Θ η ξ)| ≤ M * (C.dl ξ η).toReal ^ d := by
  obtain ⟨R₀, hR₀⟩ := C.exists_gauge_bound hL hLU
  have hRm : 0 < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨M, hM0, hM⟩ := (hB (max R₀ 1) hRm).bound
  refine ⟨M * C.gaugeConst ^ d.natAbs, by have := C.gaugeConst_pos; positivity, ?_⟩
  intro ξ hξ η hη hne
  have hu : C.Θ η ξ ≠ 0 := (C.theta_eq_zero_iff (hLU hη) (hLU hξ)).not.mpr hne
  have h1 := hM (ξ, η, C.Θ η ξ) ⟨hξ, hη⟩ hu ((hR₀ η hη ξ hξ).trans (le_max_left _ _))
  have h2 := C.gauge_zpow_le_dl (hLU hη) (hLU hξ) hne d
  rw [C.dl_symm ξ η]
  calc |B (ξ, η, C.Θ η ξ)| ≤ M * kgauge C.G (C.Θ η ξ) ^ d := h1
    _ ≤ M * (C.gaugeConst ^ d.natAbs * (C.dl η ξ).toReal ^ d) :=
        mul_le_mul_of_nonneg_left h2 hM0
    _ = M * C.gaugeConst ^ d.natAbs * (C.dl η ξ).toReal ^ d := by ring

variable {C}
variable {L : Set (Fin (n + m) → ℝ)} {ℓ : ℕ}
  {κ₁ κ₂ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}

/-- Kernel bounds only see the off-diagonal values of the kernel: the difference condition
`2 d̃(ξ, ξ') < d̃(ξ', η)` forces `ξ ≠ η` and `ξ' ≠ η`. -/
theorem HasKernelBounds.congr_of_ne (hLU : L ⊆ C.U) (h : C.HasKernelBounds L ℓ κ₁)
    (he : ∀ ξ ∈ L, ∀ η ∈ L, ξ ≠ η → κ₁ ξ η = κ₂ ξ η) : C.HasKernelBounds L ℓ κ₂ := by
  obtain ⟨A, S, hA, hS, hsz, hdf⟩ := h
  refine ⟨A, S, hA, hS, fun ξ hξ η hη hne => ?_, fun ξ hξ ξ' hξ' η hη hsep => ?_⟩
  · rw [← he ξ hξ η hη hne]
    exact hsz ξ hξ η hη hne
  · have hh0 : 0 ≤ (C.dl ξ ξ').toReal := ENNReal.toReal_nonneg
    have hpos : 0 < (C.dl ξ' η).toReal := by linarith
    have hne1 : ξ' ≠ η := by
      intro he'
      rw [he', show C.dl η η = 0 from G1.controlDistance_self w C.Xl
        (C.mem_O_of_mem_U (hLU hη))] at hpos
      simp at hpos
    have hne2 : ξ ≠ η := by
      intro he'
      rw [he', C.dl_symm η ξ'] at hsep
      linarith [ENNReal.toReal_nonneg (a := C.dl ξ' η)]
    rw [← he ξ' hξ' η hη hne1, ← he ξ hξ η hη hne2, ← he η hη ξ' hξ' hne1.symm,
      ← he η hη ξ hξ hne2.symm]
    exact hdf ξ hξ ξ' hξ' η hη hsep

/-- **Kernel bounds from a symbol class** (size bound, and difference bounds via path margins in
both variables). If `A ∈ WtSym` of degree `ℓ - Q` (one derivative) on `L' × L'` for every
compact `L'` and every radius, then the kernel `A(ξ, η, Θ(η, ξ))` has kernel bounds of
exponent `ℓ` on every compact `L ⊆ U`: size `A d̃^(ℓ - Q)` and difference
`S d̃(ξ, ξ') / d̃(ξ', η)^(Q + 1 - ℓ)` for `d̃(ξ', η) > 2 d̃(ξ, ξ')`, in both variables
(the second variable by the reflection `Â(ξ, η, u) = A(η, ξ, -u)` and `Θ(ξ, η) = -Θ(η, ξ)`). -/
theorem hasKernelBounds_of_wtSym (hL : IsCompact L) (hLU : L ⊆ C.U) {A : KZ (n + m) → ℝ}
    (hA : ∀ L' : Set (Fin (n + m) → ℝ), IsCompact L' → ∀ R : ℝ, 0 < R →
      WtSym C.G (L' ×ˢ L') R 1 ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ)) A) :
    C.HasKernelBounds L ℓ (fun ξ η => A (ξ, η, C.Θ η ξ)) := by
  set d : ℤ := (ℓ : ℤ) - (C.G.homogeneousDimension : ℤ) with hd
  have hΨ : ContDiffOn ℝ 1 (kernelUncurry fun ξ η u => A (ξ, η, u)) {z | z.2.2 ≠ 0} :=
    (hA ∅ isCompact_empty 1 one_pos).contDiffOn.of_le (by simp)
  have hWB : HasWeightedBounds C.G d (fun ξ η u => A (ξ, η, u)) := hasWeightedBounds_of_wtSym hA
  have hAr : ∀ L' : Set (Fin (n + m) → ℝ), IsCompact L' → ∀ R : ℝ, 0 < R →
      WtSym C.G (L' ×ˢ L') R 1 d (fun z : KZ (n + m) => A (z.2.1, z.1, -z.2.2)) :=
    fun L' hL' R hR => WtSym.reflect (K' := L' ×ˢ L') (fun p hp => ⟨hp.2, hp.1⟩) (hA L' hL' R hR)
  have hΨ' : ContDiffOn ℝ 1 (kernelUncurry fun ξ η u => A (η, ξ, -u)) {z | z.2.2 ≠ 0} :=
    (hAr ∅ isCompact_empty 1 one_pos).contDiffOn.of_le (by simp)
  have hWB' : HasWeightedBounds C.G d (fun ξ η u => A (η, ξ, -u)) :=
    hasWeightedBounds_of_wtSym hAr
  have hswap : ∀ ξ ∈ C.U, ∀ η ∈ C.U,
      (fun ξ η u => A (η, ξ, -u)) ξ η (C.Θ η ξ) = (fun ξ η u => A (ξ, η, u)) η ξ (C.Θ ξ η) := by
    intro ξ hξ η hη
    show A (η, ξ, -C.Θ η ξ) = A (η, ξ, C.Θ ξ η)
    rw [C.theta_antisymm η hη ξ hξ]
  obtain ⟨A₀, B₀, hA0, hB0, hsize, hdiff⟩ :=
    C.exists_kernel_estimates_of_weighted hΨ hWB hΨ' hWB' hswap hL hLU
  refine ⟨A₀, B₀, hA0, hB0, hsize, ?_⟩
  intro ξ hξ ξ' hξ' η hη hsep
  have h := hdiff ξ hξ ξ' hξ' η hη hsep
  have hr : 0 < (C.dl ξ' η).toReal := by linarith [ENNReal.toReal_nonneg (a := C.dl ξ ξ')]
  have hpow : (C.dl ξ' η).toReal ^ (d - 1) =
      ((C.dl ξ' η).toReal ^ ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ)))⁻¹ := by
    rw [← zpow_neg]
    congr 1
    rw [hd]
    ring
  rw [hpow, ← div_eq_mul_inv] at h
  have hrw : B₀ * ((C.dl ξ ξ').toReal / (C.dl ξ' η).toReal ^
      ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ))) = B₀ * (C.dl ξ ξ').toReal /
      (C.dl ξ' η).toReal ^ ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ)) := by ring
  rw [hrw] at h
  exact h

/-- The symbol-class kernel `A(ξ, η, Θ(η, ξ))` is continuous on `K₀ × K₀` off the
diagonal. -/
theorem continuousOn_symbolKernel {K₀ : Set (Fin (n + m) → ℝ)} (hK₀U : K₀ ⊆ C.U)
    {A : KZ (n + m) → ℝ} (hA : ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0}) :
    ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => A (p.1, p.2, C.Θ p.2 p.1))
      ((K₀ ×ˢ K₀) \ Set.diagonal (Fin (n + m) → ℝ)) := by
  have h := C.continuousOn_kernelValue hK₀U (χ := fun _ => (1 : ℝ)) continuous_const
    (W := fun ξ η u => A (ξ, η, u)) hA.continuousOn
  refine h.congr (fun p _ => ?_)
  show A (p.1, p.2, C.Θ p.2 p.1) = 1 * A (p.1, p.2, C.Θ p.2 p.1)
  exact (one_mul _).symm

/-- **The hypotheses of the restricted-error bounds from a symbol class.** If
`A ∈ WtSym` of degree `1 - Q` on every compact `L' × L'` and radius, and a kernel `kk` agrees with
`A(ξ, η, Θ(η, ξ))` off the diagonal of the compact `K₀ ⊆ U`, then `kk` satisfies
`RestrictedKernelBounds K₀ kk`. -/
theorem exists_restrictedKernelBounds_of_wtSym {K₀ : Set (Fin (n + m) → ℝ)}
    (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U) {A : KZ (n + m) → ℝ}
    (hA : ∀ L' : Set (Fin (n + m) → ℝ), IsCompact L' → ∀ R : ℝ, 0 < R →
      WtSym C.G (L' ×ˢ L') R 1 (((1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ)) A)
    {kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hkk : ∀ ξ ∈ K₀, ∀ η ∈ K₀, ξ ≠ η → kk ξ η = A (ξ, η, C.Θ η ξ)) :
    ∃ A₀ B₀ : ℝ, C.RestrictedKernelBounds K₀ kk A₀ B₀ := by
  obtain ⟨A₀, B₀, hA0, hB0, hsize, hdiff⟩ :=
    ((hasKernelBounds_of_wtSym hK₀ hK₀U hA).congr_of_ne hK₀U
      (κ₂ := kk) (fun ξ hξ η hη hne => (hkk ξ hξ η hη hne).symm))
  refine ⟨A₀, B₀, RestrictedKernelBounds.of_estimates hA0 hB0 ?_ hsize hdiff⟩
  refine measurable_sliceKernel_of_continuousOn hK₀.isClosed.measurableSet ?_
  have hc := continuousOn_symbolKernel (C := C) hK₀U ((hA ∅ isCompact_empty 1 one_pos).contDiffOn)
  refine hc.congr (fun p hp => ?_)
  exact hkk p.1 hp.1.1 p.2 hp.1.2 (fun h => hp.2 (Set.mem_diagonal_iff.mpr h))

end LiftedChart

end RothschildStein.P1
