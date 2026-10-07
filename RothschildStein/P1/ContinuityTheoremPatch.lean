-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityTheoremBounds

/-!
# Continuity: absolutely integrable kernels have principal-value bounds

A patch kernel `κ` (kernel bounds of exponent one on the compact patch `S ⊆ U`, supported in `V × V`
off the diagonal) acts by the absolutely convergent integral `f ↦ ∫ κ(ξ, η) f(η) dη` on every
function of finite Hölder norm (`f` is continuous and bounded on `V`). Its `ρ`-principal value exists
at every point and equals this integral (`hasRhoPV_of_patchKernel`), so the Schur bound and the
`C^α → C^α` bound proved for patch kernels (`PatchKernel.exists_lp_bound`,
`PatchKernel.exists_holderENorm_bound_of_holderENorm`) are principal-value bounds
(`PVBounds.of_patchKernel`). This covers the positive-type terms of a type decomposition and the
regular remainder (BB pp. 566–576, Thm 11.29).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section HolderBound

variable {n' : ℕ} {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ} {V : Set (Fin n' → ℝ)}

/-- A function of finite Hölder norm is bounded on `V` by that norm. -/
theorem abs_le_toReal_holderENorm {f : (Fin n' → ℝ) → ℝ} (hf : holderENorm d α V f ≠ ⊤)
    {y : Fin n' → ℝ} (hy : y ∈ V) : |f y| ≤ (holderENorm d α V f).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hf).mp
    (le_trans (le_iSup (fun x : V => ENNReal.ofReal |f x|) ⟨y, hy⟩) le_self_add)

end HolderBound

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {ν : (Fin (n + m) → ℝ) → ℝ}
  {S V : Set (Fin (n + m) → ℝ)} {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}

/-- **The principal value of a patch kernel is the absolutely convergent integral**, at every
point `ξ` (also outside the chart domain, where both sides vanish), for `f` bounded and measurable
on `V`. -/
theorem hasRhoPV_of_patchKernel (hν : C.G.IsHomogeneousGauge ν) (h : C.PatchKernel S V κ)
    {f : (Fin (n + m) → ℝ) → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V)) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ y ∈ V, |f y| ≤ M) (ξ : Fin (n + m) → ℝ) :
    HasRhoPV (C.rhoGauge ν) κ f ξ (∫ η, κ ξ η * f η) := by
  by_cases hξ : ξ ∈ C.U
  · refine hasRhoPV_of_integrable hν hξ (fun η hη => ?_) (h.integrable_row hf hM0 hM ξ)
    have hηV : η ∉ V := fun hv => hη (h.subset_U (h.subset hv))
    have hne : ξ ≠ η := fun he => hη (he ▸ hξ)
    rw [h.support ξ η hne (Or.inr hηV), zero_mul]
  · have hξV : ξ ∉ V := fun hv => hξ (h.subset_U (h.subset hv))
    have hae : ∀ᵐ η ∂(volume : Measure (Fin (n + m) → ℝ)), (fun _ _ => (0 : ℝ)) ξ η = κ ξ η := by
      filter_upwards [C.ae_ne ξ] with η hη
      exact (h.support ξ η hη.symm (Or.inl hξV)).symm
    rw [h.integral_eq_zero_of_not_mem f hξV]
    exact hasRhoPV_zero.congr_ae hae

/-- **Patch kernels have principal-value bounds** (Schur `L^p` bound and `C^α → C^α` bound of
the regular part and of the positive homogeneous part, read for the principal value, which exists
at every point and is the absolutely convergent integral). -/
theorem PVBounds.of_patchKernel (hν : C.G.IsHomogeneousGauge ν) (h : C.PatchKernel S V κ) :
    C.PVBounds ν V κ := by
  have hpv : ∀ {α : ℝ}, 0 < α → ∀ f : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α V f ≠ ⊤ →
      (∀ ξ, HasRhoPV (C.rhoGauge ν) κ f ξ (∫ η, κ ξ η * f η)) ∧
        AEStronglyMeasurable f (volume.restrict V) := by
    intro α hα0 f hf
    have hfm : AEStronglyMeasurable f (volume.restrict V) :=
      aestronglyMeasurable_of_holderENorm_lt_top (fun y hy => h.subset_U (h.subset hy))
        h.measurableSet hα0 (lt_top_iff_ne_top.mpr hf)
    exact ⟨fun ξ => hasRhoPV_of_patchKernel hν h hfm ENNReal.toReal_nonneg
      (fun y hy => abs_le_toReal_holderENorm hf hy) ξ, hfm⟩
  refine ⟨fun {α} hα0 hα1 => ?_, fun {p} hp {α} hα0 hα1 => ?_⟩
  · obtain ⟨CH, hCH, hb⟩ := h.exists_holderENorm_bound_of_holderENorm hα0 hα1
    refine ⟨CH, hCH, fun f hf => ?_⟩
    have heq : rhoPV (C.rhoGauge ν) κ f = fun ξ => ∫ η, κ ξ η * f η :=
      funext fun ξ => ((hpv hα0 f hf).1 ξ).rhoPV_eq
    rw [heq]
    refine ⟨fun ξ => ?_, hb f⟩
    have := (hpv hα0 f hf).1 ξ
    exact this
  · obtain ⟨Λ, hΛ, hb⟩ := h.exists_lp_bound
    refine ⟨Λ, hΛ, fun f hf hfm => ?_⟩
    have heq : rhoPV (C.rhoGauge ν) κ f = fun ξ => ∫ η, κ ξ η * f η :=
      funext fun ξ => ((hpv hα0 f hf).1 ξ).rhoPV_eq
    rw [heq]
    exact hb (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr hp.le) ENNReal.ofReal_ne_top f
      (memLp_of_holderENorm_ne_top h.measurableSet
        (lt_of_le_of_lt (measure_mono h.subset) h.isCompact.measure_lt_top) hf hfm _)

end LiftedChart

end RothschildStein.P1
