-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Scale.Duality
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.HahnBanach

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap TemperedDistribution
open scoped FourierTransform BesselPotentialSpace ComplexConjugate
namespace Hormander.A

/-- Auxiliary: `L ∘ J_s`. -/
def JLp {N : ℕ} (s : ℝ) : 𝓢(Carrier N, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure (Carrier N)) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Carrier N))) ∘L Jschw s

theorem JLp_injective {N : ℕ} (s : ℝ) : Function.Injective (JLp (N := N) s) := by
  intro φ ψ h
  have h1 : Jschw s φ = Jschw s ψ :=
    SchwartzMap.injective_toLp 2 (volume : Measure (Carrier N)) h
  exact (Jschw_bijective s).1 h1

theorem exists_L2_representer {N : ℕ} (s : ℝ) (u : 𝓢'(Carrier N, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : 𝓢(Carrier N, ℂ), ‖u φ‖ ≤ C * ‖schwartzToSobolev s φ‖) :
    ∃ q : Lp ℂ 2 (volume : Measure (Carrier N)), ‖q‖ ≤ C ∧
      ∀ φ : 𝓢(Carrier N, ℂ), u φ = ∫ ξ, q ξ * Jschw s φ ξ := by
  let L : 𝓢(Carrier N, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (Carrier N)) := (JLp s).toLinearMap
  let e : 𝓢(Carrier N, ℂ) ≃ₗ[ℂ] LinearMap.range L :=
    LinearEquiv.ofInjective L (JLp_injective s)
  let uℓ : 𝓢(Carrier N, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => u φ
      map_add' := fun a b => map_add u a b
      map_smul' := fun c a => map_smul u c a }
  have hnorm : ∀ φ, ‖L φ‖ = ‖schwartzToSobolev s φ‖ := fun φ =>
    (weighted_fourier_density s).2.1 φ
  let f0 : LinearMap.range L →ₗ[ℂ] ℂ := uℓ ∘ₗ e.symm.toLinearMap
  have hbd : ∀ x : LinearMap.range L, ‖f0 x‖ ≤ C * ‖x‖ := by
    intro x
    obtain ⟨φ, hφ⟩ : ∃ φ, e φ = x := e.surjective x
    have : f0 x = u φ := by simp [f0, uℓ, ← hφ]
    rw [this, ← hφ]
    have : ‖(e φ : LinearMap.range L)‖ = ‖L φ‖ := rfl
    rw [this, hnorm]
    exact h φ
  let f : LinearMap.range L →L[ℂ] ℂ := f0.mkContinuous C hbd
  obtain ⟨g, hg1, hg2⟩ := exists_extension_norm_eq (LinearMap.range L) f
  have hgC : ‖g‖ ≤ C := by
    rw [hg2]; exact LinearMap.mkContinuous_norm_le _ hC _
  let g' := (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure (Carrier N)))).symm g
  refine ⟨star g', ?_, ?_⟩
  · rw [norm_star_lp2]
    simpa [g'] using hgC
  · intro φ
    have h1 : g (L φ) = u φ := by
      have := hg1 ⟨L φ, LinearMap.mem_range_self L φ⟩
      rw [this]
      have hsymm : e.symm ⟨L φ, LinearMap.mem_range_self L φ⟩ = φ :=
        (LinearEquiv.symm_apply_eq e).mpr (Subtype.ext rfl)
      simp only [f, LinearMap.mkContinuous_apply, f0, LinearMap.comp_apply]
      change uℓ (e.symm ⟨L φ, LinearMap.mem_range_self L φ⟩) = u φ
      rw [hsymm]
      rfl
    have h2 : g (L φ) = inner ℂ g' (L φ) := by
      have := InnerProductSpace.toDual_apply_apply (𝕜 := ℂ) (x := g') (y := L φ)
      have h3 : (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure (Carrier N)))) g' = g :=
        LinearIsometryEquiv.apply_symm_apply _ g
      rw [h3] at this
      exact this
    have h4 := integral_mul_eq_inner_star (star g') (L φ)
    rw [star_star] at h4
    rw [← h1, h2, ← h4]
    apply integral_congr_ae
    filter_upwards [(Jschw s φ).coeFn_toLp 2 (volume : Measure (Carrier N))] with x hx
    have : (L φ) x = Jschw s φ x := hx
    rw [this]

/-- If the Schwartz-test pairing of a tempered distribution `u` is bounded by
`C ‖φ‖_{H^s}`, then `u ∈ H^{-s}` with `‖u‖_{H^{-s}} ≤ C`. -/
theorem riesz_converse {N : ℕ} (s : ℝ) (u : 𝓢'(Carrier N, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : 𝓢(Carrier N, ℂ), ‖u φ‖ ≤ C * ‖schwartzToSobolev s φ‖) :
    ∃ v : SobolevSpace N (-s), v.toDistr = u ∧ ‖v‖ ≤ C := by
  obtain ⟨q, hq, hrep⟩ := exists_L2_representer s u hC h
  set uhat : 𝓢'(Carrier N, ℂ) := TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) s)
    (q : 𝓢'(Carrier N, ℂ)) with huhat
  have hu : u = 𝓕⁻ uhat := by
    ext φ
    rw [hrep φ]
    change _ = uhat (𝓕⁻ φ)
    rw [huhat, TemperedDistribution.smulLeftCLM_apply_apply, ← Jschw_eq_smulLeft,
      Lp.toTemperedDistribution_apply]
    simp [smul_eq_mul, mul_comm]
  have hfu : 𝓕 u = uhat := by
    rw [hu]; exact (tempered_fourier_inversion uhat).2
  have hq' : TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) (-s)) (𝓕 u) =
      (q : 𝓢'(Carrier N, ℂ)) := by
    rw [hfu, huhat, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
      (besselSymbol_hasTemperateGrowth _) (besselSymbol_hasTemperateGrowth _)]
    have : (besselSymbol (N := N) s * besselSymbol (N := N) (-s)) = fun _ => (1 : ℂ) := by
      ext ξ
      have := besselSymbol_neg_mul (N := N) s ξ
      have hst : star (besselSymbol (N := N) s ξ) = besselSymbol (N := N) s ξ := by
        simp [besselSymbol]
      rw [hst] at this
      simpa [mul_comm] using this
    rw [this, TemperedDistribution.smulLeftCLM_const, one_smul]
  have hbessel : TemperedDistribution.besselPotential (Carrier N) ℂ (-s) u =
      ((𝓕⁻ q : Lp ℂ 2 (volume : Measure (Carrier N))) : 𝓢'(Carrier N, ℂ)) := by
    rw [TemperedDistribution.besselPotential, TemperedDistribution.fourierMultiplierCLM_apply]
    change 𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) (-s)) (𝓕 u)) = _
    rw [hq', Lp.fourierInv_toTemperedDistribution_eq]
  have hmem : TemperedDistribution.MemSobolev (-s) 2 u := ⟨𝓕⁻ q, hbessel⟩
  refine ⟨hmem.toBesselPotentialSpace, hmem.toBesselPotentialSpace_toDistr, ?_⟩
  have hLp : hmem.toBesselPotentialSpace.toLp = (𝓕⁻ q : Lp ℂ 2 (volume : Measure (Carrier N))) := by
    apply (LinearMap.ker_eq_bot.mp
      (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
        (μ := (volume : Measure (Carrier N))) (p := 2)))
    show Lp.toTemperedDistribution _ = Lp.toTemperedDistribution _
    rw [← hmem.toBesselPotentialSpace.bessel_toDistr_eq_toLp, hmem.toBesselPotentialSpace_toDistr,
      hbessel]
  rw [← BesselPotentialSpace.norm_toLp_eq, hLp]
  exact (((Lp.fourierTransformₗᵢ (Carrier N) ℂ).symm.norm_map q).trans_le hq)

end Hormander.A
