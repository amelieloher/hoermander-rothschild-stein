-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderTransferTopology
public import RothschildStein.P2.NormTransfer

/-!
# The lifted oscillation bound

The lower fiber bound turns an integral over a base ball into an integral over a lifted ball
(BB p. 598, (11.88)-(11.89)): for `ξ` in a compact set of centres, `δ` and `c_f` the constants of the
fiber bounds `C.ball_bounds`, and `ξ`-centred lifted/base balls `Ũ_r = B̃(ξ, r)`, `V_r = B(π ξ, r)`,
`V_{δ r} = B(π ξ, δ r)`,
`c_f (|Ũ_r| / |V_r|) ∫_{V_{δ r}} |f - c| ≤ ∫_{Ũ_r} |f ∘ π - c|`, so that a pointwise bound
`|f ∘ π - c| ≤ M` on `Ũ_r` gives `∫_{V_{δ r}} |f - c| ≤ (M / c_f) |V_r|`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The lower fiber bound on `W` turns an integral over `W` into an integral over `A`:
`c_- ∫_W F ≤ ∫_A F ∘ π`. Only measurability of `F` on `W` is needed. -/
theorem le_lintegral_of_fiber_lower {A : Set (Fin (n + m) → ℝ)} {W : Set (Fin n → ℝ)} {clow : ℝ}
    (hA : MeasurableSet A) (hW : MeasurableSet W)
    (hlow : ∀ z ∈ W, ENNReal.ofReal clow ≤ fiberVolume A z)
    {F : (Fin n → ℝ) → ℝ≥0∞} (hF : AEMeasurable F (volume.restrict W)) :
    ENNReal.ofReal clow * ∫⁻ x in W, F x ≤ ∫⁻ ξ in A, F (basePoint ξ) := by
  have hFw : AEMeasurable (W.indicator F) volume := (aemeasurable_indicator_iff hW).2 hF
  calc ENNReal.ofReal clow * ∫⁻ x in W, F x
      = ∫⁻ x, ENNReal.ofReal clow * W.indicator F x := by
        rw [← lintegral_indicator hW, ← lintegral_const_mul'' _ hFw]
    _ ≤ ∫⁻ x, W.indicator F x * fiberVolume A x := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ W
        · simp only [indicator_of_mem hx]
          rw [mul_comm]
          exact mul_le_mul' le_rfl (hlow x hx)
        · simp [hx]
    _ = ∫⁻ ξ in A, W.indicator F (basePoint ξ) := (lintegral_comp_basePoint hA hFw).symm
    _ ≤ ∫⁻ ξ in A, F (basePoint ξ) := lintegral_mono fun ξ => indicator_le_self W F _

/-- The facts at a centre `ξ` of a compact `K₁ ⊆ U` and a radius
`r < r_*` used for H2's patch: lifted balls inside `U`, measurability, positivity, finiteness, lift
existence for the base points of `B(π ξ, δ r)`, and the lifted oscillation bound
`∫_{B(π ξ, δ r)} |f - c| ≤ (M / c_f) |B(π ξ, r)|` whenever `|f ∘ π - c| ≤ M` on `B̃(ξ, r)`. -/
def LiftedOscFacts (C : LiftedChart w s Ω hΩ X x₀ m) (K₁ : Set (Fin (n + m) → ℝ))
    (rstar δ cf : ℝ) : Prop :=
  ∀ ξ ∈ K₁, ∀ r : ℝ, 0 < r → r < rstar →
    rsBall C.O w C.Xl ξ r ⊆ C.U ∧
    MeasurableSet (rsBall Ω w X (basePoint ξ) (δ * r)) ∧
    MeasurableSet (rsBall Ω w X (basePoint ξ) r) ∧
    0 < (volume (rsBall Ω w X (basePoint ξ) r)).toReal ∧
    volume (rsBall Ω w X (basePoint ξ) r) ≠ ⊤ ∧
    (∀ x ∈ rsBall Ω w X (basePoint ξ) (δ * r),
      ∃ ζ ∈ rsBall C.O w C.Xl ξ r, basePoint ζ = x) ∧
    ∀ (f : (Fin n → ℝ) → ℝ) (c M : ℝ), 0 ≤ M →
      AEStronglyMeasurable f (volume.restrict (rsBall Ω w X (basePoint ξ) (δ * r))) →
      (∀ ζ ∈ rsBall C.O w C.Xl ξ r, |f (basePoint ζ) - c| ≤ M) →
      ∫ x in rsBall Ω w X (basePoint ξ) (δ * r), |f x - c| ≤
        M / cf * (volume (rsBall Ω w X (basePoint ξ) r)).toReal

/-- The lifted oscillation bound at every centre of a compact
`K₁ ⊆ U` and every radius `r < r_*` (lower fiber bound, BB p. 598). -/
theorem lifted_oscillation (C : LiftedChart w s Ω hΩ X x₀ m) {K₁ : Set (Fin (n + m) → ℝ)}
    (hK₁ : IsCompact K₁) (hK₁U : K₁ ⊆ C.U) :
    ∃ rstar δ cf : ℝ, 0 < rstar ∧ 0 < δ ∧ δ < 1 ∧ 0 < cf ∧ LiftedOscFacts C K₁ rstar δ cf := by
  obtain ⟨rstar, cv, Cv, δ, cf, Cf, hr, hcv, hCv, hδ0, hδ1, hcf, hCf, hall⟩ :=
    C.ball_bounds K₁ hK₁ hK₁U
  refine ⟨rstar, δ, cf, hr, hδ0, hδ1, hcf, fun ξ hξ r hr0 hrr => ?_⟩
  obtain ⟨hUlU, hUlm, hVbm, hUlfin, hVbfin, hUlpos, hVbpos, -, -, hdist, hup, hlow⟩ :=
    hall ξ hξ r hr0 hrr
  obtain ⟨-, -, hWm, -, -, -, -, -, -, -, -, -⟩ :=
    hall ξ hξ (δ * r) (mul_pos hδ0 hr0) (by nlinarith)
  have hcpos : 0 < cf * (volume (rsBall C.O w C.Xl ξ r)).toReal /
      (volume (rsBall Ω w X (basePoint ξ) r)).toReal := div_pos (mul_pos hcf hUlpos) hVbpos
  refine ⟨hUlU, hWm, hVbm, hVbpos, hVbfin, fun x hx => ?_, ?_⟩
  · have hpos : 0 < fiberVolume (rsBall C.O w C.Xl ξ r) x :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hcpos) (hlow x hx)
    have hne : volume {t : Fin m → ℝ | joinPoint x t ∈ rsBall C.O w C.Xl ξ r} ≠ 0 := hpos.ne'
    obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero hne
    exact ⟨joinPoint x t, ht, basePoint_joinPoint x t⟩
  · intro f c M hM hfm hbound
    set Ul := rsBall C.O w C.Xl ξ r with hUl
    set Vb := rsBall Ω w X (basePoint ξ) r with hVb
    set Vδ := rsBall Ω w X (basePoint ξ) (δ * r) with hVδ
    set A := (volume Ul).toReal with hA
    set B := (volume Vb).toReal with hB
    have hfc : AEStronglyMeasurable (fun x => f x - c) (volume.restrict Vδ) :=
      hfm.sub aestronglyMeasurable_const
    have hF : AEMeasurable (fun x => ENNReal.ofReal |f x - c|) (volume.restrict Vδ) := by
      have := hfc.norm.aemeasurable
      simpa only [Real.norm_eq_abs] using this.ennreal_ofReal
    have h1 := le_lintegral_of_fiber_lower hUlm hWm hlow hF
    have h2 : ∫⁻ ζ in Ul, ENNReal.ofReal |f (basePoint ζ) - c| ≤
        ENNReal.ofReal M * volume Ul := by
      calc ∫⁻ ζ in Ul, ENNReal.ofReal |f (basePoint ζ) - c|
          ≤ ∫⁻ ζ in Ul, ENNReal.ofReal M :=
            setLIntegral_mono' hUlm (fun ζ hζ => ENNReal.ofReal_le_ofReal (hbound ζ hζ))
        _ = ENNReal.ofReal M * volume Ul := setLIntegral_const _ _
    have hUlA : volume Ul = ENNReal.ofReal A := (ENNReal.ofReal_toReal hUlfin).symm
    set I := ∫⁻ x in Vδ, ENNReal.ofReal |f x - c| with hI
    have hIfin : I ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.mul_top (by simpa using hcpos)] at h1
      have : ENNReal.ofReal M * volume Ul < ⊤ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUlfin.lt_top
      exact absurd (top_le_iff.mp (h1.trans h2)) this.ne
    have h3 : ENNReal.ofReal (cf * A / B) * I ≤ ENNReal.ofReal (M * A) := by
      refine h1.trans (h2.trans (le_of_eq ?_))
      rw [hUlA, ← ENNReal.ofReal_mul hM]
    rw [← ENNReal.ofReal_toReal hIfin, ← ENNReal.ofReal_mul hcpos.le,
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM ENNReal.toReal_nonneg)] at h3
    have hint : ∫ x in Vδ, |f x - c| = I.toReal := by
      rw [hI]
      refine integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => abs_nonneg _) ?_
      have := hfc.norm
      simpa only [Real.norm_eq_abs] using this
    have h3' : cf * (A / B) * I.toReal ≤ M * A := by
      have := h3
      rwa [mul_div_assoc] at this
    have h4 : I.toReal * cf ≤ M * B := by
      have hAB : 0 < A / B := div_pos hUlpos hVbpos
      have : (I.toReal * cf) * (A / B) ≤ (M * B) * (A / B) := by
        calc (I.toReal * cf) * (A / B) = cf * (A / B) * I.toReal := by ring
          _ ≤ M * A := h3'
          _ = (M * B) * (A / B) := by field_simp
      exact le_of_mul_le_mul_right this hAB
    rw [hint, div_mul_eq_mul_div, le_div_iff₀ hcf]
    exact h4

end RothschildStein.P2
