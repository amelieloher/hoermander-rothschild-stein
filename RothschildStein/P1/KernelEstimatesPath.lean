-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesBounds
public import RothschildStein.G1.ControlledVariation

/-!
# Path margins for kernel estimates

The geometric part of the difference estimate: a controlled curve of small parameter starting in
a compact `K₀ ⊆ U` stays in a fixed compact neighborhood `cthickening ε K₀ ⊆ U` of `K₀`
(path margin, [GAP-FILL] of BB p. 570), and subcurves of a controlled curve have control distance
at most the parameter of the curve.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric
open scoped BigOperators ENNReal
namespace RothschildStein.P1

/-- A subcurve of a controlled curve (any weights) has control distance at most the
parameter of the curve: the affine time change has factor at most one, and `s * δ^w ≤ δ^w`. -/
theorem controlDistance_subcurve_le_param {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {δ : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    controlDistance Ω w X (γ a) (γ b) ≤ ENNReal.ofReal δ := by
  rcases eq_or_lt_of_le hab with h | h
  · subst b
    rw [RothschildStein.G1.controlDistance_self w X (hγ.2.2.1 ⟨ha, hb⟩)]
    exact bot_le
  · have hd : 0 < b - a := sub_pos.mpr h
    have hcurve := RothschildStein.G1.isControlledCurve_comp_affine hγ hγ.1 (ne_of_gt hd)
      (c := a) (d := b - a)
      (fun t ht => by constructor <;> dsimp <;> nlinarith [ht.1, ht.2])
      (fun i => by
        rw [abs_of_pos hd]
        exact mul_le_of_le_one_left (pow_nonneg hγ.1.le _) (by linarith))
    simpa only [mul_zero, add_zero, mul_one, add_sub_cancel] using
      RothschildStein.G1.controlDistance_le_of_curve hcurve

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- Path margin: a compact neighborhood `cthickening ε K₀ ⊆ U` of `K₀` and a radius `r₁`
such that every controlled curve of parameter `< r₁` starting in `K₀` stays in the neighborhood
(BB p. 570, [GAP-FILL: path margins]). -/
theorem exists_path_margin {K₀ : Set (Fin (n + m) → ℝ)} (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U) :
    ∃ ε : ℝ, 0 < ε ∧ cthickening ε K₀ ⊆ C.U ∧ ∃ r₁ : ℝ, 0 < r₁ ∧
      ∀ ξ ∈ K₀, ∀ δ : ℝ, δ < r₁ → ∀ γ : ℝ → (Fin (n + m) → ℝ),
        isControlledCurve C.O w C.Xl δ γ → γ 0 = ξ → ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ cthickening ε K₀ := by
  obtain ⟨ε, hε, hεU⟩ := hK₀.exists_cthickening_subset_open C.isOpen_U hK₀U
  refine ⟨ε, hε, hεU, ?_⟩
  have hK₁ : IsCompact (cthickening ε K₀) := hK₀.cthickening
  set Z : Set (Fin (n + m) → ℝ) := cthickening ε K₀ ∩ {c | ε ≤ infDist c K₀} with hZ
  have hZc : IsCompact Z :=
    hK₁.inter_right (isClosed_le continuous_const (continuous_infDist_pt K₀))
  have hZU : Z ⊆ C.U := fun c hc => hεU hc.1
  -- positivity of the gauge between `K₀` and `Z`
  have hpos : ∀ ξ ∈ K₀, ∀ c ∈ Z, 0 < kgauge C.G (C.Θ ξ c) := by
    intro ξ hξ c hc
    have hne : c ≠ ξ := by
      rintro rfl
      have h1 : ε ≤ infDist c K₀ := hc.2
      rw [infDist_zero_of_mem hξ] at h1
      linarith
    exact kgauge_pos C.G ((C.theta_eq_zero_iff (hK₀U hξ) (hZU hc)).not.mpr hne)
  obtain ⟨m₀, hm₀, hm₀le⟩ : ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ ξ ∈ K₀, ∀ c ∈ Z, m₀ ≤ kgauge C.G (C.Θ ξ c) := by
    by_cases hne : (K₀ ×ˢ Z).Nonempty
    · have hcont : ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
          kgauge C.G (C.Θ p.1 p.2)) (K₀ ×ˢ Z) :=
        (G2.continuous_gauge C.G).comp_continuousOn
          (C.theta_continuousOn.mono (Set.prod_mono hK₀U hZU))
      obtain ⟨p, hp, hmin⟩ := (hK₀.prod hZc).exists_isMinOn hne hcont
      exact ⟨kgauge C.G (C.Θ p.1 p.2), hpos p.1 hp.1 p.2 hp.2,
        fun ξ hξ c hc => hmin (show (ξ, c) ∈ K₀ ×ˢ Z from ⟨hξ, hc⟩)⟩
    · refine ⟨1, one_pos, fun ξ hξ c hc => ?_⟩
      exact absurd ⟨(ξ, c), hξ, hc⟩ hne
  refine ⟨m₀ / C.gaugeConst, div_pos hm₀ C.gaugeConst_pos, ?_⟩
  intro ξ hξ δ hδ γ hγ hγ0 t₁ ht₁
  by_contra hout
  have hcont : ContinuousOn γ (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hγ.2.1.continuousOn
  have hf : ContinuousOn (fun t => infDist (γ t) K₀) (Icc (0 : ℝ) t₁) :=
    (continuous_infDist_pt K₀).comp_continuousOn (hcont.mono (Icc_subset_Icc le_rfl ht₁.2))
  have hgt : ε < infDist (γ t₁) K₀ := by
    by_contra hle
    apply hout
    obtain ⟨y, hy, hyd⟩ := hK₀.exists_infDist_eq_dist ⟨ξ, hξ⟩ (γ t₁)
    exact mem_cthickening_of_dist_le (γ t₁) y ε K₀ hy (by rw [← hyd]; exact not_lt.mp hle)
  have h0 : infDist (γ 0) K₀ = 0 := by rw [hγ0]; exact infDist_zero_of_mem hξ
  obtain ⟨t₀, ht₀, hft₀⟩ := intermediate_value_Icc ht₁.1 hf
    (show ε ∈ Icc (infDist (γ 0) K₀) (infDist (γ t₁) K₀) from ⟨by rw [h0]; exact hε.le, hgt.le⟩)
  have ht₀' : t₀ ∈ Icc (0 : ℝ) 1 := ⟨ht₀.1, ht₀.2.trans ht₁.2⟩
  have hcZ : γ t₀ ∈ Z := by
    have hft : infDist (γ t₀) K₀ = ε := hft₀
    refine ⟨?_, show ε ≤ infDist (γ t₀) K₀ from hft.ge⟩
    obtain ⟨y, hy, hyd⟩ := hK₀.exists_infDist_eq_dist ⟨ξ, hξ⟩ (γ t₀)
    exact mem_cthickening_of_dist_le (γ t₀) y ε K₀ hy (by rw [← hyd]; exact hft.le)
  have hdl : C.dl ξ (γ t₀) ≤ ENNReal.ofReal δ := by
    have := controlDistance_subcurve_le_param hγ le_rfl ht₀.1 ht₀'.2
    rwa [hγ0] at this
  have h1 : (C.dl ξ (γ t₀)).toReal ≤ δ := ENNReal.toReal_le_of_le_ofReal
    (by have := hγ.1; exact this.le) hdl
  have h2 := C.gauge_div_le_dl_toReal (hK₀U hξ) (hZU hcZ)
  have h3 : m₀ / C.gaugeConst ≤ kgauge C.G (C.Θ ξ (γ t₀)) / C.gaugeConst :=
    div_le_div_of_nonneg_right (hm₀le ξ hξ _ hcZ) C.gaugeConst_pos.le
  linarith

end LiftedChart
end RothschildStein.P1
