-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.AnnularKernelBounds
public import RothschildStein.H2.PrincipalValueLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2

/-- The two endpoint corrections converting metric shells into
open d'-shells, including the endpoint correction in BB p. 303. -/
def cancellationBoundaryConstant (C θ₁ θ₂ : ℝ) : ℝ :=
  C * (4 * θ₂ / (3 * θ₁)) ^ Real.logb 2 C + C ^ 2

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The far cancellation term A₁₂, including both endpoint errors.
BB p. 303 uses a metric shell where its hypothesis concerns d'-shells. -/
theorem SupportedKernel.far_cancellation_bound {D : LocDoubling X} {E G : Set X}
    {β A S R C_K : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β 0 A S R K)
    (d : TruncDist D) (hCan : ShellCancellation D.μ E G d.d' K C_K)
    {x₀ x : X} (_hx₀ : x₀ ∈ E) (hx : x ∈ E) (hxx : x₀ ≠ x)
    (hκ : dist x₀ x < D.κ / 3) :
    IntegrableOn (fun y => K x y) (G ∩ {y | 2 * dist x₀ x < dist x₀ y}) D.μ ∧
      |∫ y in G ∩ {y | 2 * dist x₀ x < dist x₀ y}, K x y ∂D.μ| ≤
        C_K + cancellationBoundaryConstant D.C_D d.θ₁ d.θ₂ * A := by
  classical
  let t := dist x₀ x
  have ht : 0 < t := dist_pos.mpr hxx
  have hθ₁ := d.θ₁_pos
  have hθ : 0 < d.θ₂ := d.θ₁_pos.trans_le d.θ₁_le
  let F : Set X := {y | 2 * t < dist x₀ y}
  let J : Set X := {y | 3 * t < dist x y}
  let T : Set X := {y | 3 * d.θ₁ * t < d.d' x y ∧ d.d' x y < d.θ₂ * R}
  let E₁ := F \ J
  let E₂ := T \ J
  have hm : Measurable (d.d' x) := d.meas.comp (measurable_const.prodMk measurable_id)
  have hF : MeasurableSet F := measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  have hJ : MeasurableSet J := measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  have hT : MeasurableSet T := (measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const)
  have h₄ : 4 * t ≤ 6 * D.κ := by dsimp [t]; linarith [D.κ_pos]
  have hCD : 0 ≤ D.C_D := by linarith [D.one_lt_C_D]
  have hE₁ := hK.kernel.annular_indicator_bound (hK.sub_EG hx) (hK.sub_G (hK.sub_EG hx)) (hF.diff hJ)
    (a := t) (b := 4 * t) ht h₄ (by
      intro y hy
      have hyF : 2 * t < dist x₀ y := hy.2.1
      have hyJ : ¬3 * t < dist x y := hy.2.2
      have htri := dist_triangle x₀ x y
      change t + dist x y ≥ dist x₀ y at htri
      exact ⟨by linarith, by linarith⟩) (C := D.C_D ^ 2) (sq_nonneg _) (by
      have he := D.outerPatch.shell_integral_pow (hK.sub_G (hK.sub_EG hx)) ht
        (b := 4 * t) (by linarith) h₄ 2 (by norm_num)
      change (∫⁻ y in {y | t ≤ dist x y ∧ dist x y < 4 * t}, (volumeAt D.μ x y)⁻¹ ∂D.μ) ≤ ENNReal.ofReal D.C_D ^ 2 at he
      simpa only [ENNReal.ofReal_pow hCD] using he)
  let a := 3 * d.θ₁ * t / d.θ₂
  have ha : 0 < a := div_pos (by positivity) hθ
  have ha₃ : a ≤ 3 * t := (div_le_iff₀ hθ).mpr (by nlinarith [d.θ₁_le])
  have hE₂ := hK.kernel.annular_indicator_bound (hK.sub_EG hx) (hK.sub_G (hK.sub_EG hx)) (hT.diff hJ)
    (a := a) (b := 4 * t) ha h₄ (by
      intro y hy
      have hyT : 3 * d.θ₁ * t < d.d' x y := hy.2.1.1
      have hyJ : ¬3 * t < dist x y := hy.2.2
      have hd := (d.comp x (hK.sub_G (hK.sub_EG hx)) y (hK.sub_G hy.1)).2
      refine ⟨?_, by linarith⟩
      apply (div_le_iff₀ hθ).mpr
      nlinarith) (C := D.C_D * (4 * d.θ₂ / (3 * d.θ₁)) ^ Real.logb 2 D.C_D)
    (mul_nonneg hCD (Real.rpow_nonneg (by positivity) _)) (by
      have he := D.outerPatch.shell_integral_rpow (hK.sub_G (hK.sub_EG hx)) ha (b := 4 * t)
        (by linarith) h₄
      have heq : 4 * t / a = 4 * d.θ₂ / (3 * d.θ₁) := by dsimp [a]; field_simp
      change (∫⁻ y in {y | a ≤ dist x y ∧ dist x y < 4 * t}, (volumeAt D.μ x y)⁻¹ ∂D.μ) ≤ ENNReal.ofReal (D.C_D * (4 * t / a) ^ Real.logb 2 D.C_D) at he
      simpa only [heq] using he)
  have hpos : 0 < 3 * d.θ₁ * t := by positivity
  have hk' := (hK.truncated_absolute d hpos (f := fun _ => 1) aestronglyMeasurable_const
    (M := 1) (by norm_num) (ae_of_all _ (by intro y; norm_num)) hx).1
  have hiT : IntegrableOn (T.indicator (K x)) G D.μ := by
    apply (integrableOn_indicator_iff hT).mpr
    simpa only [mul_one] using hk'.mono_set (show T ∩ G ⊆ G ∩ {y | 3 * d.θ₁ * t < d.d' x y} from fun y hy => ⟨hy.2, hy.1.1⟩)
  have hid : ∀ y ∈ G, F.indicator (K x) y = T.indicator (K x) y + E₁.indicator (K x) y - E₂.indicator (K x) y := by
    intro y hy
    have htri := dist_triangle x₀ x y
    change dist x₀ y ≤ t + dist x y at htri
    have htri' := dist_triangle x x₀ y
    rw [dist_comm x x₀] at htri'
    by_cases hyJ : y ∈ J
    · have hyF : y ∈ F := by have hd : 3 * t < dist x y := hyJ; change 2 * t < dist x₀ y; linarith
      by_cases hyT : y ∈ T
      · simp [E₁, E₂, hyF, hyJ, hyT]
      · have hk : K x y = 0 := by
          by_cases hyR : R ≤ dist x y
          · exact hK.support x hx y hy hyR
          · have hc := d.comp x (hK.sub_G (hK.sub_EG hx)) y (hK.sub_G hy)
            have hd : 3 * t < dist x y := hyJ
            have he : y ∈ T := by
              change 3 * d.θ₁ * t < d.d' x y ∧ d.d' x y < d.θ₂ * R
              constructor <;> nlinarith [d.θ₁_pos, hθ]
            exact False.elim (hyT he)
        simp [E₁, E₂, hyF, hyJ, hyT, hk]
    · by_cases hyF : y ∈ F <;> by_cases hyT : y ∈ T <;> simp [E₁, E₂, hyF, hyJ, hyT]
  have hisum : IntegrableOn (fun y => T.indicator (K x) y + E₁.indicator (K x) y - E₂.indicator (K x) y) G D.μ :=
    (hiT.add hE₁.1).sub hE₂.1
  have heq : (∫ y in G, F.indicator (K x) y ∂D.μ) =
      (∫ y in G, T.indicator (K x) y ∂D.μ) + (∫ y in G, E₁.indicator (K x) y ∂D.μ) -
        ∫ y in G, E₂.indicator (K x) y ∂D.μ := by
    rw [setIntegral_congr_fun hK.kernel.measurable_E hid]
    have hip : IntegrableOn (fun y => T.indicator (K x) y + E₁.indicator (K x) y) G D.μ := hiT.add hE₁.1
    have hie₁ : IntegrableOn (fun y => E₁.indicator (K x) y) G D.μ := hE₁.1
    have hie₂ : IntegrableOn (fun y => E₂.indicator (K x) y) G D.μ := hE₂.1
    have hit : IntegrableOn (fun y => T.indicator (K x) y) G D.μ := hiT
    rw [integral_sub hip hie₂, integral_add hit hie₁]
  have hboundT : |∫ y in G, T.indicator (K x) y ∂D.μ| ≤ C_K := by
    rw [setIntegral_indicator hT]
    by_cases hlt : 3 * d.θ₁ * t < d.θ₂ * R
    · exact hCan.2 x hx _ _ hpos hlt
    · have hz : T = ∅ := by
        ext y
        simp only [T, mem_ofPred_eq, mem_empty_iff_false]
        constructor
        · intro hy
          linarith [hy.1, hy.2]
        · intro hy
          exact False.elim hy
      rw [hz, inter_empty, setIntegral_empty, abs_zero]
      exact hCan.1
  have hiF : IntegrableOn (F.indicator (K x)) G D.μ := hisum.congr (by
    filter_upwards [ae_restrict_mem hK.kernel.measurable_E] with y hy
    exact (hid y hy).symm)
  refine ⟨by simpa only [inter_comm] using (integrableOn_indicator_iff hF).mp hiF, ?_⟩
  have hb₁ := abs_sub ((∫ y in G, T.indicator (K x) y ∂D.μ) + ∫ y in G, E₁.indicator (K x) y ∂D.μ)
    (∫ y in G, E₂.indicator (K x) y ∂D.μ)
  have hb₂ := abs_add_le (∫ y in G, T.indicator (K x) y ∂D.μ) (∫ y in G, E₁.indicator (K x) y ∂D.μ)
  rw [← setIntegral_indicator hF, heq]
  unfold cancellationBoundaryConstant
  nlinarith [hE₁.2, hE₂.2]

end RothschildStein.H2
