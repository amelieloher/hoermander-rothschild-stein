-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderLocalMatrixBounds
public import HeatKernel.Moser.HolderLocalRepresentativeGluing
public import HeatKernel.Moser.HolderUniformOscillation
import Mathlib.Tactic

/-! # Uniform parabolic Hölder continuity for matrix weak solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter RothschildStein Metric
open scoped BigOperators Topology ENNReal NNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Measurable uniformly elliptic symmetric matrix equations have a uniform
parabolic Hölder exponent. One continuous representative is chosen before any
essential bounds or pairs of points, including on cylinders touching the top. -/
theorem exists_uniform_matrix_parabolic_holder
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (lam Λ : ℝ) (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    let X := G.horizontalFields hq
    let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
      fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
    let d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ :=
      fun x y => (horizontalL2Distance X x y).toReal
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ,
        (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)) →
        (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
          (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧
          ∀ ξ : Fin q → ℝ,
            lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ∧
            ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ≤ Λ * ∑ i, ξ i ^ 2) →
      ∀ (x₀ : Fin N → ℝ) (r t₀ : ℝ), 0 < r →
      ∀ u : ℝ → (Fin N → ℝ) → ℝ,
        IsLocalWeakSolution G hq hqpos hw hspan a ⟨Ioo (t₀ - 4 * r ^ 2) t₀, isOpen_Ioo⟩
          ⟨interior (B x₀ (2 * r)), isOpen_interior⟩ u →
        ∃ v : ℝ → (Fin N → ℝ) → ℝ,
          (∀ᵐ z ∂(volume.restrict (Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r)), v z.1 z.2 = u z.1 z.2) ∧
          ContinuousOn (fun z : ℝ × (Fin N → ℝ) => v z.1 z.2) (Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r) ∧
          ∀ m M : ℝ,
            (∀ᵐ z ∂(volume.restrict (Ioo (t₀ - 4 * r ^ 2) t₀ ×ˢ B x₀ (2 * r))),
              m ≤ u z.1 z.2 ∧ u z.1 z.2 ≤ M) →
            ∀ z ∈ Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r, ∀ w ∈ Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r,
              |v z.1 z.2 - v w.1 w.2| ≤
                C * ((d z.2 w.2 + Real.sqrt |z.1 - w.1|) / r) ^ α * (M - m) := by
  intro X B d
  have hB (x : Fin N → ℝ) (ρ : ℝ) :
      B x ρ = horizontalBall (G.horizontalFields hq) x ρ := rfl
  let E := CarnotPoint G hq hqpos hspan
  let : SecondCountableTopology E :=
    (CarnotPoint.coordinateHomeomorph G hq hqpos hspan).secondCountableTopology
  let : Nonempty E := ⟨fun _ => 0⟩
  obtain ⟨c, hc⟩ := exists_dense_seq E
  obtain ⟨θ, hθ, hcontraction⟩ := exists_uniform_matrix_oscillation_decay
    G hq hqpos hspan hw lam Λ hlam (hlam.le.trans hlamΛ)
  obtain ⟨α, hα, hθα⟩ := exists_dyadic_holder_exponent hθ
  refine ⟨α, (1024 / 15 : ℝ) ^ α, hα.1, hα.2, by positivity, ?_⟩
  intro coeff hcoeff hquad x₀ r top hr u hu
  have hUeq : (⟨interior (B x₀ (2 * r)), isOpen_interior⟩ : Opens (Fin N → ℝ)) =
      ⟨horizontalBall (G.horizontalFields hq) x₀ (2 * r),
        isOpen_horizontalBall G hq hqpos hspan x₀ (2 * r)⟩ := by
    apply Opens.ext
    exact (isOpen_horizontalBall G hq hqpos hspan x₀ (2 * r)).interior_eq
  rw [hUeq] at hu
  have hu' : IsLocalWeakSolution G hq hqpos hw hspan coeff
      ⟨Ioo (top - (2 * r) ^ 2) top, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) x₀ (2 * r),
        isOpen_horizontalBall G hq hqpos hspan x₀ (2 * r)⟩ u := by
    simpa only [show (2 * r) ^ 2 = 4 * r ^ 2 by ring] using hu
  let μ := CarnotPoint.spaceTimeVolume G hq hqpos hspan
  let : μ.IsOpenPosMeasure := inferInstanceAs
    ((volume : Measure (ℝ × (Fin N → ℝ))).IsOpenPosMeasure)
  let Ω : Set (ℝ × E) := parabolicCylinder (show E from x₀) top (2 * r)
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_ball
  have hlocal : ∀ z ∈ Ω, ∃ (Q : Set (ℝ × E)) (f : ℝ × E → ℝ),
      IsOpen Q ∧ z ∈ Q ∧ ContinuousOn f Q ∧
        f =ᵐ[μ.restrict Q] Function.uncurry u := by
    intro z hz
    have hz' : z ∈ Ioo (top - (2 * r) ^ 2) top ×ˢ
        horizontalBall (G.horizontalFields hq) x₀ (2 * r) := by
      simpa only [Ω, parabolicCylinder_eq_horizontal G hq hqpos hspan, hB] using hz
    obtain ⟨t, ρ, hρ, hzρ, hweak, hup, hlo⟩ :=
      hu'.exists_bounded_parabolic_neighborhood G hq hqpos hw hspan
        hcoeff hlam (hlam.le.trans hlamΛ) hquad z hz'
    let W := essSup (Function.uncurry u) (μ.restrict (parabolicCylinder z.2 t (2 * ρ))) -
      essInf (Function.uncurry u) (μ.restrict (parabolicCylinder z.2 t (2 * ρ)))
    obtain ⟨f, hf, heq, _⟩ := exists_matrix_holder_representative_of_bounded_cylinder
      G hq hqpos hw hspan c hc θ α hθ.1.le hα.1 hθα coeff
        (hcontraction coeff hcoeff hquad) z.2 t ρ W hρ
      (essential_oscillation_nonneg hup hlo) u hweak hup hlo le_rfl
    exact ⟨parabolicCylinder z.2 t ρ, f, isOpen_Ioo.prod isOpen_ball, hzρ, hf, heq⟩
  obtain ⟨v, hv, heqv⟩ := exists_continuousOn_representative_of_local_representatives
    μ Ω hΩ (Function.uncurry u) hlocal
  have hinner : parabolicCylinder (show E from x₀) top r ⊆ Ω :=
    parabolicCylinder_mono (show E from x₀) top hr.le (by linarith)
  have hvinner := hv.mono hinner
  have heqinner : v =ᵐ[μ.restrict (parabolicCylinder (show E from x₀) top r)]
      Function.uncurry u := ae_restrict_of_ae_restrict_of_subset hinner heqv
  refine ⟨fun t x => v (t, x), ?_, ?_, ?_⟩
  · rw [hB, ← parabolicCylinder_eq_horizontal G hq hqpos hspan]
    change v =ᵐ[μ.restrict (parabolicCylinder (show E from x₀) top r)] Function.uncurry u
    exact heqinner
  · rw [hB, ← parabolicCylinder_eq_horizontal G hq hqpos hspan]
    change ContinuousOn v (parabolicCylinder (show E from x₀) top r)
    exact hvinner
  intro m M hmM
  have hmM' : ∀ᵐ z ∂μ.restrict Ω, m ≤ u z.1 z.2 ∧ u z.1 z.2 ≤ M := by
    change ∀ᵐ z : ℝ × (Fin N → ℝ) ∂(μ : Measure (ℝ × (Fin N → ℝ))).restrict
      (show Set (ℝ × (Fin N → ℝ)) from Ω), m ≤ u z.1 z.2 ∧ u z.1 z.2 ≤ M
    simpa only [μ, Ω, CarnotPoint.spaceTimeVolume_eq_coordinate,
      parabolicCylinder_eq_horizontal G hq hqpos hspan,
      show (2 * r) ^ 2 = 4 * r ^ 2 by ring, hB] using hmM
  have hμ : μ.restrict Ω ≠ 0 := by
    simpa only [μ, Ω, CarnotPoint.spaceTimeVolume_eq_coordinate, parabolicCylinder_eq_horizontal G hq hqpos hspan] using
      volume_restrict_horizontal_cylinder_ne_zero G hq hqpos hspan x₀
        (show top - (2 * r) ^ 2 < top by nlinarith [sq_pos_of_pos hr])
        (show 0 < 2 * r by positivity)
  have : (ae (μ.restrict Ω)).NeBot := ae_neBot.mpr hμ
  obtain ⟨z₁, hz₁⟩ := hmM'.exists
  have hW : 0 ≤ M - m := sub_nonneg.mpr (hz₁.1.trans hz₁.2)
  have hup : IsBoundedUnder (· ≤ ·) (ae (μ.restrict Ω)) (Function.uncurry u) :=
    ⟨M, hmM'.mono fun _ h => h.2⟩
  have hlo : IsBoundedUnder (· ≥ ·) (ae (μ.restrict Ω)) (Function.uncurry u) :=
    ⟨m, hmM'.mono fun _ h => h.1⟩
  have hosc : essSup (Function.uncurry u) (μ.restrict Ω) -
      essInf (Function.uncurry u) (μ.restrict Ω) ≤ M - m :=
    sub_le_sub (essSup_le_of_ae_le M (hmM'.mono fun _ h => h.2) hlo.isCoboundedUnder_le)
      (le_essInf_of_ae_le m (hmM'.mono fun _ h => h.1) hup.isCoboundedUnder_ge)
  obtain ⟨v₁, hv₁, heq₁, hbound⟩ := exists_matrix_holder_representative_of_bounded_cylinder
    G hq hqpos hw hspan c hc θ α hθ.1.le hα.1 hθα coeff
    (hcontraction coeff hcoeff hquad) (show E from x₀)
    top r (M - m) hr hW u hu' hup hlo hosc
  have heq : EqOn v v₁ (parabolicCylinder (show E from x₀) top r) :=
    Measure.eqOn_open_of_ae_eq (heqinner.trans heq₁.symm)
      (isOpen_Ioo.prod isOpen_ball) hvinner hv₁
  intro z hz w hw
  have hz' : z ∈ parabolicCylinder (show E from x₀) top r := by
    simpa only [parabolicCylinder_eq_horizontal G hq hqpos hspan, hB] using hz
  have hw' : w ∈ parabolicCylinder (show E from x₀) top r := by
    simpa only [parabolicCylinder_eq_horizontal G hq hqpos hspan, hB] using hw
  change |v (show ℝ × E from z) - v (show ℝ × E from w)| ≤
    (1024 / 15 : ℝ) ^ α * ((d z.2 w.2 + Real.sqrt |z.1 - w.1|) / r) ^ α * (M - m)
  rw [heq hz', heq hw']
  have hd : dist ((parabolicSpaceTimeHomeomorph E).symm z)
      ((parabolicSpaceTimeHomeomorph E).symm w) ≤
      d z.2 w.2 + Real.sqrt |z.1 - w.1| := by
    rw [parabolicSpaceTime_dist]
    have hdist : dist (show E from z.2) w.2 = d z.2 w.2 := by
      rw [dist_edist, CarnotPoint.edist_eq]
    change max (Real.sqrt |z.1 - w.1|) (dist (show E from z.2) w.2) ≤ _
    rw [← hdist]
    exact max_le (by linarith [dist_nonneg (x := (show E from z.2)) (y := w.2)])
      (by linarith [Real.sqrt_nonneg |z.1 - w.1|])
  exact (hbound z hz' w hw').trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg dist_nonneg hr.le)
        (div_le_div_of_nonneg_right hd hr.le) hα.1.le)
      (Real.rpow_nonneg (by norm_num) _)) hW)

end HeatKernel
