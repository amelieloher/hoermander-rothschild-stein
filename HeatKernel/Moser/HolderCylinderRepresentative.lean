-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderMeasuredDomain
public import HeatKernel.Moser.HolderRationalOscillationRepresentative
public import HeatKernel.Moser.DyadicDecay
import Mathlib.Tactic

/-! # Continuous representatives from ambient cylinder oscillations -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter Topology
namespace HeatKernel

/-- A backward parabolic cylinder with an open top. -/
def parabolicCylinder {X : Type*} [MetricSpace X] (x : X) (t r : ℝ) : Set (ℝ × X) :=
  Ioo (t - r ^ 2) t ×ˢ ball x r

/-- Positive radii give nested backward parabolic cylinders. -/
theorem parabolicCylinder_mono {X : Type*} [MetricSpace X] (x : X) (t : ℝ)
    {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R) :
    parabolicCylinder x t r ⊆ parabolicCylinder x t R := by
  intro z hz
  exact ⟨⟨by dsimp [parabolicCylinder] at hz ⊢; nlinarith [hz.1.1], hz.1.2⟩,
    ball_subset_ball hR hz.2⟩

/-- A finite ambient oscillation and uniform half-radius contraction give a
continuous representative on the inner cylinder, with a normalized modulus. -/
theorem exists_continuous_representative_of_cylinder_contraction
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (c : ℕ → X) (hc : DenseRange c)
    (μ : Measure (ℝ × X)) [μ.IsOpenPosMeasure] (u : ℝ × X → ℝ)
    (x₀ : X) (top r α θ W : ℝ) (hr : 0 < r) (hα : 0 < α)
    (hθ : 0 ≤ θ) (hθα : θ ≤ (1 / 2 : ℝ) ^ α) (hW : 0 ≤ W)
    (hup : IsBoundedUnder (· ≤ ·) (ae (μ.restrict (parabolicCylinder x₀ top (2 * r)))) u)
    (hlo : IsBoundedUnder (· ≥ ·) (ae (μ.restrict (parabolicCylinder x₀ top (2 * r)))) u)
    (hglobal : essSup u (μ.restrict (parabolicCylinder x₀ top (2 * r))) -
      essInf u (μ.restrict (parabolicCylinder x₀ top (2 * r))) ≤ W)
    (hstep : ∀ (x : X) (t ρ : ℝ), 0 < ρ →
      parabolicCylinder x t ρ ⊆ parabolicCylinder x₀ top (2 * r) →
      essSup u (μ.restrict (parabolicCylinder x t (ρ / 2))) -
        essInf u (μ.restrict (parabolicCylinder x t (ρ / 2))) ≤
      θ * (essSup u (μ.restrict (parabolicCylinder x t ρ)) -
        essInf u (μ.restrict (parabolicCylinder x t ρ)))) :
    ∃ v : ℝ × X → ℝ, ContinuousOn v (parabolicCylinder x₀ top r) ∧
      v =ᵐ[μ.restrict (parabolicCylinder x₀ top r)] u ∧
      ∀ z ∈ parabolicCylinder x₀ top r, ∀ w ∈ parabolicCylinder x₀ top r,
        |v z - v w| ≤ (1024 / 15 : ℝ) ^ α *
          (dist ((parabolicSpaceTimeHomeomorph X).symm z)
            ((parabolicSpaceTimeHomeomorph X).symm w) / r) ^ α * W := by
  let : MeasurableSpace (ParabolicSpaceTime X) := borel _
  let : BorelSpace (ParabolicSpaceTime X) := ⟨rfl⟩
  let h := parabolicSpaceTimeHomeomorph X
  let Ω : Set (ParabolicSpaceTime X) := h ⁻¹' parabolicCylinder x₀ top r
  have hΩopen : IsOpen Ω :=
    (isOpen_Ioo.prod isOpen_ball).preimage h.continuous
  let e : Ω → ℝ × X := fun z => h z.val
  have he : IsOpenEmbedding e := h.isOpenEmbedding.comp hΩopen.isOpenEmbedding_subtypeVal
  have herange : range e = parabolicCylinder x₀ top r := by
    ext z
    exact ⟨fun ⟨w, hw⟩ => hw ▸ w.property,
      fun hz => ⟨⟨h.symm z, by simpa only [Ω, mem_preimage, h.apply_symm_apply] using hz⟩,
        h.apply_symm_apply z⟩⟩
  let ν := μ.restrict (parabolicCylinder x₀ top (2 * r))
  let μΩ := μ.comap e
  have hμΩ : ν.comap e = μΩ := by
    rw [he.measurableEmbedding.comap_restrict]
    have hp : e ⁻¹' parabolicCylinder x₀ top (2 * r) = univ := by
      apply eq_univ_of_forall
      intro z
      exact parabolicCylinder_mono x₀ top hr.le (by linarith) z.property
    rw [hp, Measure.restrict_univ]
  let : μΩ.IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap μ he
  let ω : ℝ → X → ℝ → ℝ := fun t x ρ =>
    essSup u (ν.restrict (parabolicCylinder x t ρ)) -
      essInf u (ν.restrict (parabolicCylinder x t ρ))
  have hb := boundedUnder_comap he.measurableEmbedding hup hlo
  rw [hμΩ] at hb
  have hcomparison (t ρ : ℝ) (x : X) :
      essSup (u ∘ e) (μΩ.restrict (e ⁻¹' parabolicCylinder x t ρ)) -
        essInf (u ∘ e) (μΩ.restrict (e ⁻¹' parabolicCylinder x t ρ)) ≤ ω t x ρ := by
    rw [← hμΩ, ← he.measurableEmbedding.comap_restrict]
    exact essential_oscillation_comap_le he.measurableEmbedding
      (hup.mono (ae_mono Measure.restrict_le_self))
      (hlo.mono (ae_mono Measure.restrict_le_self))
  have hmono (t : ℝ) (x : X) : MonotoneOn (ω t x) (Ici 0) := by
    intro ρ hρ R _ hρR
    exact essential_oscillation_mono
      (Measure.restrict_mono (parabolicCylinder_mono x t hρ hρR) le_rfl)
      (hup.mono (ae_mono Measure.restrict_le_self))
      (hlo.mono (ae_mono Measure.restrict_le_self))
  have hdecay (t : ℝ) (x : X)
      (hsub : parabolicCylinder x t (2 * (15 * r / 32)) ⊆
        parabolicCylinder x₀ top (2 * r)) (n : ℕ) :
      ω t x ((15 * r / 32) * (1 / 2 : ℝ) ^ n) ≤ θ ^ n * W := by
    have hsmall {ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ ≤ 15 * r / 32) :
        parabolicCylinder x t ρ ⊆ parabolicCylinder x₀ top (2 * r) :=
      (parabolicCylinder_mono x t hρ (by linarith)).trans hsub
    have hbase : ω t x (15 * r / 32) ≤ W :=
      (essential_oscillation_mono Measure.restrict_le_self hup hlo).trans hglobal
    apply (le_pow_mul_of_half_radius_decay (by positivity : 0 < 15 * r / 32)
      hθ (fun ρ hρ hρR => ?_) n).trans
      (mul_le_mul_of_nonneg_left hbase (pow_nonneg hθ n))
    have hfull := hsmall hρ.le hρR
    have hhalf := (parabolicCylinder_mono x t (by positivity : 0 ≤ ρ / 2)
      (by linarith : ρ / 2 ≤ ρ)).trans hfull
    change essSup u (ν.restrict _) - essInf u (ν.restrict _) ≤
      θ * (essSup u (ν.restrict _) - essInf u (ν.restrict _))
    dsimp only [ν]
    rw [Measure.restrict_restrict_of_subset hhalf, Measure.restrict_restrict_of_subset hfull]
    exact hstep x t ρ hρ hfull
  have hglobal' : essSup (u ∘ e) μΩ - essInf (u ∘ e) μΩ ≤ W := by
    have hh := essential_oscillation_comap_le he.measurableEmbedding hup hlo
    rw [hμΩ] at hh
    exact hh.trans hglobal
  obtain ⟨v, hv, heq, hbound⟩ :=
    exists_continuous_parabolic_representative_of_rational_oscillation_decay c hc μΩ u ω
      hr hα hθ hθα hW
      (fun z hz => ⟨hz.2, hz.1.1, hz.1.2⟩) hb.1 hb.2
      hglobal'
      (fun τ ρ i => hcomparison τ ρ (c i))
      (fun τ i => (hmono τ (c i)).mono (fun _ h => h.1))
      (fun τ i hs n => hdecay τ (c i) (by
        simpa only [parabolicCylinder, show (2 * (15 * r / 32)) ^ 2 =
          4 * (15 * r / 32) ^ 2 by ring,
          show (2 * r) ^ 2 = 4 * r ^ 2 by ring] using hs) n)
  obtain ⟨w, hw, hweq, hwe⟩ := exists_representative_on_embedding_range
    he.isEmbedding he.measurableEmbedding μ u v hv heq
  rw [herange] at hw hweq
  refine ⟨w, hw, hweq, ?_⟩
  intro z hz w hw
  let z' : Ω := ⟨h.symm z, hz⟩
  let w' : Ω := ⟨h.symm w, hw⟩
  have hz' : e z' = z := h.apply_symm_apply z
  have hw' : e w' = w := h.apply_symm_apply w
  rw [← hz', ← hw', hwe z', hwe w']
  change |v z' - v w'| ≤ (1024 / 15 : ℝ) ^ α *
    (dist (h.symm (h z'.val)) (h.symm (h w'.val)) / r) ^ α * W
  simpa only [h.symm_apply_apply, Subtype.dist_eq] using hbound z' w'

end HeatKernel
