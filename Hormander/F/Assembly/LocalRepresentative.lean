-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.Assembly.LocalDistribution
public import Hormander.F.Assembly.Cutoffs

/-!
# Local smooth representative

For a fixed point `x₀ ∈ Ω`, a frame patch, the local regularity estimate, the smooth
representative, and the real-part identification give a local smooth
representative of `u`.
-/

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap Topology Filter Set Metric

namespace Hormander.F

/-- Every point of `Ω` has an open neighbourhood in `Ω` on which `u`
agrees almost everywhere with a smooth function, assuming the local regularity estimate and
localized forcing identity. -/
theorem exists_local_representative {k N : ℕ} (hN : 0 < N) {Ω : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c g u : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hspan : Hormander.Interface.LieAlgebraSpansOn Ω X)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (hE4 : E4Statement) (x₀ : Fin N → ℝ) (hx₀ : x₀ ∈ Ω)
    (hF4 : ∀ P : LocalPatch hN (coordinateEquiv N '' Ω) (pushVectorFields X)
      (fun y => c ((coordinateEquiv N).symm y)) (coordinateEquiv N x₀),
      LocalizedForcingStatement hN X c g u x₀ P) :
    ∃ U : Set (Fin N → ℝ), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ Ω ∧
      ∃ f : (Fin N → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧ f =ᵐ[volume.restrict U] u := by
  obtain ⟨P⟩ := exists_local_frame_patch hN hΩ X c x₀ hx₀ hX hspan hc
  set e := coordinateEquiv N with he
  obtain ⟨ζ, ζ', χ, hζ, hζ', hχ, hcζ, hcζ', hcχ, hζ1, hζζ', hχζ', hKB, hχB⟩ :=
    exists_nested_cutoffs (e x₀) P.radius_pos
  obtain ⟨hv, f, hfeq, hforce⟩ := hF4 P χ ζ' hχ hcχ hχB hζ' hcζ' hχζ'
  have hneg := localized_negative_sobolev hζ' hcζ' hv
  have hmem := hE4 P.extendedX P.extendedC P.extendedX_smooth P.extendedX_compact
    P.extendedC_smooth P.extendedC_compact (K := tsupport ζ') hcζ' (U := ball (e x₀) P.radius)
    isOpen_ball hKB P.words P.frame_on_ball hζ hζ' hζζ' subset_rfl _ f hforce hneg
  -- `ζ' = 1` and `χ = 1` on `tsupport ζ`.
  have hζ'one : ∀ x ∈ tsupport ζ, ζ' x = 1 := fun x hx =>
    (hζζ'.self_of_nhdsSet x hx)
  have hζsub : tsupport ζ ⊆ tsupport ζ' := by
    intro x hx
    apply subset_tsupport
    rw [Function.mem_support, hζ'one x hx]
    exact one_ne_zero
  have hχone : ∀ x ∈ tsupport ζ, χ x = 1 := fun x hx => hχζ'.self_of_nhdsSet x (hζsub hx)
  have hvw : ∀ y, localizedInput ζ u y = (ζ y : ℂ) * localizedInput χ u y := by
    intro y
    by_cases hy : y ∈ tsupport ζ
    · simp [localizedInput, hχone y hy]
    · have : ζ y = 0 := by
        by_contra h
        exact hy (subset_tsupport ζ h)
      simp [localizedInput, this]
  have hw : Integrable (localizedInput ζ u) volume := by
    have := integrable_cutoff_mul hζ hcζ hv
    exact this.congr (Filter.Eventually.of_forall fun y => (hvw y).symm)
  have hsm := smulLeft_toTemperedDistribution hζ hcζ hv hw hvw
  rw [hsm] at hmem
  obtain ⟨F, hF, hFae⟩ := exists_smooth_realPart_ae hw
    (uR := fun y => ζ y * u (e.symm y)) (fun y => rfl) hmem
  refine ⟨e ⁻¹' ball (e x₀) (P.radius / 8), isOpen_ball.preimage e.continuous,
    mem_ball_self (by linarith [P.radius_pos]), ?_, fun x => (F (e x)).re, ?_, ?_⟩
  · intro x hx
    have h1 : e x ∈ closure (ball (e x₀) P.radius) :=
      subset_closure (ball_subset_ball (by linarith [P.radius_pos]) hx)
    obtain ⟨z, hz, hze⟩ := P.ball_closure_subset h1
    have : z = x := e.injective hze
    exact this ▸ hz
  · exact (Complex.reCLM.contDiff.comp (hF.comp e.contDiff)).contDiffOn
  · have h2 : (fun y : E₂ N => ζ y * u (e.symm y)) =ᵐ[volume] fun y => (F y).re := hFae
    have h3 := (ae_eq_coordinateEquiv_iff (N := N)).1 h2
    refine (ae_restrict_iff' (isOpen_ball.preimage e.continuous).measurableSet).2 ?_
    filter_upwards [h3] with x hx hxU
    have hx' : ζ (e x) * u (e.symm (e x)) = (F (e x)).re := hx
    rw [hζ1 (e x) hxU, one_mul, e.symm_apply_apply] at hx'
    exact hx'.symm

end Hormander.F
