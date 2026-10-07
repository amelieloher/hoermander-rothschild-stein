-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.UniformLimitCompactPairing
public import RothschildStein.H1.Integration
public import RothschildStein.S.ClassicalWords
public import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Step 5: uniform convergence of C¹ potentials and
their actual invariant field derivatives identifies the derivative
of the limit by compact-test integration by parts. -/
theorem StandingHypotheses.fieldDerivative_eq_of_uniformLimits
    (H : StandingHypotheses G q) (i : Fin (q + 1))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [NeBot l]
    {u : ι → (Fin N → ℝ) → ℝ} {h g : (Fin N → ℝ) → ℝ}
    (hu : ∀ ε, ContDiff ℝ 1 (u ε)) (hh : ContDiff ℝ 1 h) (hg : Continuous g)
    (htu : TendstoUniformly u h l)
    (htD : TendstoUniformly (fun ε => fieldDerivative (H.fields i) (u ε)) g l) :
    fieldDerivative (H.fields i) h = g := by
  let U : Opens (Fin N → ℝ) := ⟨univ, isOpen_univ⟩
  have hdc (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (fieldDerivative (H.fields i) f) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply (H.fields_smooth G i).continuous
  have hpair (φ : TestFunction U ℝ (⊤ : ℕ∞)) : (∫ x, g x * φ x) = -(∫ x, h x * fieldDerivative (H.fields i) φ x) := by
    have hcφD := (smooth_fieldDerivative (H.fields i) (H.fields_smooth G i) φ φ.contDiff).continuous
    have hsφD : HasCompactSupport (fieldDerivative (H.fields i) φ) :=
      φ.hasCompactSupport.of_isClosed_subset isClosed_closure (S.tsupport_fieldDerivative_subset (H.fields i) φ)
    have htL := tendsto_integral_mul_compact_of_uniformLimit (fun ε => hdc (u ε) (hu ε)) hg
      φ.contDiff.continuous φ.hasCompactSupport htD
    have htR := tendsto_integral_mul_compact_of_uniformLimit (fun ε => (hu ε).continuous) hh.continuous
      hcφD hsφD htu
    have he (ε : ι) : (∫ x, fieldDerivative (H.fields i) (u ε) x * φ x) =
        -(∫ x, u ε x * fieldDerivative (H.fields i) φ x) := by
      have h := H.integral_field_test G U i (u ε) (hu ε).contDiffOn φ
      change (∫ x in univ, fieldDerivative (H.fields i) (u ε) x * φ x) =
        -(∫ x in univ, u ε x * fieldDerivative (H.fields i) φ x) at h
      simpa only [Measure.restrict_univ] using h
    have hf := funext he
    rw [hf] at htL
    exact tendsto_nhds_unique htL htR.neg
  have hEq (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
      (∫ x, fieldDerivative (H.fields i) h x * φ x) = ∫ x, g x * φ x := by
    have he := H.integral_field_test G U i h hh.contDiffOn φ
    change (∫ x in univ, fieldDerivative (H.fields i) h x * φ x) =
      -(∫ x in univ, h x * fieldDerivative (H.fields i) φ x) at he
    simp only [Measure.restrict_univ] at he
    exact he.trans (hpair φ).symm
  let D := fun x => fieldDerivative (H.fields i) h x - g x
  have hD : Continuous D := (hdc h hh).sub hg
  have hz := isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hD.locallyIntegrable (μ := volume)).locallyIntegrableOn univ) (fun φ hc hs hsU => ?_)
  · have hae : D =ᵐ[volume] fun _ => 0 := hz.mono fun x hx => hx (mem_univ x)
    have he := MeasureTheory.Measure.eq_of_ae_eq hae hD continuous_const
    funext x
    have hx := congrFun he x
    exact sub_eq_zero.mp hx
  · let ψ : TestFunction U ℝ (⊤ : ℕ∞) := ⟨φ, hc, hs, hsU⟩
    have he := hEq ψ
    have hi1 : Integrable (fun x => fieldDerivative (H.fields i) h x * φ x) volume :=
      ((hdc h hh).mul hc.continuous).integrable_of_hasCompactSupport hs.mul_left
    have hi2 : Integrable (fun x => g x * φ x) volume :=
      (hg.mul hc.continuous).integrable_of_hasCompactSupport hs.mul_left
    have hzero : (∫ x, (fieldDerivative (H.fields i) h x - g x) * φ x) = 0 := by
      simp_rw [sub_mul]
      rw [integral_sub hi1 hi2]
      change (∫ x, fieldDerivative (H.fields i) h x * ψ x) - (∫ x, g x * ψ x) = 0
      rw [he, sub_self]
    convert hzero using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by change φ x * D x = D x * φ x; ring

end RothschildStein.H1
