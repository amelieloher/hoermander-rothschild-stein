-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.StationaryTests
public import HeatKernel.Moser.SmoothSpatialIntegration
public import HeatKernel.Form.ParabolicEnergyCurves

/-! # Stationary elliptic solutions in the parabolic weak class

Spatial weak identities extend to spacetime tests by taking spatial sections and using
Fubini. Integrability of the principal test term is stated explicitly.
-/

@[expose] public section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped BigOperators ENNReal

namespace HeatKernel

/-- A stationary local Sobolev solution of the elliptic test identity is a parabolic local
weak solution, provided its spacetime principal test terms are integrable. -/
theorem isLocalWeakSolution_stationary_of_integrable_flux_tests {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    {u : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ}
    (hu : memSobolevXLoc noDriftWeight (G.horizontalFields hq) U 1 2 u)
    (hg : ∀ i, hasWeakWordDeriv (G.horizontalFields hq) U [i] u (g i))
    (hell : ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞),
      (∫ x in (U : Set (Fin N → ℝ)),
        ∑ i, ∑ j, a x i j * g j x * fieldDerivative (G.horizontalFields hq i) ψ x) = 0)
    (hflux : ∀ φ : ℝ × (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)) →
      Integrable (fun z : ℝ × (Fin N → ℝ) => ∑ i, ∑ j,
        a z.2 i j * g j z.2 * fderiv ℝ φ z (0, G.horizontalFields hq i z.2))) :
    IsLocalWeakSolution G hq hqpos hw hspan (fun _ x => a x) I U (fun _ x => u x) := by
  have hum : AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => u z.2)
      ((volume.restrict (I : Set ℝ)).prod (volume.restrict (U : Set (Fin N → ℝ)))) :=
    (hg ⟨0, hqpos⟩).1.aestronglyMeasurable.comp_snd
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hum
  refine ⟨hum, fun i _ x => g i x, ae_of_all _ (fun _ => hg), ?_, ?_⟩
  · intro J K hJ _ hK hKU
    exact ⟨essSup_stationary_eLpNorm_lt_top hu J hK hKU,
      fun i => memLp_two_stationary_horizontal_on_compact hu hJ hK hKU i (hg i)⟩
  · intro φ hφ hc hs
    have hsU : tsupport φ ⊆ Prod.snd ⁻¹' (U : Set (Fin N → ℝ)) := fun z hz => (hs hz).2
    have ht := integrable_stationary_mul_fderiv_time hu hφ hc hsU
    have htzero := integral_stationary_mul_fderiv_time_eq_zero hu hφ hc hsU
    have hF := hflux φ hφ hc hs
    have hspace (t : ℝ) : (∫ x : Fin N → ℝ, ∑ i, ∑ j,
        a x i j * g j x * fderiv ℝ φ (t, x) (0, G.horizontalFields hq i x)) = 0 := by
      have hφS : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ (t, x)) :=
        hφ.comp (contDiff_const.prodMk contDiff_id)
      have hsS : tsupport (fun x => φ (t, x)) ⊆ (U : Set (Fin N → ℝ)) := by
        intro x hx
        exact (hs (tsupport_comp_subset_preimage φ
          (continuous_const.prodMk continuous_id) hx)).2
      let ψ : TestFunction U ℝ (⊤ : ℕ∞) :=
        ⟨(fun x => φ (t, x)), hφS, hasCompactSupport_spaceSection hc t, hsS⟩
      have he := hell ψ
      change (∫ x in (U : Set (Fin N → ℝ)), ∑ i, ∑ j, a x i j * g j x *
        fderiv ℝ (fun y => φ (t, y)) x (G.horizontalFields hq i x)) = 0 at he
      simp_rw [fderiv_spaceSection_apply (hφ.differentiable (by simp))] at he
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at he
      · exact he
      · intro x hx
        have hz : (t, x) ∉ tsupport φ := fun hz => hx (hs hz).2
        simp only [fderiv_of_notMem_tsupport ℝ hz, zero_apply, mul_zero, Finset.sum_const_zero]
    have hFzero : (∫ z : ℝ × (Fin N → ℝ), ∑ i, ∑ j,
        a z.2 i j * g j z.2 * fderiv ℝ φ z (0, G.horizontalFields hq i z.2)) = 0 := by
      change (∫ z : ℝ × (Fin N → ℝ), ∑ i, ∑ j,
        a z.2 i j * g j z.2 * fderiv ℝ φ z (0, G.horizontalFields hq i z.2)
        ∂volume.prod volume) = 0
      rw [integral_prod _ hF]
      exact integral_eq_zero_of_ae (ae_of_all _ hspace)
    refine ⟨ht.neg.add hF, ?_⟩
    have hadd := integral_add ht.neg hF
    change (∫ z : ℝ × (Fin N → ℝ), -(u z.2 * fderiv ℝ φ z (1, 0)) +
      ∑ i, ∑ j, a z.2 i j * g j z.2 * fderiv ℝ φ z (0, G.horizontalFields hq i z.2)) = _ at hadd
    rw [hadd]
    change (∫ z : ℝ × (Fin N → ℝ), -(u z.2 * fderiv ℝ φ z (1, 0))) + _ = 0
    rw [integral_neg, htzero, hFzero]
    simp

end HeatKernel
