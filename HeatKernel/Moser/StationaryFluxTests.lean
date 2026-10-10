-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.StationarySolutions
public import HeatKernel.Moser.JointMeasurability

/-! # Integrable stationary flux tests

Bounded measurable coefficients and local horizontal square integrability make every
compactly supported spacetime principal term integrable.
-/

@[expose] public section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal BigOperators

namespace HeatKernel

/-- A bounded stationary coefficient flux paired with a compact smooth spacetime test
has an integrable principal term. -/
theorem integrable_stationary_flux_test {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {U : Opens (Fin N → ℝ)} {u : (Fin N → ℝ) → ℝ}
    {g : Fin q → (Fin N → ℝ) → ℝ}
    (hu : memSobolevXLoc noDriftWeight X U 1 2 u)
    (hg : ∀ i, hasWeakWordDeriv X U [i] u (g i))
    {a : (Fin N → ℝ) → Fin q → Fin q → ℝ} {C : ℝ}
    (ha : ∀ i j, Measurable (fun x => a x i j))
    (hb : ∀ i j, ∀ᵐ x ∂volume, ‖a x i j‖ ≤ C)
    {φ : ℝ × (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Prod.snd ⁻¹' (U : Set (Fin N → ℝ))) :
    Integrable (fun z : ℝ × (Fin N → ℝ) => ∑ i, ∑ j,
      a z.2 i j * g j z.2 * fderiv ℝ φ z (0, X i z.2)) := by
  let J := Prod.fst '' tsupport φ
  let K := Prod.snd '' tsupport φ
  have hJ : IsCompact J := hc.image continuous_fst
  have hK : IsCompact K := hc.image continuous_snd
  have hKU : K ⊆ (U : Set (Fin N → ℝ)) := by
    rintro x ⟨z, hz, rfl⟩
    exact hs hz
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have hgLp := memLp_two_stationary_horizontal_on_compact hu hJ hK hKU j (hg j)
  have haM : AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => a z.2 i j)
      (volume.restrict (J ×ˢ K)) :=
    ((ha i j).comp measurable_snd).aestronglyMeasurable
  have hbM : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume, ‖a z.2 i j‖ ≤ C := by
    change ∀ᵐ z ∂volume.prod volume, ‖a z.2 i j‖ ≤ C
    exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (Fin N → ℝ)))).ae (hb i j)
  have hflux := memLp_two_mul_of_ae_bound haM hgLp (ae_restrict_of_ae hbM)
  have hd : Continuous (fun z : ℝ × (Fin N → ℝ) => fderiv ℝ φ z (0, X i z.2)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply
      (continuous_const.prodMk ((hX i).continuous.comp continuous_snd))
  have hdLp : MemLp (fun z : ℝ × (Fin N → ℝ) => fderiv ℝ φ z (0, X i z.2)) 2 volume :=
    hd.memLp_of_hasCompactSupport (hasCompactSupport_fderiv_apply_variable hc _)
  have hi := hflux.integrable_mul (hdLp.restrict (J ×ˢ K))
  apply (integrableOn_iff_integrable_of_support_subset (s := J ×ˢ K) ?_).mp hi
  intro z hz
  have hdne : fderiv ℝ φ z (0, X i z.2) ≠ 0 := (mul_ne_zero_iff.mp hz).2
  have hzφ : z ∈ tsupport φ :=
    tsupport_fderiv_apply_variable_subset φ (fun z => (0, X i z.2)) (subset_tsupport _ hdne)
  exact ⟨⟨z, hzφ, rfl⟩, ⟨z, hzφ, rfl⟩⟩

/-- A local elliptic Sobolev solution for bounded measurable coefficients belongs to the
literal parabolic weak class when extended constantly in time. -/
theorem isLocalWeakSolution_stationary_of_bounded_coefficients {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    {u : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ}
    (hu : memSobolevXLoc noDriftWeight (G.horizontalFields hq) U 1 2 u)
    (hg : ∀ i, hasWeakWordDeriv (G.horizontalFields hq) U [i] u (g i))
    (ha : ∀ i j, Measurable (fun x => a x i j)) {C : ℝ}
    (hb : ∀ i j, ∀ᵐ x ∂volume, ‖a x i j‖ ≤ C)
    (hell : ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞),
      (∫ x in (U : Set (Fin N → ℝ)),
        ∑ i, ∑ j, a x i j * g j x * fieldDerivative (G.horizontalFields hq i) ψ x) = 0) :
    IsLocalWeakSolution G hq hqpos hw hspan (fun _ x => a x) I U (fun _ x => u x) := by
  apply isLocalWeakSolution_stationary_of_integrable_flux_tests G hq hqpos hw hspan a I U hu hg hell
  intro φ hφ hc hs
  exact integrable_stationary_flux_test (G.horizontalFields_contDiff hq) hu hg ha hb hφ hc
    (fun z hz => (hs hz).2)

end HeatKernel
