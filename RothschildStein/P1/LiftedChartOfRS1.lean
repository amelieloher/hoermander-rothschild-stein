-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LiftedChart

/-!
# The conclusions of the lifting theorem as lifted charts

`RothschildStein.P1.liftedChart_of_noDrift` and `RothschildStein.P1.liftedChart_of_drift` take, as
their hypothesis, the conclusion of the lifting theorems
`RothschildStein.exists_lift_approximation_noDrift` and
`RothschildStein.exists_lift_approximation_drift` copied verbatim (this file does not import the
lifting statements or their proofs), and repackage it as `LiftedChart`. Nothing is assumed beyond
that conclusion. The final assembly is
`liftedChart_of_noDrift Ω hΩ X x₀ s (exists_lift_approximation_noDrift hn hq Ω hΩ X hX x₀ hx₀ s hs hspan)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein.P1

/-- The conclusion of the lifting theorem (no drift) is a lifted chart.
The hypothesis `h` is, verbatim, the conclusion of the lifting theorem
`RothschildStein.exists_lift_approximation_noDrift` (alphabet `Fin q`, all weights one), so that
`liftedChart_of_noDrift Ω hΩ X x₀ s (exists_lift_approximation_noDrift hn hq Ω hΩ X hX x₀ hx₀ s hs hspan)`
elaborates. The only non-syntactic step is the model dilation exponent, written
`t ^ (-1 : ℤ)` in the lifting theorem and `-(w i)` in `LiftedChart.model_field_homogeneous`. -/
theorem liftedChart_of_noDrift {n q : ℕ}
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (s : ℕ)
    (h :
    ∃ m : ℕ, n + m = freeDimension q s (fun _ : Fin q => 1) ∧
    ∃ P : Fin q → Fin m → MvPolynomial (Fin (n + m)) ℝ,
    ∃ U : Set (Fin (n + m) → ℝ),
    ∃ G : HomogeneousGroup (n + m),
    ∃ B : Fin (n + m) → List (Fin q),
    ∃ v : Fin q → (Fin (n + m) → ℝ),
    ∃ Y : Fin q → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ),
    ∃ Θ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ),
    ∃ e : (Fin (n + m) → ℝ) → OpenPartialHomeomorph
      (Fin (n + m) → ℝ) (Fin (n + m) → ℝ),
    ∃ R : List (Fin q) → (Fin (n + m) → ℝ) →
      (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ),
    ∃ c : (Fin (n + m) → ℝ) → ℝ,
    ∃ ωp ωm : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ,
    let Xl := triangularLift X P
    let O := {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω}
    let T := {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) |
      z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
    (∀ i l, ∀ j ∈ (P i l).vars, j.val < n + l.val) ∧
    IsOpen U ∧ IsCompact (closure U) ∧ closure U ⊆ O ∧
    joinPoint x₀ (0 : Fin m → ℝ) ∈ U ∧
    (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xl i) O) ∧
    (∀ ξ ∈ U, FreeAt (fun _ : Fin q => 1) s Xl ξ ∧ StepSpansAt (fun _ : Fin q => 1) s Xl ξ) ∧
    (∀ j, B j ≠ [] ∧ wordWeight (fun _ : Fin q => 1) (B j) ≤ s ∧ G.weight j = wordWeight (fun _ : Fin q => 1) (B j)) ∧
    LinearIndependent ℝ (fun j => (truncatedBracket (B j) : WordCoefficients q s (fun _ : Fin q => 1))) ∧
    Submodule.span ℝ (Set.range (fun j =>
      (truncatedBracket (B j) : WordCoefficients q s (fun _ : Fin q => 1)))) = formalSpan q s (fun _ : Fin q => 1) ∧
    (∀ i, (∑ j, v i j • (truncatedBracket (B j) : WordCoefficients q s (fun _ : Fin q => 1))) =
      truncatedBracket [i]) ∧
    (∀ u, (fun j => MvPolynomial.eval u (G.inversePolynomial j)) = -u) ∧
    (∀ i u, Y i u = fderiv ℝ (G.mul u) 0 (v i)) ∧
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i)) ∧
    (∀ i u z, fderiv ℝ (G.mul u) z (Y i z) = Y i (G.mul u z)) ∧
    (∀ i t, 0 < t → ∀ u,
      Y i (G.dilate t u) = t ^ (-1 : ℤ) • G.dilate t (Y i u)) ∧
    (∀ u, FreeAt (fun _ : Fin q => 1) s Y u ∧ StepSpansAt (fun _ : Fin q => 1) s Y u) ∧
    (∀ I : List (Fin q), s < wordWeight (fun _ : Fin q => 1) I → wordBracket Y I = 0) ∧
    (∀ j, wordBracket Y (B j) 0 = Pi.single j 1) ∧
    (∀ u, (∑ j, u j • wordBracket Y (B j) u) = u) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Θ z.1 z.2) (U ×ˢ U) ∧
    (∀ η ∈ U, (e η).source = U ∧
      (∀ ξ ∈ U, e η ξ = Θ η ξ) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (e η) (e η).source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (e η).symm (e η).target ∧ Θ η η = 0) ∧
    (∀ η ∈ U, ∀ u ∈ (e η).target,
      ∃ γ : ℝ → (Fin (n + m) → ℝ), γ 0 = η ∧ γ 1 = (e η).symm u ∧
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ O ∧
          HasDerivAt γ (∑ j, u j • wordBracket Xl (B j) (γ t)) t)) ∧
    (∀ η ∈ U, ∀ ξ ∈ U, Θ ξ η = -Θ η ξ) ∧
    IsOpen T ∧
    (∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => R I z.1 z.2) T) ∧
    (∀ I, I ≠ [] → ∀ η ∈ U,
      WeightedJet G.weight (1 - (wordWeight (fun _ : Fin q => 1) I : ℤ)) (R I η)) ∧
    (∀ I, I ≠ [] → wordWeight (fun _ : Fin q => 1) I ≤ s → ∀ η ∈ U, R I η 0 = 0) ∧
    (∀ I, I ≠ [] → ∀ η ∈ U, ∀ ξ ∈ U,
      fderiv ℝ (Θ η) ξ (wordBracket Xl I ξ) =
        wordBracket Y I (Θ η ξ) + R I η (Θ η ξ)) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) c U ∧ (∀ η ∈ U, 0 < c η) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωp z.1 z.2) T ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωm z.1 z.2) T ∧
    (∀ η ∈ U, ωp η 0 = 0 ∧ ωm η 0 = 0) ∧
    (∀ η ∈ U, ∀ u, ωm η u = ωp η (-u)) ∧
    (∀ η ∈ U, ∀ ξ ∈ U,
      0 < 1 + ωp η (Θ η ξ) ∧ 0 < 1 + ωm ξ (Θ η ξ) ∧
      absoluteJacobian (Θ η) ξ = (c η * (1 + ωp η (Θ η ξ)))⁻¹ ∧
      absoluteJacobian (fun ζ => Θ ζ ξ) η = (c ξ * (1 + ωm ξ (Θ η ξ)))⁻¹) ∧
    (∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ U →
      ∃ cmin cmax C r : ℝ, 0 < cmin ∧ 0 < cmax ∧ 0 < C ∧ 0 < r ∧
        (∀ η ∈ K, cmin ≤ c η ∧ c η ≤ cmax) ∧
        (∀ η ∈ K, ∀ u ∈ (e η).target, ‖u‖ < r →
          |ωp η u| ≤ C * ‖u‖ ∧ |ωm η u| ≤ C * ‖u‖)) ∧
    (∃ Cρ : ℝ, 1 ≤ Cρ ∧ ∀ η ∈ U, ∀ ξ ∈ U,
      ENNReal.ofReal (rsGauge G.weight G.weight_pos (Θ η ξ) / Cρ) ≤ controlDistance O (fun _ : Fin q => 1) Xl η ξ ∧
      controlDistance O (fun _ : Fin q => 1) Xl η ξ ≤ ENNReal.ofReal (Cρ * rsGauge G.weight G.weight_pos (Θ η ξ))) ∧
    (∀ V : TopologicalSpace.Opens (Fin (n + m) → ℝ), (V : Set _) = U →
      ∃ F : TestFunction V ℝ (⊤ : ℕ∞) →L_c[ℝ]
        TestFunction (⟨Ω, hΩ⟩ : TopologicalSpace.Opens (Fin n → ℝ)) ℝ (⊤ : ℕ∞),
        ∀ φ x, F φ x = ∫ t : Fin m → ℝ, φ (joinPoint x t)) ∧
    (∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ U →
      ∃ rstar cv Cv δ cf Cf : ℝ,
        0 < rstar ∧ 0 < cv ∧ 0 < Cv ∧ 0 < δ ∧ δ < 1 ∧ 0 < cf ∧ 0 < Cf ∧
        ∀ η ∈ K, ∀ r : ℝ, 0 < r → r < rstar →
          let Ul := rsBall O (fun _ : Fin q => 1) Xl η r
          let Vb := rsBall Ω (fun _ : Fin q => 1) X (basePoint η) r
          Ul ⊆ U ∧ MeasurableSet Ul ∧ MeasurableSet Vb ∧
          volume Ul ≠ ⊤ ∧ volume Vb ≠ ⊤ ∧
          0 < (volume Ul).toReal ∧ 0 < (volume Vb).toReal ∧
          cv * r ^ G.homogeneousDimension ≤ (volume Ul).toReal ∧
          (volume Ul).toReal ≤ Cv * r ^ G.homogeneousDimension ∧
          (∀ ξ ∈ Ul, controlDistance Ω (fun _ : Fin q => 1) X (basePoint η) (basePoint ξ) ≤
            controlDistance O (fun _ : Fin q => 1) Xl η ξ) ∧
          (∀ z : Fin n → ℝ,
            fiberVolume Ul z ≤ ENNReal.ofReal (Cf * (volume Ul).toReal / (volume Vb).toReal)) ∧
          (∀ z ∈ rsBall Ω (fun _ : Fin q => 1) X (basePoint η) (δ * r),
            ENNReal.ofReal (cf * (volume Ul).toReal / (volume Vb).toReal) ≤ fiberVolume Ul z))) :
    ∃ m : ℕ, n + m = freeDimension q s (fun _ : Fin q => 1) ∧
      Nonempty (LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m) := by
  obtain ⟨m, hm, P, U, G, B, v, Y, Θ, e, R, c, ωp, ωm, hvars, hU, hUc, hUO, hcenter,
    hsmooth, hfree, hbw, hbi, hbs, hgc, hinv, hYeq, hYsm, hYinv, hYhom, hYfree, hYnil,
    hYbo, hYexp, hθ, hchart, hrad, hanti, hT, hRs, hRw, hRo, hbr, hcs, hcp, hωps, hωms,
    hωo, hωme, hjac, hdb, hgcmp, hfib, hball⟩ := h
  refine ⟨m, hm, ⟨⟨P, U, G, B, v, Y, Θ, e, R, c, ωp, ωm, hvars, hU, hUc, hUO, hcenter,
    hsmooth, hfree, hbw, hbi, hbs, hgc, hinv, hYeq, hYsm, hYinv, ?_, hYfree, hYnil, hYbo,
    hYexp, hθ, hchart, hrad, hanti, hT, hRs, hRw, hRo, hbr, hcs, hcp, hωps, hωms, hωo,
    hωme, hjac, hdb, hgcmp, hfib, hball⟩⟩⟩
  intro i t ht u
  simpa using hYhom i t ht u

/-- The conclusion of the lifting theorem (drift) is a lifted chart.
The hypothesis `h` is, verbatim, the conclusion of the lifting theorem
`RothschildStein.exists_lift_approximation_drift` (alphabet `Fin (q + 1)`, weight two at the drift letter `0`), so that
`liftedChart_of_drift Ω hΩ X x₀ s (exists_lift_approximation_drift hn hq Ω hΩ X hX x₀ hx₀ s hs hspan)`
elaborates. The only non-syntactic step is the model dilation exponent, written
`t ^ (if i = 0 then (-2 : ℤ) else -1)` in the lifting theorem and `-(w i)` in `LiftedChart.model_field_homogeneous`. -/
theorem liftedChart_of_drift {n q : ℕ}
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (s : ℕ)
    (h :
    ∃ m : ℕ, n + m = freeDimension (q + 1) s (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) ∧
    ∃ P : Fin (q + 1) → Fin m → MvPolynomial (Fin (n + m)) ℝ,
    ∃ U : Set (Fin (n + m) → ℝ),
    ∃ G : HomogeneousGroup (n + m),
    ∃ B : Fin (n + m) → List (Fin (q + 1)),
    ∃ v : Fin (q + 1) → (Fin (n + m) → ℝ),
    ∃ Y : Fin (q + 1) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ),
    ∃ Θ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ),
    ∃ e : (Fin (n + m) → ℝ) → OpenPartialHomeomorph
      (Fin (n + m) → ℝ) (Fin (n + m) → ℝ),
    ∃ R : List (Fin (q + 1)) → (Fin (n + m) → ℝ) →
      (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ),
    ∃ c : (Fin (n + m) → ℝ) → ℝ,
    ∃ ωp ωm : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ,
    let Xl := triangularLift X P
    let O := {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω}
    let T := {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) |
      z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
    (∀ i l, ∀ j ∈ (P i l).vars, j.val < n + l.val) ∧
    IsOpen U ∧ IsCompact (closure U) ∧ closure U ⊆ O ∧
    joinPoint x₀ (0 : Fin m → ℝ) ∈ U ∧
    (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xl i) O) ∧
    (∀ ξ ∈ U, FreeAt (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Xl ξ ∧ StepSpansAt (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Xl ξ) ∧
    (∀ j, B j ≠ [] ∧ wordWeight (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) (B j) ≤ s ∧ G.weight j = wordWeight (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) (B j)) ∧
    LinearIndependent ℝ (fun j => (truncatedBracket (B j) : WordCoefficients (q + 1) s (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1))) ∧
    Submodule.span ℝ (Set.range (fun j =>
      (truncatedBracket (B j) : WordCoefficients (q + 1) s (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1)))) = formalSpan (q + 1) s (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) ∧
    (∀ i, (∑ j, v i j • (truncatedBracket (B j) : WordCoefficients (q + 1) s (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1))) =
      truncatedBracket [i]) ∧
    (∀ u, (fun j => MvPolynomial.eval u (G.inversePolynomial j)) = -u) ∧
    (∀ i u, Y i u = fderiv ℝ (G.mul u) 0 (v i)) ∧
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i)) ∧
    (∀ i u z, fderiv ℝ (G.mul u) z (Y i z) = Y i (G.mul u z)) ∧
    (∀ i t, 0 < t → ∀ u,
      Y i (G.dilate t u) = t ^ (if i = 0 then (-2 : ℤ) else -1) • G.dilate t (Y i u)) ∧
    (∀ u, FreeAt (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Y u ∧ StepSpansAt (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Y u) ∧
    (∀ I : List (Fin (q + 1)), s < wordWeight (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) I → wordBracket Y I = 0) ∧
    (∀ j, wordBracket Y (B j) 0 = Pi.single j 1) ∧
    (∀ u, (∑ j, u j • wordBracket Y (B j) u) = u) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Θ z.1 z.2) (U ×ˢ U) ∧
    (∀ η ∈ U, (e η).source = U ∧
      (∀ ξ ∈ U, e η ξ = Θ η ξ) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (e η) (e η).source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (e η).symm (e η).target ∧ Θ η η = 0) ∧
    (∀ η ∈ U, ∀ u ∈ (e η).target,
      ∃ γ : ℝ → (Fin (n + m) → ℝ), γ 0 = η ∧ γ 1 = (e η).symm u ∧
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ O ∧
          HasDerivAt γ (∑ j, u j • wordBracket Xl (B j) (γ t)) t)) ∧
    (∀ η ∈ U, ∀ ξ ∈ U, Θ ξ η = -Θ η ξ) ∧
    IsOpen T ∧
    (∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => R I z.1 z.2) T) ∧
    (∀ I, I ≠ [] → ∀ η ∈ U,
      WeightedJet G.weight (1 - (wordWeight (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) I : ℤ)) (R I η)) ∧
    (∀ I, I ≠ [] → wordWeight (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) I ≤ s → ∀ η ∈ U, R I η 0 = 0) ∧
    (∀ I, I ≠ [] → ∀ η ∈ U, ∀ ξ ∈ U,
      fderiv ℝ (Θ η) ξ (wordBracket Xl I ξ) =
        wordBracket Y I (Θ η ξ) + R I η (Θ η ξ)) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) c U ∧ (∀ η ∈ U, 0 < c η) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωp z.1 z.2) T ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωm z.1 z.2) T ∧
    (∀ η ∈ U, ωp η 0 = 0 ∧ ωm η 0 = 0) ∧
    (∀ η ∈ U, ∀ u, ωm η u = ωp η (-u)) ∧
    (∀ η ∈ U, ∀ ξ ∈ U,
      0 < 1 + ωp η (Θ η ξ) ∧ 0 < 1 + ωm ξ (Θ η ξ) ∧
      absoluteJacobian (Θ η) ξ = (c η * (1 + ωp η (Θ η ξ)))⁻¹ ∧
      absoluteJacobian (fun ζ => Θ ζ ξ) η = (c ξ * (1 + ωm ξ (Θ η ξ)))⁻¹) ∧
    (∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ U →
      ∃ cmin cmax C r : ℝ, 0 < cmin ∧ 0 < cmax ∧ 0 < C ∧ 0 < r ∧
        (∀ η ∈ K, cmin ≤ c η ∧ c η ≤ cmax) ∧
        (∀ η ∈ K, ∀ u ∈ (e η).target, ‖u‖ < r →
          |ωp η u| ≤ C * ‖u‖ ∧ |ωm η u| ≤ C * ‖u‖)) ∧
    (∃ Cρ : ℝ, 1 ≤ Cρ ∧ ∀ η ∈ U, ∀ ξ ∈ U,
      ENNReal.ofReal (rsGauge G.weight G.weight_pos (Θ η ξ) / Cρ) ≤ controlDistance O (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) Xl η ξ ∧
      controlDistance O (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) Xl η ξ ≤ ENNReal.ofReal (Cρ * rsGauge G.weight G.weight_pos (Θ η ξ))) ∧
    (∀ V : TopologicalSpace.Opens (Fin (n + m) → ℝ), (V : Set _) = U →
      ∃ F : TestFunction V ℝ (⊤ : ℕ∞) →L_c[ℝ]
        TestFunction (⟨Ω, hΩ⟩ : TopologicalSpace.Opens (Fin n → ℝ)) ℝ (⊤ : ℕ∞),
        ∀ φ x, F φ x = ∫ t : Fin m → ℝ, φ (joinPoint x t)) ∧
    (∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ U →
      ∃ rstar cv Cv δ cf Cf : ℝ,
        0 < rstar ∧ 0 < cv ∧ 0 < Cv ∧ 0 < δ ∧ δ < 1 ∧ 0 < cf ∧ 0 < Cf ∧
        ∀ η ∈ K, ∀ r : ℝ, 0 < r → r < rstar →
          let Ul := rsBall O (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) Xl η r
          let Vb := rsBall Ω (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) X (basePoint η) r
          Ul ⊆ U ∧ MeasurableSet Ul ∧ MeasurableSet Vb ∧
          volume Ul ≠ ⊤ ∧ volume Vb ≠ ⊤ ∧
          0 < (volume Ul).toReal ∧ 0 < (volume Vb).toReal ∧
          cv * r ^ G.homogeneousDimension ≤ (volume Ul).toReal ∧
          (volume Ul).toReal ≤ Cv * r ^ G.homogeneousDimension ∧
          (∀ ξ ∈ Ul, controlDistance Ω (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) X (basePoint η) (basePoint ξ) ≤
            controlDistance O (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) Xl η ξ) ∧
          (∀ z : Fin n → ℝ,
            fiberVolume Ul z ≤ ENNReal.ofReal (Cf * (volume Ul).toReal / (volume Vb).toReal)) ∧
          (∀ z ∈ rsBall Ω (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) X (basePoint η) (δ * r),
            ENNReal.ofReal (cf * (volume Ul).toReal / (volume Vb).toReal) ≤ fiberVolume Ul z))) :
    ∃ m : ℕ, n + m = freeDimension (q + 1) s (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) ∧
      Nonempty (LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m) := by
  obtain ⟨m, hm, P, U, G, B, v, Y, Θ, e, R, c, ωp, ωm, hvars, hU, hUc, hUO, hcenter,
    hsmooth, hfree, hbw, hbi, hbs, hgc, hinv, hYeq, hYsm, hYinv, hYhom, hYfree, hYnil,
    hYbo, hYexp, hθ, hchart, hrad, hanti, hT, hRs, hRw, hRo, hbr, hcs, hcp, hωps, hωms,
    hωo, hωme, hjac, hdb, hgcmp, hfib, hball⟩ := h
  refine ⟨m, hm, ⟨⟨P, U, G, B, v, Y, Θ, e, R, c, ωp, ωm, hvars, hU, hUc, hUO, hcenter,
    hsmooth, hfree, hbw, hbi, hbs, hgc, hinv, hYeq, hYsm, hYinv, ?_, hYfree, hYnil, hYbo,
    hYexp, hθ, hchart, hrad, hanti, hT, hRs, hRw, hRo, hbr, hcs, hcp, hωps, hωms, hωo,
    hωme, hjac, hdb, hgcmp, hfib, hball⟩⟩⟩
  intro i t ht u
  have h1 := hYhom i t ht u
  by_cases hi : i = 0 <;> simpa [hi] using h1

end RothschildStein.P1
