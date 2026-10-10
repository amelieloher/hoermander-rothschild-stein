-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.HeatAdjoint
public import RothschildStein.P2.SobolevInterpolationTranspose
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Classical equations for smooth weak heat solutions

Local integration by parts moves the sum of squares from compact tests to the
smooth solution. Distribution uniqueness and continuity give the equation at every point.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators

namespace HeatKernel

open RothschildStein Hormander.Interface

/-- The transpose of a smooth sum-of-squares operator preserves local smoothness. -/
theorem contDiffOn_sumSquaresWithDriftTranspose {q n : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : (Fin n → ℝ) → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sumSquaresWithDriftTranspose X u) Ω := by
  have htrans (V : (Fin n → ℝ) → Fin n → ℝ)
      (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
      (f : (Fin n → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fieldTranspose V f) Ω := by
    exact (P1.contDiffOn_euclideanDivergence Ω _ (hf.smul hV)).neg
  exact (htrans _ (hX 0) u hu).add
    (ContDiffOn.sum fun i _ => htrans _ (hX i.succ) _ (htrans _ (hX i.succ) u hu))

/-- A smooth function annihilating the operator on tests solves its transpose pointwise. -/
theorem sumSquaresWithDriftTranspose_eq_zero_of_integral_identity {q n : ℕ}
    (Ω : Opens (Fin n → ℝ)) (X : Fin (q + 1) → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : (Fin n → ℝ) → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    (hweak : ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in (Ω : Set (Fin n → ℝ)), u x * sumSquaresWithDrift X φ x) = 0) :
    ∀ x ∈ Ω, sumSquaresWithDriftTranspose X u x = 0 := by
  have hc := (contDiffOn_sumSquaresWithDriftTranspose Ω X hX u hu).continuousOn
  have hae := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hc.locallyIntegrableOn Ω.isOpen.measurableSet) (fun φ hφ hcompact hsupp => by
      let ψ : TestFunction Ω ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hcompact, hsupp⟩
      have hibp := P2.integral_mul_sumSquaresWithDrift Ω X hX u
        (hu.of_le (by simp)) ψ
      have hz : (∫ x in (Ω : Set (Fin n → ℝ)),
          sumSquaresWithDriftTranspose X u x * φ x) = 0 :=
        hibp.symm.trans (hweak φ hφ hcompact hsupp)
      have hset : (∫ x in (Ω : Set (Fin n → ℝ)), φ x * sumSquaresWithDriftTranspose X u x) =
          ∫ x, φ x * sumSquaresWithDriftTranspose X u x := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h)), zero_mul]
      simpa only [smul_eq_mul, ← hset, mul_comm] using hz)
  have heq : sumSquaresWithDriftTranspose X u =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))]
      (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    exact hx hxΩ
  exact Measure.eqOn_open_of_ae_eq heq Ω.isOpen hc continuousOn_const

/-- The transpose of divergence-free fields is the sum of squares minus the drift. -/
theorem sumSquaresWithDriftTranspose_eq_of_divergence_zero {q n : ℕ}
    (Ω : Opens (Fin n → ℝ)) (X : Fin (q + 1) → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hdiv : ∀ i x, euclideanDivergence (X i) x = 0)
    (u : (Fin n → ℝ) → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    {x : Fin n → ℝ} (hx : x ∈ Ω) :
    sumSquaresWithDriftTranspose X u x =
      (∑ i : Fin q, fieldDerivative (X i.succ) (fieldDerivative (X i.succ) u) x) -
        fieldDerivative (X 0) u x := by
  have hfun (i : Fin (q + 1)) : euclideanDivergence (X i) = fun _ => 0 := funext (hdiv i)
  simpa [hfun, fieldDerivative] using
    P2.sumSquaresWithDriftTranspose_apply_of_contDiffAt Ω X hX u hx
      ((hu.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le (by simp))

/-- A smooth weak solution of the horizontal heat equation satisfies it at every positive time. -/
theorem fderiv_time_eq_horizontal_squares_of_integral_identity {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (u : (Fin (1 + n) → ℝ) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x | 0 < x 0})
    (hweak : ∀ φ : (Fin (1 + n) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ {x | 0 < x 0} →
      (∫ x in {x | 0 < x 0}, u x *
        (fderiv ℝ φ x (leftCoordinateInclusion 1 n (fun _ => 1)) +
          ∑ i : Fin q, fderiv ℝ
            (fun y => fderiv ℝ φ y (liftRightField 1 (G.horizontalFields hq i) y)) x
            (liftRightField 1 (G.horizontalFields hq i) x))) = 0)
    {x : Fin (1 + n) → ℝ} (hx : 0 < x 0) :
    fderiv ℝ u x (leftCoordinateInclusion 1 n (fun _ => 1)) =
      ∑ i : Fin q, fderiv ℝ
        (fun y => fderiv ℝ u y (liftRightField 1 (G.horizontalFields hq i) y)) x
        (liftRightField 1 (G.horizontalFields hq i) x) := by
  let Ω : Opens (Fin (1 + n) → ℝ) := ⟨{x | 0 < x 0}, isOpen_positive_time n⟩
  let X := timeSpaceFields 1 (G.horizontalFields hq)
  have hderiv (V : (Fin (1 + n) → ℝ) → Fin (1 + n) → ℝ)
      (f : (Fin (1 + n) → ℝ) → ℝ) :
      fieldDerivative V f = fun y => fderiv ℝ f y (V y) := rfl
  have hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω :=
    fun i => (contDiff_timeSpaceFields 1 _ (G.horizontalFields_contDiff hq) i).contDiffOn
  have hdiv : ∀ i z, euclideanDivergence (X i) z = 0 := by
    apply euclideanDivergence_timeSpaceFields 1 _ (G.horizontalFields_contDiff hq)
    intro j z
    simpa only [HomogeneousGroup.horizontalFields, RothschildStein.G2.canonicalField_eq_leftField]
      using RothschildStein.G2.leftField_divergence_zero G (basisVec (Fin.castLE hq j)) z
  have hz := sumSquaresWithDriftTranspose_eq_zero_of_integral_identity Ω X hX u hu
    (fun φ hφ hc hs => by
      simpa only [Ω, Opens.coe_mk, X, sumSquaresWithDrift, hderiv, timeSpaceFields_zero,
        timeSpaceFields_succ] using hweak φ hφ hc hs) x hx
  rw [sumSquaresWithDriftTranspose_eq_of_divergence_zero Ω X hX hdiv u hu hx] at hz
  simpa only [X, hderiv, timeSpaceFields_zero, timeSpaceFields_succ] using
    (sub_eq_zero.mp hz).symm

end HeatKernel
