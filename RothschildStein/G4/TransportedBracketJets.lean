-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.TransportedBracket
public import RothschildStein.G1.BracketAlgebra
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- Every actual time derivative of the transported field is the
signed transport of the corresponding iterated adjoint bracket. The open
finite trajectory buffer is explicit (BB Lemma 9.48, pp. 442–443). -/
theorem localFlow_transported_iteratedDeriv
    {N : ℕ} {Ω U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (Z Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {T : Set ℝ} (hT : IsOpen T)
    (hTτ : T ⊆ Ioo (-τ) τ) (hend : ∀ s ∈ T, Φ (x, -s) ∈ U)
    (k : ℕ) {t : ℝ} (ht : t ∈ T) :
    iteratedDeriv k (fun v => (fderiv ℝ (fun y => Φ (y, v)) (Φ (x, -v)))
      (Y (Φ (x, -v)))) t = (-1 : ℝ) ^ k •
        (fderiv ℝ (fun y => Φ (y, t)) (Φ (x, -t)))
          (((VectorField.lieBracket ℝ Z)^[k] Y) (Φ (x, -t))) := by
  induction k generalizing Y with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_smul, Function.iterate_zero, id_eq]
  | succ k ih =>
    have he : (deriv (fun v => (fderiv ℝ (fun y => Φ (y, v)) (Φ (x, -v)))
        (Y (Φ (x, -v))))) =ᶠ[𝓝 t]
        (fun v => -(fderiv ℝ (fun y => Φ (y, v)) (Φ (x, -v)))
          (VectorField.lieBracket ℝ Z Y (Φ (x, -v)))) := by
      filter_upwards [hT.mem_nhds ht] with s hs
      exact (localFlow_transported_hasDerivAt hΩ hU Z Y hZ hY hτ Φ hc hΦ hx
        (hTτ hs) (hend s hs)).deriv
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq k, iteratedDeriv_fun_neg,
      ih (VectorField.lieBracket ℝ Z Y) (RothschildStein.G1.bracket_contDiffOn hΩ hZ hY)]
    rw [Function.iterate_succ_apply, pow_succ, mul_smul, neg_one_smul, smul_neg]

end RothschildStein.G4
