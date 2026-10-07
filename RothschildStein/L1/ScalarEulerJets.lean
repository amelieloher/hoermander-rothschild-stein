-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.ScalarEulerDerivative
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.L1

/-- Each ordinary coordinate derivative contributes one to the Euler
coefficient. This is an identity of actual smooth derivatives. -/
theorem rsPartial_scalarJetEuler {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (J : List (Fin N)) : ∀ x ∈ Ω,
    rsPartial J (scalarJetEuler f) x =
      scalarJetEuler (rsPartial J f) x + (J.length : ℝ) * rsPartial J f x := by
  induction J with
  | nil => intro x hx; simp only [rsPartial, List.length_nil, Nat.cast_zero, zero_mul, add_zero]
  | cons j J ih =>
    intro x hx
    have hs := rsPartial_contDiffOn Ω J f hf
    have hE := scalarJetEuler_contDiffOn Ω (rsPartial J f) hs
    have hd := (hs.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
    have hdE := (hE.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
    have he : rsPartial J (scalarJetEuler f) =ᶠ[𝓝 x]
        (fun y => scalarJetEuler (rsPartial J f) y + (J.length : ℝ) * rsPartial J f y) :=
      Filter.Eventually.mono (Ω.isOpen.mem_nhds hx) (fun y hy => ih y hy)
    change fderiv ℝ (rsPartial J (scalarJetEuler f)) x (Pi.single j 1) = _
    have hdL : DifferentiableAt ℝ (fun y => (J.length : ℝ) * rsPartial J f y) x :=
      hd.const_mul (J.length : ℝ)
    rw [he.fderiv_eq, fderiv_fun_add hdE hdL,
      fderiv_const_mul hd, add_apply, smul_apply]
    change rsPartial [j] (scalarJetEuler (rsPartial J f)) x +
      (J.length : ℝ) * rsPartial (j :: J) f x = _
    rw [rsPartial_scalarJetEuler_single Ω (rsPartial J f) hs j hx]
    change scalarJetEuler (rsPartial (j :: J) f) x + rsPartial (j :: J) f x +
      (J.length : ℝ) * rsPartial (j :: J) f x =
      scalarJetEuler (rsPartial (j :: J) f) x + ((j :: J).length : ℝ) * rsPartial (j :: J) f x
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- On the ordinary jet of order length J, the
Euler operator multiplies by the strictly positive scalar 2 + length J. -/
theorem rsPartial_scalarJetEuler_zero {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (J : List (Fin N)) :
    rsPartial J (scalarJetEuler f) 0 = (2 + (J.length : ℝ)) * rsPartial J f 0 := by
  rw [rsPartial_scalarJetEuler Ω f hf J 0 h0]
  simp only [scalarJetEuler, fieldDerivative, id_eq, map_zero]
  ring

/-- Euler inversion preserves precisely the forbidden finite scalar jets. -/
theorem scalarJetVanishing_scalarJetEuler_iff {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) (ω : Fin N → ℕ) (a : ℝ)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) :
    scalarJetVanishing ω a p (scalarJetEuler f) ↔ scalarJetVanishing ω a p f := by
  constructor
  · intro h J hJ hw
    have he := h J hJ hw
    rw [rsPartial_scalarJetEuler_zero Ω h0 f hf J] at he
    exact (mul_eq_zero.mp he).resolve_left (by positivity)
  · intro h J hJ hw
    rw [rsPartial_scalarJetEuler_zero Ω h0 f hf J, h J hJ hw, mul_zero]
end RothschildStein.L1
