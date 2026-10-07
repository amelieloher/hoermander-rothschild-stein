-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingBridge
public import RothschildStein.S.WeakIntrinsicWords

/-!
# Weak-to-intrinsic regularity: continuous weak derivatives are intrinsic

BB p. 609-610 (the converse needed alongside Prop 2.22, p. 87). The Lean content is the proved weak-to-intrinsic derivative result
package `RothschildStein.S.hasIntrinsicDeriv_of_continuous_weak_derivative` (a continuous weak
`X`-derivative is the intrinsic derivative, by differentiation along every integral curve)
and its word form `RothschildStein.S.hasIntrinsicWordDeriv_of_continuous_weak_subwords`. This file
states them for the alphabets `Fin k` of P2 (drift at index `0` allowed: no drift restriction
is used), adds the flow-line identity `u(Φ_t x) - u(x) = ∫_0^t g(Φ_s x) ds`, and combines the word
form with the cylinder descent for the Hölder branch of Thm 11.62
(`hasIntrinsicWordDeriv_descent`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2
variable {n : ℕ}

/-- Continuous weak word derivatives, for every subword, are the iterated intrinsic derivatives (the successive application of the one-letter statement to each word
derivative; alphabet `Fin k`, drift allowed; BB pp. 87-90). -/
theorem hasIntrinsicWordDeriv_of_continuous_weak_words {k : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) (I : List (Fin k))
    (f : (Fin n → ℝ) → ℝ) (jet : List (Fin k) → (Fin n → ℝ) → ℝ) (hzero : jet [] = f)
    (hw : ∀ J, J.Sublist I → hasWeakWordDeriv X Ω J f (jet J))
    (hc : ∀ J, J.Sublist I → ContinuousOn (jet J) (Ω : Set (Fin n → ℝ))) :
    hasIntrinsicWordDeriv X Ω I f (jet I) :=
  RothschildStein.S.hasIntrinsicWordDeriv_of_continuous_weak_subwords Ω X hX I f jet hzero hw hc

/-- The Hölder branch of Thm 11.62 on a cylinder. If, for every
subword `J` of `I`, the continuous function `w` representing `T̃` has the continuous weak lifted
derivative `X̃_J w = gJ J` on the cylinder `A × B`, then the slice `x ↦ w(x, t₀)` represents `T` on
`A` and has the intrinsic word derivative `x ↦ gJ I (x, t₀)` (BB pp. 609-610). -/
theorem hasIntrinsicWordDeriv_descent {k m : ℕ} {A : Opens (Fin n → ℝ)} {B : Opens (Fin m → ℝ)}
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i)
      (cylinder A B : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (A : Set (Fin n → ℝ)))
    (S : FiberSetting (cylinder A B) A) {η : TestFunction B ℝ (⊤ : ℕ∞)}
    (hη : ∫ t : Fin m → ℝ, η t = 1) (T : Distribution A ℝ (⊤ : ℕ∞))
    {w : (Fin (n + m) → ℝ) → ℝ}
    (hw : LocallyIntegrableOn w (cylinder A B : Set (Fin (n + m) → ℝ)) volume)
    (hT : ∀ ψ : TestFunction (cylinder A B) ℝ (⊤ : ℕ∞),
      T (S.test ψ) = Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞) ψ)
    (I : List (Fin k)) (gJ : List (Fin k) → (Fin (n + m) → ℝ) → ℝ) (hg0 : gJ [] = w)
    (hg : ∀ J, J.Sublist I → hasWeakWordDeriv (triangularLift X P) (cylinder A B) J w (gJ J))
    (hgc : ∀ J, J.Sublist I → ContinuousOn (gJ J) (cylinder A B : Set (Fin (n + m) → ℝ)))
    {t₀ : Fin m → ℝ} (ht₀ : t₀ ∈ (B : Set (Fin m → ℝ))) :
    representsDistribution A T (fun x => w (joinPoint x t₀)) ∧
      hasIntrinsicWordDeriv X A I (fun x => w (joinPoint x t₀)) (fun x => gJ I (joinPoint x t₀)) := by
  have hwc : ContinuousOn w (cylinder A B : Set (Fin (n + m) → ℝ)) := by
    have := hgc [] (List.nil_sublist I)
    rwa [hg0] at this
  have key := fun J (hJ : J.Sublist I) =>
    hasWeakWordDeriv_descent_continuous X P hXt hX S hη T hw hT J (hg J hJ) hwc (hgc J hJ) ht₀
  refine ⟨(key [] (List.nil_sublist I)).2.2.1, ?_⟩
  refine hasIntrinsicWordDeriv_of_continuous_weak_words A X hX I _
    (fun J x => gJ J (joinPoint x t₀)) ?_ (fun J hJ => (key J hJ).2.2.2.1)
    (fun J hJ => (key J hJ).2.1)
  rw [hg0]

end RothschildStein.P2
