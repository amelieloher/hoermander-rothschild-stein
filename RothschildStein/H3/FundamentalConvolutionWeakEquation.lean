-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.KernelPotential
public import RothschildStein.H3.WeakOperatorPairing
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped BigOperators

/-- every compact smooth source and the actual fundamental
potential satisfy the exact local transpose equation used in the weak-jet
limit. No approximant equation or operator representative is assumed. -/
theorem fundamental_convolution_weak_equation {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (Ω : Opens (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsf : HasCompactSupport f)
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)), f x*ψ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), G2.groupConvolution G f K x*
        sumSquaresWithDriftTranspose H.fields ψ x := by
  let v := G2.groupConvolution G f K
  let φ : TestFunction (⊤ : Opens (Fin n → ℝ)) ℝ (⊤ : ℕ∞) := ⟨f,hf,hsf,subset_univ _⟩
  have hconv : v = G.potential K φ := by
    dsimp only [v]
    funext x
    rw [G2.groupConvolution_eq_integral]
    rfl
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := by rw [hconv]; exact K.potential_smooth φ
  have heq : sumSquaresWithDrift H.fields v = f := by rw [hconv]; exact K.potential_equation φ
  have hX := fun i => (H.fields_smooth G i).contDiffOn (s := (Ω : Set (Fin n → ℝ)))
  have hg : ∀ i, hasWeakWordDeriv H.fields Ω [i] v (fieldDerivative (H.fields i) v) := by
    intro i
    simpa only [wordDerivative] using S.hasWeakWordDeriv_classical Ω H.fields hX [i] v hv.contDiffOn
  have hh : ∀ i : Fin q, hasWeakWordDeriv H.fields Ω [i.succ,i.succ] v
      (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) v)) := by
    intro i
    simpa only [wordDerivative] using
      S.hasWeakWordDeriv_classical Ω H.fields hX [i.succ,i.succ] v hv.contDiffOn
  have hb := integral_sumSquaresWithDrift_weak_jets H.fields Ω hX v
    (fun i => fieldDerivative (H.fields i) v)
    (fun i => fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) v)) hg hh ψ
  change (∫ x in (Ω : Set (Fin n → ℝ)), sumSquaresWithDrift H.fields v x*ψ x) = _ at hb
  rw [heq] at hb
  exact hb

end RothschildStein.H3
