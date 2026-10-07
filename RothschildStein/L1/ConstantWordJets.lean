-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LocalFrozenWordJets
public import RothschildStein.P1.BracketExpansion
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Constant directional differentiation evaluates the next ordinary jet. -/
theorem iteratedFDeriv_const_fieldDerivative_on {N k : ℕ}
    (Ω : Opens (Fin N → ℝ)) (u : (Fin N → ℝ) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) {x : Fin N → ℝ} (hx : x ∈ Ω)
    (z : Fin N → ℝ) (v : Fin k → (Fin N → ℝ)) :
    iteratedFDeriv ℝ k (fieldDerivative (fun _ => z) u) x v =
      iteratedFDeriv ℝ (k+1) u x (Fin.snoc v z) := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ u) Ω := hu.fderiv_of_isOpen Ω.isOpen (by simp)
  have he := iteratedFDerivWithin_clm_apply_const_apply Ω.isOpen.uniqueDiffOn hd
    (i := k) (by simp) hx (u := z) (m := v)
  simp only [iteratedFDerivWithin_of_isOpen _ Ω.isOpen hx] at he
  change iteratedFDeriv ℝ k (fun y => fderiv ℝ u y z) x v = _
  rw [he,iteratedFDeriv_succ_apply_right]
  simp

/-- An ordered product of constant fields
is the corresponding ordinary multilinear derivative, with no jet hypotheses. -/
theorem wordDerivative_constant_eq_iteratedFDeriv {a N r : ℕ}
    (Ω : Opens (Fin N → ℝ)) (V : Fin a → (Fin N → ℝ))
    (u : (Fin N → ℝ) → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (q : Fin r → Fin a) :
    wordDerivative (fun i _ => V i) (List.ofFn q) u x =
      iteratedFDeriv ℝ r u x (fun i => V (q i)) := by
  induction r generalizing u with
  | zero => simp [List.ofFn_zero,wordDerivative,iteratedFDeriv_zero_apply]
  | succ r ih =>
    rw [List.ofFn_succ',List.concat_eq_append,P1.wordDerivative_append]
    change wordDerivative (fun i _ => V i) (List.ofFn (fun i => q i.castSucc))
      (fieldDerivative (fun _ => V (q (Fin.last r))) u) x = _
    have hg : ContDiffOn ℝ (⊤ : ℕ∞)
        (fieldDerivative (fun _ => V (q (Fin.last r))) u) Ω :=
      (hu.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const
    rw [ih (fieldDerivative (fun _ => V (q (Fin.last r))) u) hg (fun i => q i.castSucc)]
    rw [iteratedFDeriv_const_fieldDerivative_on Ω u hu hx]
    congr 1
    exact Fin.snoc_init_self (fun i => V (q i))
end RothschildStein.L1
