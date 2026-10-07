-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.OneVariableLift
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- The lifted coefficient domain is the open cylinder over the
original coefficient domain (BB Proposition 10.17). -/
def oneVariableLiftDomain {n : ℕ} (Ω : Opens (Fin n → ℝ)) :
    Opens (Fin (n+1) → ℝ) :=
  ⟨(P1.paddingBaseCLM n 1) ⁻¹' (Ω : Set (Fin n → ℝ)),
    Ω.isOpen.preimage (P1.paddingBaseCLM n 1).continuous⟩

/-- A smooth field and smooth base-dependent vertical coefficient
produce an actual smooth lifted field on the open cylinder. -/
theorem oneVariableLift_contDiffOn {a n : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : Fin a → (Fin n → ℝ) → ℝ)
    (hu : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (u i) Ω) (i : Fin a) :
    ContDiffOn ℝ (⊤ : ℕ∞) (oneVariableLift X u i) (oneVariableLiftDomain Ω) := by
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (P1.paddingBaseCLM n 1)
      (oneVariableLiftDomain Ω) := (P1.paddingBaseCLM n 1).contDiff.contDiffOn
  have hx := (hX i).comp hb (fun _ h => h)
  have hv := (hu i).comp hb (fun _ h => h)
  have hz : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun ξ => (fun _ : Fin 1 => u i (P1.paddingBaseCLM n 1 ξ)))
      (oneVariableLiftDomain Ω) := contDiffOn_pi.mpr (fun _ => hv)
  have hj := (P1.paddingJoinCLM n 1).contDiff.comp_contDiffOn (hx.prodMk hz)
  change ContDiffOn ℝ (⊤ : ℕ∞)
    (fun ξ => joinPoint (X i (P1.paddingBaseCLM n 1 ξ))
      (fun _ : Fin 1 => u i (P1.paddingBaseCLM n 1 ξ))) (oneVariableLiftDomain Ω)
  simpa only [Function.comp_def,P1.paddingJoinCLM_apply] using hj
end RothschildStein.L1
