-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetAddition
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Ordinary coordinate partials commute with negation. -/
theorem rsPartial_neg {N : ℕ} (J : List (Fin N))
    (f : (Fin N → ℝ) → ℝ) : rsPartial J (fun u => -f u) = fun u => -rsPartial J f u := by
  induction J with
  | nil => rfl
  | cons j J ih =>
    simp only [rsPartial, ih, fderiv_fun_neg, neg_apply]

/-- Negation preserves the finite weighted jet class. -/
theorem scalarJetClass_neg {N p : ℕ} {Ω : Set (Fin N → ℝ)} {ω : Fin N → ℕ}
    {a : ℝ} {f : (Fin N → ℝ) → ℝ} (hf : scalarJetClass Ω ω a p f) :
    scalarJetClass Ω ω a p (fun u => -f u) := by
  refine ⟨hf.1.neg, ?_⟩
  intro J hJ hw
  rw [rsPartial_neg]
  change -rsPartial J f 0 = 0
  rw [hf.2 J hJ hw, neg_zero]

/-- Subtraction preserves the finite weighted jet class. -/
theorem scalarJetClass_sub {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a : ℝ}
    {f g : (Fin N → ℝ) → ℝ} (hf : scalarJetClass Ω ω a p f)
    (hg : scalarJetClass Ω ω a p g) :
    scalarJetClass Ω ω a p (fun u => f u - g u) := by
  simpa only [sub_eq_add_neg] using scalarJetClass_add Ω h0 hf (scalarJetClass_neg hg)

/-- Ordinary order may be lowered without changing the threshold. -/
theorem fieldJetClass_order_mono {N p q : ℕ} {Ω : Set (Fin N → ℝ)}
    {ω : Fin N → ℕ} {a : ℝ} {R : (Fin N → ℝ) → (Fin N → ℝ)}
    (hR : fieldJetClass Ω ω a p R) (hqp : q ≤ p) : fieldJetClass Ω ω a q R :=
  ⟨hR.1, fieldJetVanishing_mono hR.2 le_rfl hqp⟩
end RothschildStein.L1
