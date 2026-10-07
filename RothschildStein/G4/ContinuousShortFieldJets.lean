-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ContinuousSpatialBracketJets
public import RothschildStein.G4.ShortFields

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Actual word-bracket spatial jets are jointly continuous
under finitely many jointly continuous primitive spatial jets. The
external parameter is never differentiated (BB p. 452). -/
theorem wordBracket_spatial_jet_joint_continuity {P : Type*} {m n : ℕ}
    [TopologicalSpace P] {U : Set P} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ p ∈ U, ∀ J, ContDiffOn ℝ (⊤ : ℕ∞) (X p J) Ω)
    (I : List (Fin m)) (j : ℕ)
    (hjets : ∀ J, ∀ i ≤ j + I.length,
      ContinuousOn (fun q : P × (Fin n → ℝ) => iteratedFDeriv ℝ i (X q.1 J) q.2) (U ×ˢ Ω)) :
    ContinuousOn (fun q : P × (Fin n → ℝ) =>
      iteratedFDeriv ℝ j (wordBracket (X q.1) I) q.2) (U ×ˢ Ω) := by
  induction I generalizing j with
  | nil =>
    change ContinuousOn (fun q : P × (Fin n → ℝ) =>
      iteratedFDeriv ℝ j (fun _ : Fin n → ℝ => (0 : Fin n → ℝ)) q.2) (U ×ˢ Ω)
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
      (continuousOn_const : ContinuousOn (fun _ : P × (Fin n → ℝ) =>
        (0 : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin n → ℝ) (Fin n → ℝ))) (U ×ˢ Ω))
  | cons J I ih =>
    cases I with
    | nil =>
      simpa only [wordBracket] using hjets J j (by simp)
    | cons J' I =>
      have htail : ∀ i ≤ j + 1, ContinuousOn
          (fun q : P × (Fin n → ℝ) => iteratedFDeriv ℝ i (wordBracket (X q.1) (J' :: I)) q.2)
          (U ×ˢ Ω) := by
        intro i hi
        exact ih i (fun A r hr => hjets A r (by simp only [List.length_cons] at *; omega))
      exact spatial_jet_lieBracket_continuity hΩ j (fun p => X p J)
        (fun p => wordBracket (X p) (J' :: I)) (fun p hp => hX p hp J)
        (fun p hp => G1.wordBracket_contDiffOn hΩ (X p) (hX p hp) (J' :: I))
        (fun i hi => hjets J i (by simp only [List.length_cons]; omega)) htail

/-- Primitive joint spatial jets through order s+1 supply the
actual short-field values and first spatial derivatives required by the
compact external-family flow/injectivity interface (BB p. 452). -/
theorem shortField_joint_continuity_of_spatial_jets {P : Type*} {m n s : ℕ}
    [TopologicalSpace P] {U : Set P} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (w : Fin m → ℕ+) (X : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ p ∈ U, ∀ J, ContDiffOn ℝ (⊤ : ℕ∞) (X p J) Ω)
    (hjets : ∀ J, ∀ i ≤ s + 1,
      ContinuousOn (fun q : P × (Fin n → ℝ) => iteratedFDeriv ℝ i (X q.1 J) q.2) (U ×ˢ Ω))
    (I : ShortWord w s) :
    ContinuousOn (fun q : P × (Fin n → ℝ) => shortField w (X q.1) I q.2) (U ×ˢ Ω) ∧
    ContinuousOn (fun q : P × (Fin n → ℝ) =>
      fderiv ℝ (shortField w (X q.1) I) q.2) (U ×ˢ Ω) := by
  have hlen : I.val.length ≤ s :=
    (G3.length_le_weight w I.val).trans ((mem_shortWordFamily_iff w I.val).mp I.property).2
  have h0 := wordBracket_spatial_jet_joint_continuity hΩ X hX I.val 0
    (fun J i hi => hjets J i (by omega))
  have h1 := wordBracket_spatial_jet_joint_continuity hΩ X hX I.val 1
    (fun J i hi => hjets J i (by omega))
  have hd0 := spatial_derivative_jet_continuity 0 (fun p => wordBracket (X p) I.val) h1
  exact ⟨spatial_jet_zero_continuity_values (fun p => wordBracket (X p) I.val) h0,
    spatial_jet_zero_continuity_values (fun p => fderiv ℝ (wordBracket (X p) I.val)) hd0⟩

end RothschildStein.G4
