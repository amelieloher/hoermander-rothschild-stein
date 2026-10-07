-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.BracketAlgebra
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.L1

/-- Recenter the coefficient domain at the chosen base point. -/
def translatedDomain {n : ℕ} (Ω : Opens (Fin n → ℝ)) (t : Fin n → ℝ) :
    Opens (Fin n → ℝ) :=
  ⟨(fun x => x+t) ⁻¹' (Ω : Set (Fin n → ℝ)),
    Ω.isOpen.preimage (continuous_id.add continuous_const)⟩

/-- The coefficients of a vector field in translated coordinates. -/
def translatedFields {a n : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (t : Fin n → ℝ) :=
  fun i x => X i (x+t)

/-- Translation preserves smoothness on the recentered coefficient domain. -/
theorem translatedFields_contDiffOn {a n : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (t : Fin n → ℝ) (i : Fin a) :
    ContDiffOn ℝ (⊤ : ℕ∞) (translatedFields X t i) (translatedDomain Ω t) :=
  (hX i).comp (contDiff_id.add contDiff_const).contDiffOn (fun _ h => h)

/-- Translation has identity derivative, so directions are unchanged. -/
theorem fderiv_translate_apply {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (t x v : Fin n → ℝ) (hF : DifferentiableAt ℝ F (x+t)) :
    fderiv ℝ (fun y => F (y+t)) x v = fderiv ℝ F (x+t) v := by
  have ht : HasFDerivAt (fun y : Fin n → ℝ => y+t)
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) x := (hasFDerivAt_id x).add_const t
  change fderiv ℝ (F ∘ (fun y => y+t)) x v = _
  rw [fderiv_comp x hF ht.differentiableAt,ht.fderiv]
  rfl

/-- The actual nested brackets commute with recentering, for
fields smooth only on their original open domain (BB Theorem 10.19). -/
theorem translatedFields_wordBracket {a n : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (t : Fin n → ℝ)
    (I : List (Fin a)) :
    ∀ x ∈ translatedDomain Ω t,
      wordBracket (translatedFields X t) I x = wordBracket X I (x+t) := by
  induction I with
  | nil => intro x _; rfl
  | cons i I ih =>
    cases I with
    | nil => intro x _; rfl
    | cons j J =>
      intro x hx
      have he : wordBracket (translatedFields X t) (j::J) =ᶠ[𝓝 x]
          (fun y => wordBracket X (j::J) (y+t)) :=
        ((show EqOn _ _ (translatedDomain Ω t) from fun y hy => ih y hy).eventuallyEq_of_mem
          ((translatedDomain Ω t).isOpen.mem_nhds hx))
      have hdX := ((hX i).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
      have hdW := ((G1.wordBracket_contDiffOn Ω.isOpen X hX (j::J)).contDiffAt
        (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
      change fderiv ℝ _ x _ - fderiv ℝ _ x _ = _
      rw [he.fderiv_eq,ih x hx]
      change fderiv ℝ (fun y => wordBracket X (j::J) (y+t)) x (X i (x+t)) -
        fderiv ℝ (fun y => X i (y+t)) x (wordBracket X (j::J) (x+t)) = _
      rw [fderiv_translate_apply _ t x _ hdW,fderiv_translate_apply _ t x _ hdX]
      rfl
end RothschildStein.L1
