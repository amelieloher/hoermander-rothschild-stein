-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.TriangularProjection
public import RothschildStein.S.ClassicalWords
public import RothschildStein.G1.BracketAlgebra

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.L1

/-- Derivatives of projected fields intertwine on an open set. -/
theorem fderiv_linear_projection_apply {n N : ℕ} {U : Set (Fin N → ℝ)}
    (hU : IsOpen U) (P : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : (Fin n → ℝ) → (Fin n → ℝ)) (Z : (Fin N → ℝ) → (Fin N → ℝ))
    (hproj : ∀ ξ ∈ U, P (Z ξ) = X (P ξ)) {ξ : Fin N → ℝ} (hξ : ξ ∈ U)
    (hX : DifferentiableAt ℝ X (P ξ)) (hZ : DifferentiableAt ℝ Z ξ)
    (v : Fin N → ℝ) :
    P (fderiv ℝ Z ξ v) = fderiv ℝ X (P ξ) (P v) := by
  have heq : P ∘ Z =ᶠ[𝓝 ξ] X ∘ P := by
    filter_upwards [hU.mem_nhds hξ] with η hη
    exact hproj η hη
  have hh := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp ξ P.differentiableAt hZ,
    fderiv_comp ξ hX P.differentiableAt, ContinuousLinearMap.fderiv] at hh
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv] using
    congrArg (fun A : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ) => A v) hh

/-- The actual fderiv-based Lie brackets project to the
original Lie bracket whenever the fields project on an open neighborhood. -/
theorem lieBracket_linear_projection {n N : ℕ} {U : Set (Fin N → ℝ)}
    (hU : IsOpen U) (P : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ))
    (X Y : (Fin n → ℝ) → (Fin n → ℝ))
    (Z W : (Fin N → ℝ) → (Fin N → ℝ))
    (hZproj : ∀ ξ ∈ U, P (Z ξ) = X (P ξ))
    (hWproj : ∀ ξ ∈ U, P (W ξ) = Y (P ξ))
    {ξ : Fin N → ℝ} (hξ : ξ ∈ U)
    (hX : DifferentiableAt ℝ X (P ξ)) (hY : DifferentiableAt ℝ Y (P ξ))
    (hZ : DifferentiableAt ℝ Z ξ) (hW : DifferentiableAt ℝ W ξ) :
    P (VectorField.lieBracket ℝ Z W ξ) = VectorField.lieBracket ℝ X Y (P ξ) := by
  unfold VectorField.lieBracket
  rw [map_sub, fderiv_linear_projection_apply hU P Y W hWproj hξ hY hW,
    fderiv_linear_projection_apply hU P X Z hZproj hξ hX hZ,
    hZproj ξ hξ, hWproj ξ hξ]

/-- All lifted nested word brackets project to the original
word brackets. This is an identity of the actual smooth fields. -/
theorem wordBracket_linear_projection {q n N : ℕ}
    {Ω : Set (Fin n → ℝ)} {U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (P : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)) (hmap : MapsTo P U Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (Z : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) U)
    (hproj : ∀ ξ ∈ U, ∀ i, P (Z i ξ) = X i (P ξ)) (I : List (Fin q)) :
    ∀ ξ ∈ U, P (wordBracket Z I ξ) = wordBracket X I (P ξ) := by
  induction I with
  | nil => intro ξ _; simp only [wordBracket, Pi.zero_apply, map_zero]
  | cons i I ih =>
      cases I with
      | nil => intro ξ hξ; exact hproj ξ hξ i
      | cons j J =>
          intro ξ hξ
          have hdX := ((hX i).contDiffAt (hΩ.mem_nhds (hmap hξ))).differentiableAt (by simp)
          have hdY := ((G1.wordBracket_contDiffOn hΩ X hX (j :: J)).contDiffAt
            (hΩ.mem_nhds (hmap hξ))).differentiableAt (by simp)
          have hdZ := ((hZ i).contDiffAt (hU.mem_nhds hξ)).differentiableAt (by simp)
          have hdW := ((G1.wordBracket_contDiffOn hU Z hZ (j :: J)).contDiffAt
            (hU.mem_nhds hξ)).differentiableAt (by simp)
          exact lieBracket_linear_projection hU P (X i) (wordBracket X (j :: J))
            (Z i) (wordBracket Z (j :: J)) (fun η hη => hproj η hη i) ih hξ hdX hdY hdZ hdW

end RothschildStein.L1
