-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- Linearity of the replacement numerator in the inserted vector
(BB Cramer's formula, p. 422). -/
theorem replacementDet_coordinates {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (v : Fin n → ℝ) (i : Fin n) (x : Fin n → ℝ) :
    replacementDet Z B v i x = ∑ k, v k * replacementDet Z B (Pi.single k 1) i x := by
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin n → ℝ) := by
    ext j
    simp [Pi.single_apply]
  change (Matrix.cramer (frameMatrix Z B x) v) i = _
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cramer_apply, replacementDet]

/-- Coordinate expression of a Cramer coefficient as a linear
functional of the represented field value (BB p. 422). -/
theorem frameCoefficient_coordinates {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin n) (x : Fin n → ℝ) :
    frameCoefficient Z B V i x =
      ∑ k, V x k * frameCoefficient Z B (fun _ => Pi.single k 1) i x := by
  unfold frameCoefficient
  rw [replacementDet_coordinates, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Bounds of the coordinate functionals control coefficients for
an arbitrary represented field, using the sup norm (BB p. 422). -/
theorem frameCoefficient_le_of_coordinate_bounds {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin n) (x : Fin n → ℝ)
    {M : ℝ}
    (hcoord : ∀ k, |frameCoefficient Z B (fun _ => Pi.single k 1) i x| ≤ M) :
    |frameCoefficient Z B V i x| ≤ n * M * ‖V x‖ := by
  rw [frameCoefficient_coordinates]
  calc
    _ ≤ ∑ k, |V x k * frameCoefficient Z B (fun _ => Pi.single k 1) i x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, ‖V x‖ * M := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (V x) k)
        (hcoord k) (abs_nonneg _) (norm_nonneg _)
    _ = n * M * ‖V x‖ := by simp; ring

/-- A fixed nondegenerate frame has uniformly bounded coordinate
functionals on any compact subset of its original-domain patch. This bound
is frame-specific; it is not the suboptimal uniform quantitative estimate
(BB Proposition 9.29, p. 422). -/
theorem exists_compact_frame_coordinate_bound {ι : Type*} {n : ℕ}
    {Ω K : Set (Fin n → ℝ)} {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω) (B : Fin n → ι)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hB : ∀ x ∈ K, frameDet Z B x ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ i k (x : Fin n → ℝ), x ∈ K →
      |frameCoefficient Z B (fun _ => Pi.single k 1) i x| ≤ M := by
  have hex : ∀ i k : Fin n, ∃ M : ℝ, ∀ x ∈ K,
      |frameCoefficient Z B (fun _ => Pi.single k 1) i x| ≤ M := by
    intro i k
    have hc := (frameCoefficient_contDiffOn hZ (contDiffOn_const (c := Pi.single k 1)) B i).continuousOn
    obtain ⟨M, hM⟩ := (hK.image_of_continuousOn (hc.mono (fun x hx => ⟨hKΩ hx, hB x hx⟩))).isBounded.exists_norm_le
    exact ⟨M, fun x hx => by simpa only [Real.norm_eq_abs] using hM _ (mem_image_of_mem _ hx)⟩
  choose M hM using hex
  let C := 1 + ∑ i : Fin n, ∑ k : Fin n, |M i k|
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro i k x hx
  have hi : |M i k| ≤ ∑ l : Fin n, |M i l| :=
    Finset.single_le_sum (fun l _ => abs_nonneg (M i l)) (Finset.mem_univ k)
  have hk : (∑ l : Fin n, |M i l|) ≤ ∑ j : Fin n, ∑ l : Fin n, |M j l| :=
    Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun l _ => abs_nonneg (M j l))) (Finset.mem_univ i)
  exact ((hM i k x hx).trans (le_abs_self _)).trans (hi.trans (hk.trans (by dsimp [C]; linarith)))

end RothschildStein.G4
