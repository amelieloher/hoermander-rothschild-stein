-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialCoordinateBrackets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The exact radial commutator identity underlying BB's Euler argument.
The constant coordinate contribution is isolated from the varying
coefficient error before any weighted estimates are applied. -/
theorem radial_frame_euler_bracket_identity {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (hrad : ∀ u ∈ Ω, ∑ i, u i • Z i u = u)
    {u : Fin N → ℝ} (hu : u ∈ Ω) (i j : Fin N) :
    (2 : ℝ) • VectorField.lieBracket ℝ (Z j) (fun _ => Pi.single i 1) u +
      (∑ k, u k • VectorField.lieBracket ℝ (Z k)
        (VectorField.lieBracket ℝ (Z j) (fun _ => Pi.single i 1)) u) =
      VectorField.lieBracket ℝ (Z j) (Z i) u +
      (∑ k, (Z j u k - (Pi.single j (1 : ℝ) : Fin N → ℝ) k) •
        VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (Z k) u) +
      ∑ k, u k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1)
        (VectorField.lieBracket ℝ (Z j) (Z k)) u := by
  let E := fun _ : Fin N → ℝ => (Pi.single i (1 : ℝ) : Fin N → ℝ)
  let W := VectorField.lieBracket ℝ (Z j) E
  have he := radial_frame_bracket_identity Ω Z hZ hrad (Z j) hu i
  have hJac (k : Fin N) : VectorField.lieBracket ℝ (Z j)
      (VectorField.lieBracket ℝ E (Z k)) u =
      -VectorField.lieBracket ℝ (Z k) W u +
        VectorField.lieBracket ℝ E (VectorField.lieBracket ℝ (Z j) (Z k)) u := by
    have hj := VectorField.leibniz_identity_lieBracket (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (by simp)
      ((hZ j).contDiffAt (Ω.isOpen.mem_nhds hu))
      (show ContDiffAt ℝ (⊤ : ℕ∞) E u from contDiffAt_const)
      ((hZ k).contDiffAt (Ω.isOpen.mem_nhds hu))
    rw [hj,VectorField.lieBracket_swap (V := W) (W := Z k)]
  have hcoeff : (∑ k, Z j u k • VectorField.lieBracket ℝ E (Z k) u) =
      -W u + ∑ k, (Z j u k - (Pi.single j (1 : ℝ) : Fin N → ℝ) k) •
        VectorField.lieBracket ℝ E (Z k) u := by
    have hsplit (k : Fin N) :
        Z j u k • VectorField.lieBracket ℝ E (Z k) u =
        (Pi.single j (1 : ℝ) : Fin N → ℝ) k • VectorField.lieBracket ℝ E (Z k) u +
        (Z j u k - (Pi.single j (1 : ℝ) : Fin N → ℝ) k) •
          VectorField.lieBracket ℝ E (Z k) u := by
      rw [← add_smul]
      congr 1
      ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    have hdelta : (∑ k, (Pi.single j (1 : ℝ) : Fin N → ℝ) k •
        VectorField.lieBracket ℝ E (Z k) u) = -W u := by
      simpa [Pi.single_apply,W] using
        (VectorField.lieBracket_swap (𝕜 := ℝ) (V := E) (W := Z j) (x := u))
    rw [hdelta]
  change W u = VectorField.lieBracket ℝ (Z j) (Z i) u +
    (∑ k, Z j u k • VectorField.lieBracket ℝ E (Z k) u) +
    ∑ k, u k • VectorField.lieBracket ℝ (Z j) (VectorField.lieBracket ℝ E (Z k)) u at he
  rw [hcoeff] at he
  simp_rw [hJac,smul_add,smul_neg] at he
  rw [Finset.sum_add_distrib,Finset.sum_neg_distrib] at he
  change (2 : ℝ) • W u + _ = _
  rw [two_smul]
  have hr (a b c d e : Fin N → ℝ) (hh : a = b + (-a+c) + (-d+e)) :
      a+a+d = b+c+e := by
    calc
      _ = (b+(-a+c)+(-d+e))+a+d := by rw [← hh]
      _ = _ := by abel
  exact hr _ _ _ _ _ he
end RothschildStein.L1
