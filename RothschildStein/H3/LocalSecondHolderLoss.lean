-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- On a bounded positive gap interval every smaller loss is
controlled by the largest loss, with the radius dependence explicit. -/
theorem bounded_gap_rpow_loss {d R a b : ℝ} (hd : 0 < d) (hdR : d ≤ R)
    (hab : a ≤ b) : d ^ (-a) ≤ R ^ (b - a) * d ^ (-b) := by
  have he : d ^ (-a) = d ^ (b - a) * d ^ (-b) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hd.le hdR (sub_nonneg.mpr hab))
    (Real.rpow_nonneg hd.le _)

/-- Combining the cutoff source loss with the full first-order
interpolation loss gives exactly beta = 2 + alpha + gamma. The
constant is selected before every input norm and gap. -/
theorem local_second_holder_loss_bound {α γ R A B C D : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hR : 0 < R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ d F U ψ Ψ : ℝ,
      0 < d → d ≤ R → 0 ≤ F → 0 ≤ U →
      ψ ≤ F / 2 + C * d ^ (-γ) * U →
      Ψ ≤ A * d ^ (-α) * F + B * d ^ (-(2 + α)) * ψ + D * U →
      Ψ ≤ K * d ^ (-(2 + α + γ)) * (F + U) := by
  let β := 2 + α + γ
  let L := A * R ^ (β - α) + B / 2 * R ^ γ
  let M := B * C + D * R ^ β
  let K := L + M + 1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro d F U ψ Ψ hd hdR hF hU hψ hΨ
  have hp : 0 ≤ d ^ (-β) := Real.rpow_nonneg hd.le _
  have h0 := bounded_gap_rpow_loss (a := 0) (b := β) hd hdR (by dsimp [β]; linarith)
  have h1 := bounded_gap_rpow_loss (a := α) (b := β) hd hdR (by dsimp [β]; linarith)
  have h2 := bounded_gap_rpow_loss (a := 2 + α) (b := β) hd hdR (by dsimp [β]; linarith)
  simp only [neg_zero, Real.rpow_zero, sub_zero] at h0
  have he2 : β - (2 + α) = γ := by dsimp [β]; ring
  rw [he2] at h2
  have hprod : d ^ (-(2 + α)) * d ^ (-γ) = d ^ (-β) := by
    rw [← Real.rpow_add hd]
    congr 1
    dsimp [β]
    ring
  have hstep := hΨ.trans (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hψ
      (mul_nonneg hB (Real.rpow_nonneg hd.le _)))) le_rfl)
  have hAF := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hA) hF
  have hBF := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hB) (by positivity : 0 ≤ F / 2)
  have hDU := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h0 hU) hD
  have htotal : Ψ ≤ L * d ^ (-β) * F + M * d ^ (-β) * U := by
    calc
      Ψ ≤ A * d ^ (-α) * F + B * d ^ (-(2 + α)) * (F / 2 + C * d ^ (-γ) * U) + D * U := hstep
      _ = A * d ^ (-α) * F + B * d ^ (-(2 + α)) * (F / 2) + B * C * d ^ (-β) * U + D * U := by
        rw [mul_add]
        have he : B * d ^ (-(2 + α)) * (C * d ^ (-γ) * U) = B * C * d ^ (-β) * U := by
          calc
            _ = B * C * (d ^ (-(2 + α)) * d ^ (-γ)) * U := by ring
            _ = _ := by rw [hprod]
        rw [he]
        ring
      _ ≤ _ := by dsimp [L, M]; nlinarith [hAF, hBF, hDU]
  have hLF : L * d ^ (-β) * F ≤ K * d ^ (-β) * F :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by dsimp [K]; linarith : L ≤ K) hp) hF
  have hMU : M * d ^ (-β) * U ≤ K * d ^ (-β) * U :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by dsimp [K]; linarith : M ≤ K) hp) hU
  exact htotal.trans (by nlinarith [hLF, hMU])

end RothschildStein.H3
