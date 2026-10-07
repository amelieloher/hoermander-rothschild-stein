-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FrameVolumeAdapters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.L1

/-- A selected suboptimal frame term is comparable in both
directions with the full volume polynomial. The factor counts all
frames and retains inverse suboptimality (BB pp. 521–522). -/
theorem suboptimal_frame_volumePolynomial_bounds {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
    (B : Fin n → ι) (x : Fin n → ℝ) {t r : ℝ} (ht : 0 < t) (hr : 0 < r)
    (hB : G4.IsSuboptimal Z w B x t r) :
    |G4.frameDet Z B x| * r ^ (∑ i, (w (B i) : ℕ)) ≤
      G4.volumePolynomial (fun C => G4.frameDet Z C x)
        (fun C : Fin n → ι => ∑ i, (w (C i) : ℕ)) r ∧
    G4.volumePolynomial (fun C => G4.frameDet Z C x)
        (fun C : Fin n → ι => ∑ i, (w (C i) : ℕ)) r ≤
      ((Fintype.card (Fin n → ι) : ℝ) / t) *
        (|G4.frameDet Z B x| * r ^ (∑ i, (w (B i) : ℕ))) := by
  classical
  refine ⟨?_, ?_⟩
  · unfold G4.volumePolynomial
    exact Finset.single_le_sum
      (fun C _ => mul_nonneg (abs_nonneg (G4.frameDet Z C x))
        (pow_nonneg hr.le (∑ i, (w (C i) : ℕ)))) (Finset.mem_univ B)
  · have hsum : t * G4.volumePolynomial (fun C => G4.frameDet Z C x)
        (fun C : Fin n → ι => ∑ i, (w (C i) : ℕ)) r ≤
        (Fintype.card (Fin n → ι) : ℝ) *
          (|G4.frameDet Z B x| * r ^ (∑ i, (w (B i) : ℕ))) := by
      rw [G4.volumePolynomial, Finset.mul_sum]
      calc
        _ ≤ ∑ _C : Fin n → ι,
            |G4.frameDet Z B x| * r ^ (∑ i, (w (B i) : ℕ)) := by
          apply Finset.sum_le_sum
          intro C _
          simpa only [G4.frameWeight_eq_nat_sum, zpow_natCast] using hB C
        _ = _ := by simp
    have hd := (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hsum)
    (convert hd using 1; ring)

end RothschildStein.L1
