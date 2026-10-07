-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.HolderSpaces
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]

/-- Extending an output supported in B(z,r/4) from B(z,r) to X
costs at most 1+(4/(3r))^δ in the full Hölder norm. -/
theorem boundedHolderNorm_ball_extension {z : X} {r : ℝ} (hr : 0 < r)
    {δ : ℝ≥0} {g : X → ℝ} (hg : BoundedHolder δ (ball z r) g)
    (hs : ∀ x ∉ ball z (r / 4), g x = 0) :
    boundedHolderNorm δ univ g ≤ (1 + ENNReal.ofReal ((4 / (3 * r)) ^ (δ : ℝ))) *
      boundedHolderNorm δ (ball z r) g := by
  let S := (holderSup (ball z r) g).toReal
  let H := (holderSemi δ (ball z r) g).toReal
  let c := (4 / (3 * r)) ^ (δ : ℝ)
  have hSn : 0 ≤ S := ENNReal.toReal_nonneg
  have hHn : 0 ≤ H := ENNReal.toReal_nonneg
  have hcn : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  have hout {x : X} (hx : x ∉ ball z r) : g x = 0 :=
    hs x (fun h => hx ((ball_subset_ball (show r / 4 ≤ r by linarith)) h))
  have hcross {x y : X} (hx : x ∈ ball z r) (hy : y ∉ ball z r) :
      |g x - g y| ≤ c * S * dist x y ^ (δ : ℝ) := by
    rw [hout hy, sub_zero]
    by_cases hxin : x ∈ ball z (r / 4)
    · have hxz : dist x z < r / 4 := hxin
      have hyz : r ≤ dist y z := not_lt.mp hy
      have htri := dist_triangle y x z
      rw [dist_comm y x] at htri
      have hd : 3 * r / 4 ≤ dist x y := by linarith
      have hp := Real.rpow_le_rpow (show 0 ≤ 3 * r / 4 by positivity) hd δ.coe_nonneg
      have he : c * (3 * r / 4) ^ (δ : ℝ) = 1 := by
        dsimp [c]
        rw [← Real.mul_rpow (by positivity) (by positivity), show (4 / (3 * r)) * (3 * r / 4) = 1 by field_simp]
        simp
      have hcp : 1 ≤ c * dist x y ^ (δ : ℝ) := he ▸ mul_le_mul_of_nonneg_left hp hcn
      have hb := abs_le_holderSup hg.parts.1 hx
      have hSb := mul_le_mul_of_nonneg_left hcp hSn
      nlinarith
    · rw [hs x hxin, abs_zero]; positivity
  have hpoint (x y : X) : |g x - g y| ≤ (H + c * S) * dist x y ^ (δ : ℝ) := by
    by_cases hx : x ∈ ball z r <;> by_cases hy : y ∈ ball z r
    · exact (sub_le_holderSemi hg.parts.2 hx hy).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hcn hSn)) (Real.rpow_nonneg dist_nonneg _))
    · exact (hcross hx hy).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hHn) (Real.rpow_nonneg dist_nonneg _))
    · rw [abs_sub_comm, dist_comm]; exact (hcross hy hx).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hHn) (Real.rpow_nonneg dist_nonneg _))
    · rw [hout hx, hout hy, sub_self, abs_zero]; positivity
  have hsup : holderSup univ g ≤ holderSup (ball z r) g := by
    apply iSup_le; intro x
    by_cases hx : (x : X) ∈ ball z r
    · exact le_iSup_of_le ⟨x, hx⟩ le_rfl
    · simp only [hout hx, abs_zero, ENNReal.ofReal_zero]; exact bot_le
  have hsemi := holderSemi_le_of_bound (add_nonneg hHn (mul_nonneg hcn hSn))
    (δ := δ) (A := univ) (f := g) (fun x _ y _ => hpoint x y)
  have he : ENNReal.ofReal (H + c * S) = holderSemi δ (ball z r) g +
      ENNReal.ofReal c * holderSup (ball z r) g := by
    rw [ENNReal.ofReal_add hHn (mul_nonneg hcn hSn), ENNReal.ofReal_mul hcn]
    dsimp [H, S]
    rw [ENNReal.ofReal_toReal hg.parts.1.ne, ENNReal.ofReal_toReal hg.parts.2.ne]
  rw [he] at hsemi
  change holderSup univ g + holderSemi δ univ g ≤ _
  apply (add_le_add hsup hsemi).trans
  rw [boundedHolderNorm, add_mul, one_mul]
  calc
    _ = (holderSup (ball z r) g + holderSemi δ (ball z r) g) + ENNReal.ofReal c * holderSup (ball z r) g := by ac_rfl
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_right (le_add_right le_rfl) _)
end RothschildStein.H2
