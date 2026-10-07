-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedRadiusIntervals
public import RothschildStein.G4.Suboptimality
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.Compact

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology

namespace RothschildStein.G4

/-- A frame's positive t-suboptimal radii form an interval
(BB p. 454, immediately before (9.56)). -/
theorem ordConnected_suboptimal_radii {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
    (B : Fin n → ι) (x : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    OrdConnected {r : ℝ | 0 < r ∧ IsSuboptimal Z w B x t r} := by
  constructor
  intro r₁ h₁ r₂ h₂ r hr
  refine ⟨h₁.1.trans_le hr.1, ?_⟩
  intro C
  have hinterval := ordConnected_weighted_radius_comparison
    (mul_nonneg ht (abs_nonneg (frameDet Z C x)))
    (frameWeight w C) (frameWeight w B) (B := |frameDet Z B x|)
  have hh := hinterval.out
    (show r₁ ∈ {r : ℝ | 0 < r ∧ (t * |frameDet Z C x|) * r ^ frameWeight w C ≤
      |frameDet Z B x| * r ^ frameWeight w B} from
      ⟨h₁.1, by simpa only [mul_assoc] using h₁.2 C⟩)
    (show r₂ ∈ {r : ℝ | 0 < r ∧ (t * |frameDet Z C x|) * r ^ frameWeight w C ≤
      |frameDet Z B x| * r ^ frameWeight w B} from
      ⟨h₂.1, by simpa only [mul_assoc] using h₂.2 C⟩) hr
  simpa only [mul_assoc] using hh.2

/-- Actual frame weights are nonnegative, so the original
weighted comparisons define a closed set of all real radii
(BB p. 454, before (9.56)). -/
theorem isClosed_suboptimal_radii {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
    (B : Fin n → ι) (x : Fin n → ℝ) (t : ℝ) :
    IsClosed {r : ℝ | IsSuboptimal Z w B x t r} := by
  have hW : ∀ C : Fin n → ι, 0 ≤ frameWeight w C := by
    intro C
    change 0 ≤ ∑ i : Fin n, ((w (C i) : ℕ) : ℤ)
    exact Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hp : ∀ C : Fin n → ι, Continuous (fun r : ℝ => r ^ frameWeight w C) :=
    fun C => continuous_id.zpow₀ (frameWeight w C) (fun _ => Or.inr (hW C))
  have hc : ∀ C : Fin n → ι, IsClosed {r : ℝ |
      t * (|frameDet Z C x| * r ^ frameWeight w C) ≤
        |frameDet Z B x| * r ^ frameWeight w B} := fun C =>
    isClosed_le (continuous_const.mul (continuous_const.mul (hp C)))
      (continuous_const.mul (hp B))
  simpa only [IsSuboptimal, ofPred_forall] using isClosed_iInter hc

/-- Restriction to a closed bounded positive radius interval
makes each suboptimal-radius interval compact (BB (9.57), p. 454). -/
theorem isCompact_restricted_suboptimal_radii {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
    (B : Fin n → ι) (x : Fin n → ℝ) (t r R : ℝ) :
    IsCompact (Icc r R ∩ {ρ : ℝ | IsSuboptimal Z w B x t ρ}) :=
  isCompact_Icc.inter_right (isClosed_suboptimal_radii Z w B x t)

end RothschildStein.G4
