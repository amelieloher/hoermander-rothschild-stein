-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialZeroDifferentiation
public import RothschildStein.L1.LieBracketFiniteSums
public import RothschildStein.L1.WeightedFieldBrackets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology BigOperators
namespace RothschildStein.L1

/-- Bracketing a differentiated zero radial sum exchanges the two
remainder indices exactly, before taking any weighted quotient. -/
theorem radial_zero_bracket_sum {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (R : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hR : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (R k) Ω)
    (hrad : ∀ u ∈ Ω, ∑ k, u k • R k u = 0)
    {u : Fin N → ℝ} (hu : u ∈ Ω) (i j : Fin N) :
    (∑ k, VectorField.lieBracket ℝ (fun _ => Pi.single j 1)
      (fun v => v k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (R k) v) u) =
      VectorField.lieBracket ℝ (R i) (fun _ => Pi.single j 1) u := by
  let T := fun v : Fin N → ℝ => ∑ k, v k •
    VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (R k) v
  have he : T =ᶠ[𝓝 u] (fun v => -R i v) :=
    Filter.Eventually.mono (Ω.isOpen.mem_nhds hu) (fun v hv => by
      have hh := (radial_zero_differential_identity Ω R hR hrad hv i).symm
      have rearrange (a b : Fin N → ℝ) (h : a+b=0) : b = -a := by
        calc
          b = -a+(a+b) := by abel
          _ = -a := by rw [h,add_zero]
      exact rearrange _ _ hh)
  have hg := (Filter.EventuallyEq.refl (𝓝 u) (fun _ : Fin N → ℝ => Pi.single j 1)).lieBracket_vectorField_eq
    (𝕜 := ℝ) he
  have hs := lieBracket_finset_sum_right Finset.univ
    (fun _ : Fin N → ℝ => Pi.single j 1)
    (fun k v => v k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (R k) v) u
    (fun k _ => (((contDiffOn_apply ℝ ℝ k Ω).smul
      (lieBracket_contDiffOn Ω _ _ contDiffOn_const (hR k))).contDiffAt
        (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp))
  rw [← hs]
  change VectorField.lieBracket ℝ (fun _ => Pi.single j 1) T u = _
  rw [hg]
  rw [VectorField.lieBracket_swap (V := R i) (W := fun _ => Pi.single j 1)]
  simp only [VectorField.lieBracket,fderiv_fun_neg,neg_apply,map_neg]
  abel
end RothschildStein.L1
