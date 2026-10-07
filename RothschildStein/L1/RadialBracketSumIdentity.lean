-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LieBracketAddRight
public import RothschildStein.L1.RadialFrameDifferentiation
public import RothschildStein.L1.WeightedFieldBrackets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology BigOperators
namespace RothschildStein.L1

/-- Bracketing the differentiated radial identity as an actual field
identity leaves its variable coefficient derivatives inside each bracket. -/
theorem radial_frame_bracket_sum_identity {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Z k) Ω)
    (hrad : ∀ u ∈ Ω, ∑ k, u k • Z k u = u)
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    {u : Fin N → ℝ} (hu : u ∈ Ω) (i : Fin N) :
    VectorField.lieBracket ℝ V (fun _ => Pi.single i 1) u =
      VectorField.lieBracket ℝ V (Z i) u +
        ∑ k, VectorField.lieBracket ℝ V
          (fun v => v k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (Z k) v) u := by
  let T := fun k v => v k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (Z k) v
  have hT (k : Fin N) : ContDiffOn ℝ (⊤ : ℕ∞) (T k) Ω :=
    (contDiffOn_apply ℝ ℝ k Ω).smul (lieBracket_contDiffOn Ω _ _ contDiffOn_const (hZ k))
  have he : (fun _ : Fin N → ℝ => Pi.single i 1) =ᶠ[𝓝 u]
      (fun v => Z i v + ∑ k, T k v) :=
    Filter.Eventually.mono (Ω.isOpen.mem_nhds hu) (fun v hv =>
      radial_frame_coordinate_identity Ω Z hZ hrad hv i)
  have hg := (Filter.EventuallyEq.refl (𝓝 u) V).lieBracket_vectorField_eq (𝕜 := ℝ) he
  rw [hg]
  rw [lieBracket_fun_add_right V (Z i) (fun v => ∑ k, T k v) u
    (((hZ i).contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp))
    (((ContDiffOn.sum (fun k _ => hT k)).contDiffAt
      (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp))]
  rw [lieBracket_finset_sum_right Finset.univ V T u (fun k _ =>
    ((hT k).contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp))]
end RothschildStein.L1
