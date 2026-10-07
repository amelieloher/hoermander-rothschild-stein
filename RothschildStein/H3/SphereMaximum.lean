-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.KernelSphereBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
variable {N : ℕ} {G : HomogeneousGroup N}

/-- Every punctured continuous scalar function has an attained,
finite, nonnegative maximum of its absolute value on a gauge unit sphere.
This also applies to every Euclidean kernel derivative (BB p. 346). -/
theorem kernelSphereBound_continuous
    {ν T : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hT : ContinuousOn T {0}ᶜ) :
    0 ≤ kernelSphereBound ν T ∧
    (∃ z, ν z = 1 ∧ |T z| = kernelSphereBound ν T) ∧
    ∀ z, ν z = 1 → |T z| ≤ kernelSphereBound ν T := by
  obtain ⟨hc, hn⟩ := homogeneousGauge_unitSphere hν
  have hsub : {x | ν x = 1} ⊆ ({0}ᶜ : Set (Fin N → ℝ)) := by
    intro x hx
    change x ≠ 0
    intro hx0
    have hz := (hν.2.2.1 0).mpr rfl
    change ν x = 1 at hx
    rw [hx0, hz] at hx
    norm_num at hx
  obtain ⟨z, hz, hmax⟩ := hc.exists_isMaxOn hn (hT.mono hsub).abs
  have hg : IsGreatest ((fun x => |T x|) '' {x | ν x = 1}) |T z| := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro b ⟨x, hx, rfl⟩
    exact hmax hx
  have he : kernelSphereBound ν T = |T z| := hg.isLUB.csSup_eq ⟨|T z|, hg.1⟩
  rw [he]
  exact ⟨abs_nonneg _, ⟨z, hz, rfl⟩, fun x hx => hmax hx⟩

/-- The sphere maximum bounds every homogeneous kernel degree,
including type zero before imposing a cancellation condition (BB p. 350). -/
theorem kernelSphereBound_homogeneous
    {ν T : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {γ : ℝ} (hT : ContinuousOn T {0}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → T (G.dilate t x) = t ^ γ * T x) :
    ∀ x, x ≠ 0 → |T x| ≤ kernelSphereBound ν T * (ν x) ^ γ := by
  obtain ⟨M, _, ⟨z, hz, he⟩, hb, hglobal⟩ :=
    homogeneous_function_sphere_bound hν γ hT hhom
  have hg : IsGreatest ((fun x => |T x|) '' {x | ν x = 1}) M := by
    refine ⟨⟨z, hz, he⟩, ?_⟩
    rintro b ⟨x, hx, rfl⟩
    exact hb x hx
  have hM : kernelSphereBound ν T = M := hg.isLUB.csSup_eq ⟨M, hg.1⟩
  simpa only [hM] using hglobal

end RothschildStein.H3
