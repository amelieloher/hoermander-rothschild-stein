-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.Defs
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Separation.Regular

@[expose] public section

open Filter Topology Set

namespace Hormander.D

variable {N : ℕ}

/-- A compact set inside an open set has a smooth, compactly supported plateau cutoff. -/
theorem exists_smooth_cutoff {F W : Set (EuclideanSpace ℝ (Fin N))}
    (hF : IsCompact F) (hW : IsOpen W) (hFW : F ⊆ W) :
    ∃ χ : EuclideanSpace ℝ (Fin N) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ range χ ⊆ Icc 0 1 ∧
        tsupport χ ⊆ W ∧ ∀ᶠ x in 𝓝ˢ F, χ x = 1 := by
  obtain ⟨W₀, hW₀, hFW₀, hclW₀W, hclW₀compact⟩ :=
    exists_open_between_and_isCompact_closure hF hW hFW
  obtain ⟨V, hV, hFV, hclVW₀, _⟩ :=
    exists_open_between_and_isCompact_closure hF hW₀ hFW₀
  obtain ⟨χ, hχcont, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff hW₀ isClosed_closure hclVW₀
  have hχts : tsupport χ = closure W₀ := by
    rw [tsupport, hχsupport]
  have hχcompact : HasCompactSupport χ := by
    change IsCompact (tsupport χ)
    rw [hχts]
    exact hclW₀compact
  refine ⟨χ, hχcont, hχcompact, hχrange, ?_, ?_⟩
  · rw [hχts]
    exact hclW₀W
  · filter_upwards [hV.mem_nhdsSet.mpr hFV] with x hx
    exact (hχone x).mp (subset_closure hx)

/-- A fixed nested pair has a smooth compactly supported cutoff
strictly between its members, with support contained in the outer member's plateau. -/
theorem exists_intermediate_cutoff {η₁ η₂ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hη : cutoffPrecedes η₁ η₂) :
    ∃ η', cutoffPrecedes η₁ η' ∧ cutoffPrecedes η' η₂ ∧
      tsupport η' ⊆ interior {x | η₂ x = 1} := by
  rcases hη with ⟨hη₁smooth, hη₁compact, hη₂smooth, hη₂compact, hplateau⟩
  have hFcompact : IsCompact (tsupport η₁) := hη₁compact
  let W := interior {x | η₂ x = 1}
  have hW : IsOpen W := isOpen_interior
  have hFW : tsupport η₁ ⊆ W :=
    (cutoffPrecedes_eventually_iff_interior η₁ η₂).mp hplateau
  obtain ⟨η', hη'smooth, hη'compact, _, hη'support, hη'plateau⟩ :=
    exists_smooth_cutoff hFcompact hW hFW
  have hη₁η' : cutoffPrecedes η₁ η' :=
    ⟨hη₁smooth, hη₁compact, hη'smooth, hη'compact, hη'plateau⟩
  have hη'η₂plateau : ∀ᶠ x in 𝓝ˢ (tsupport η'), η₂ x = 1 :=
    (cutoffPrecedes_eventually_iff_interior η' η₂).mpr hη'support
  exact ⟨η', hη₁η',
    ⟨hη'smooth, hη'compact, hη₂smooth, hη₂compact, hη'η₂plateau⟩, hη'support⟩

/-- Nested smooth cutoffs compose: if the middle cutoff is one near the first support and
the outer cutoff is one near the middle support, it is one near the first support. -/
theorem cutoffPrecedes.trans {η₁ η₂ η₃ : EuclideanSpace ℝ (Fin N) → ℝ}
    (h₁₂ : cutoffPrecedes η₁ η₂) (h₂₃ : cutoffPrecedes η₂ η₃) :
    cutoffPrecedes η₁ η₃ := by
  have h₁₂plateau : tsupport η₁ ⊆ interior {x | η₂ x = 1} :=
    (cutoffPrecedes_eventually_iff_interior _ _).mp h₁₂.2.2.2.2
  have h₂₃plateau : tsupport η₂ ⊆ interior {x | η₃ x = 1} :=
    (cutoffPrecedes_eventually_iff_interior _ _).mp h₂₃.2.2.2.2
  have h₁₃plateau : tsupport η₁ ⊆ interior {x | η₃ x = 1} := by
    intro x hx
    have hsub : interior {y : EuclideanSpace ℝ (Fin N) | η₂ y = 1} ⊆
        {y : EuclideanSpace ℝ (Fin N) | η₂ y = 1} := interior_subset
    have hη₂one : η₂ x = 1 := hsub (h₁₂plateau hx)
    have hx₂ : x ∈ tsupport η₂ := by
      apply subset_tsupport
      simp [hη₂one]
    exact h₂₃plateau hx₂
  exact ⟨h₁₂.1, h₁₂.2.1, h₂₃.2.2.1, h₂₃.2.2.2.1,
    (cutoffPrecedes_eventually_iff_interior _ _).mpr h₁₃plateau⟩

end Hormander.D
