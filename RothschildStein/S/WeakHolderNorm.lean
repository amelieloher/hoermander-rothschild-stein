-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderWeakLocality

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.S
variable {n q : ℕ}

/-- Hölder seminorm of a weak word derivative (BB Definition 2.13, p. 81). -/
def weakHolderWordENorm
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (U : Opens (Fin n → ℝ)) (I : List (Fin q)) (α : ℝ)
    (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ g : (Fin n → ℝ) → ℝ,hasWeakWordDeriv X U I f g ∧
    r = holderENorm d α (U : Set (Fin n → ℝ)) g}

/-- Internal weak Hölder norm on the entire weighted word
family (BB Def 2.13, p. 81; intrinsic norm is unchanged). -/
def weakHolderXENorm (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (U : Opens (Fin n → ℝ)) (k : ℕ) (α : ℝ)
    (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ I ∈ wordFamily w k,weakHolderWordENorm X d U I α f

/-- A finite Hölder weak representative realizes the internal
infimum norm exactly, by pointwise uniqueness on the open domain
(BB Def 2.13, p. 81; uniqueness). -/
theorem weakHolderWordENorm_eq
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin q))
    {α : ℝ} (hα : 0 < α) (f g : (Fin n → ℝ) → ℝ)
    (hg : hasWeakWordDeriv X U I f g)
    (hn : holderENorm G.d α (U : Set (Fin n → ℝ)) g < ⊤) :
    weakHolderWordENorm X G.d U I α f = holderENorm G.d α (U : Set (Fin n → ℝ)) g := by
  unfold weakHolderWordENorm
  apply le_antisymm
  · exact sInf_le ⟨g,hg,rfl⟩
  · apply le_sInf
    rintro r ⟨h,hh,rfl⟩
    by_cases ht : holderENorm G.d α (U : Set (Fin n → ℝ)) h < ⊤
    · exact (holderENorm_congr G.d α (U : Set (Fin n → ℝ)) g
        (eqOn_of_weakHolder_representatives Ω U G hU X I hα hg hh hn ht)).le
    · have he : holderENorm G.d α (U : Set (Fin n → ℝ)) h = ⊤ :=
        eq_top_iff.mpr (le_of_not_gt ht)
      rw [he]
      exact le_top

end RothschildStein.S
