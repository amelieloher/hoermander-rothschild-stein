-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ZeroExtension
public import RothschildStein.S.SobolevRepresentatives
public import RothschildStein.S.MollifierZeroExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.S
variable {n q : ℕ} {p : ℝ≥0∞}

/-- Compactly supported Sobolev data have the same norm on an
interior open patch containing their support (BB Cor 2.10, p. 73;
locality of every weak word supplies the support condition). -/
theorem sobolevXENorm_eq_of_compact_support
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (k : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : memSobolevX w X Ω k p f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ U) :
    sobolevXENorm w X Ω k p f = sobolevXENorm w X U k p f := by
  classical
  have hi : (U : Set (Fin n → ℝ)).indicator f = f := by
    funext x
    by_cases hx : x ∈ (U : Set (Fin n → ℝ))
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))).symm
  unfold sobolevXENorm
  apply Finset.sum_congr rfl
  intro I hI
  obtain ⟨g,hg,_⟩ := hf.2 I hI
  have hu := hasWeakWordDeriv_restrict X Ω U hU hg
  have he := hasWeakWordDeriv_zeroExtension X Ω U hU
    ⟨tsupport f,hc.isCompact⟩ hs I f g hu
    (Eventually.of_forall (fun x _ hx => image_eq_zero_of_notMem_tsupport hx))
  rw [hi] at he
  rw [weakWordENorm_eq X Ω I p f _ he,weakWordENorm_eq X U I p f g hu,
    eLpNorm_indicator_eq_eLpNorm_restrict U.isOpen.measurableSet,
    Measure.restrict_restrict_of_subset hU]

end RothschildStein.S
