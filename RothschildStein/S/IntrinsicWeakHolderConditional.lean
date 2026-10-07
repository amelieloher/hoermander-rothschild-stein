-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicWeakWordsConditional
public import RothschildStein.S.IntrinsicHolderRepresentatives
public import RothschildStein.S.WeakHolderToIntrinsic
public import RothschildStein.S.WeakHolderIntrinsicNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.S
variable {n q : ℕ}

/-- Assuming that every continuous intrinsic derivative is a weak derivative, the intrinsic Hölder class embeds in the weak Hölder class (BB Proposition 2.22, pp. 87–90). -/
theorem memWeakHolderX_of_intrinsicToWeak
    (hReverse : ∀ (V : Opens (Fin n → ℝ))
      (Y : (Fin n → ℝ) → (Fin n → ℝ)),
      ContDiffOn ℝ (⊤ : ℕ∞) Y (V : Set (Fin n → ℝ)) →
      ∀ f g : (Fin n → ℝ) → ℝ,
      ContinuousOn f (V : Set (Fin n → ℝ)) →
      ContinuousOn g (V : Set (Fin n → ℝ)) →
      hasIntrinsicDeriv V Y f g →
      hasWeakWordDeriv (fun _ : Fin 1 => Y) V [0] f g)
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin n → ℝ)))
    (k : ℕ) {α : ℝ} (hα : 0 < α) {f : (Fin n → ℝ) → ℝ}
    (hf : memHolderX w X G.d U k α f) : memWeakHolderX w X G.d U k α f := by
  obtain ⟨jet,hzero,hjet⟩ := exists_intrinsicHolder_representatives w X G.d U k α hf
  refine ⟨hf.1,fun I hI => ?_⟩
  have hs : ∀ J,J.Sublist I → J ∈ wordFamily w k := by
    intro J hJ
    exact (mem_wordFamily_iff w k J).mpr
      ((wordWeight_sublist_le w hJ).trans ((mem_wordFamily_iff w k I).mp hI))
  exact ⟨jet I,hasWeakWordDeriv_of_intrinsicToWeak hReverse U X hX I f jet hzero
    (fun J hJ => (hjet J (hs J hJ)).1)
    (fun J hJ => continuousOn_of_holderENorm_lt_top_subset Ω G hU hα (hjet J (hs J hJ)).2),
    (hjet I hI).2⟩

/-- Under the same single-field derivative implication, the intrinsic and weak Hölder norms agree (BB pp. 81, 87–90). -/
theorem holderXENorm_eq_weak_of_intrinsicToWeak
    (hReverse : ∀ (V : Opens (Fin n → ℝ))
      (Y : (Fin n → ℝ) → (Fin n → ℝ)),
      ContDiffOn ℝ (⊤ : ℕ∞) Y (V : Set (Fin n → ℝ)) →
      ∀ f g : (Fin n → ℝ) → ℝ,
      ContinuousOn f (V : Set (Fin n → ℝ)) →
      ContinuousOn g (V : Set (Fin n → ℝ)) →
      hasIntrinsicDeriv V Y f g →
      hasWeakWordDeriv (fun _ : Fin 1 => Y) V [0] f g)
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin n → ℝ)))
    (k : ℕ) {α : ℝ} (hα : 0 < α) {f : (Fin n → ℝ) → ℝ}
    (hf : memHolderX w X G.d U k α f) :
    holderXENorm w X G.d U k α f = weakHolderXENorm w X G.d U k α f := by
  exact holderXENorm_eq_weakHolderXENorm Ω U G hU w X hX k hα
    (memWeakHolderX_of_intrinsicToWeak hReverse Ω U G hU w X hX k hα hf)

end RothschildStein.S
