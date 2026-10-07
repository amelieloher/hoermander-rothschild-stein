-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionSmooth
public import RothschildStein.P1.WeakExtensionNoDriftBasic

/-!
# Hölder and noncompact inputs, no drift: smooth noncompact inputs

The no-drift counterparts of `weakExtension_parametrix_left_smooth`, `weakExtension_firstOrder_smooth`,
`weakExtension_secondOrder_smooth` (alphabet `Fin k`, `L̃ = sumSquares`): if the parametrix identity resp. a
first- or second-order representation holds for tests, it holds for every `u` smooth on `V` (not nec. compactly supported), by cutting `u` off
equal to one near the union of the compact input supports of the finitely many operators and of `supp a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The parametrix identity `a u = P₂ L̃u + F₂ u`, for smooth noncompact `u`, no
drift**: if the identity holds on `V` for tests, it holds for every `u` smooth on `V`. -/
theorem weakExtension_parametrix_left_smooth_noDrift (hF : C.IsStandardFrame F H K hQ)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {P₂ : TypeOperator F 2} {F₂ : TypeOperator F 1}
    (hzero : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
      a ξ * f ξ = P₂.apply (sumSquares C.Xl f) ξ + F₂.apply f ξ)
    {u : (Fin (n + m) → ℝ) → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ))) :
    ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
      a ξ * u ξ = P₂.apply (sumSquares C.Xl u) ξ + F₂.apply u ξ := by
  have := hF.noAtoms
  obtain ⟨K₁, hK₁, hK₁V, hs₁⟩ := P₂.exists_seesOnly
  obtain ⟨K₂, hK₂, hK₂V, hs₂⟩ := F₂.exists_seesOnly
  have hK₀ : IsCompact (K₁ ∪ K₂ ∪ tsupport (a : (Fin (n + m) → ℝ) → ℝ)) :=
    (hK₁.union hK₂).union a.hasCompactSupport
  have hK₀V : K₁ ∪ K₂ ∪ tsupport (a : (Fin (n + m) → ℝ) → ℝ) ⊆ (F.V : Set (Fin (n + m) → ℝ)) :=
    union_subset (union_subset hK₁V hK₂V) a.tsupport_subset
  obtain ⟨v, W, hW, hKW, hWV, hvu⟩ := exists_test_eq_on_nhds F.V hK₀ hK₀V hu
  have hWeq : EqOn (v : (Fin (n + m) → ℝ) → ℝ) u W := hvu
  intro ξ hξ
  have h := hzero v ξ hξ
  have e1 : a ξ * v ξ = a ξ * u ξ := by
    by_cases hx : ξ ∈ tsupport (a : (Fin (n + m) → ℝ) → ℝ)
    · rw [hvu ξ (hKW (Or.inr hx))]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have e2 : P₂.apply (sumSquares C.Xl (v : (Fin (n + m) → ℝ) → ℝ)) =
      P₂.apply (sumSquares C.Xl u) :=
    hs₁.apply_congr ((sumSquares_eqOn C.Xl hW hWeq).mono
      (subset_union_left.trans (subset_union_left.trans hKW)))
  have e3 : F₂.apply (v : (Fin (n + m) → ℝ) → ℝ) = F₂.apply u :=
    hs₂.apply_congr (hWeq.mono (subset_union_right.trans (subset_union_left.trans hKW)))
  rw [e1, e2, e3] at h
  exact h

/-- **First-order representation, for smooth noncompact `u`, no drift**: if
`X̃_l(a φ) = F_l L̃φ + S_l φ` weakly on `V` for tests `φ`, then the same identity holds weakly on `V` for every
`u` smooth on `V`, with the pointwise actions of the type operators. -/
theorem weakExtension_firstOrder_smooth_noDrift (hF : C.IsStandardFrame F H K hQ)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Fl : Fin k → TypeOperator F 1}
    {Sl : Fin k → TypeOperator F 0}
    (hid : ∀ (l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
        (fun ξ => (Fl l).apply (sumSquares C.Xl u) ξ + (Sl l).apply u ξ))
    (l : Fin k) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ))) :
    hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
      (fun ξ => (Fl l).apply (sumSquares C.Xl u) ξ + (Sl l).apply u ξ) := by
  have := hF.noAtoms
  obtain ⟨K₁, hK₁, hK₁V, hs₁⟩ := (Fl l).exists_seesOnly
  obtain ⟨K₂, hK₂, hK₂V, hs₂⟩ := (Sl l).exists_seesOnly
  have hK₀ : IsCompact (K₁ ∪ K₂ ∪ tsupport (a : (Fin (n + m) → ℝ) → ℝ)) :=
    (hK₁.union hK₂).union a.hasCompactSupport
  have hK₀V : K₁ ∪ K₂ ∪ tsupport (a : (Fin (n + m) → ℝ) → ℝ) ⊆ (F.V : Set (Fin (n + m) → ℝ)) :=
    union_subset (union_subset hK₁V hK₂V) a.tsupport_subset
  obtain ⟨v, W, hW, hKW, hWV, hvu⟩ := exists_test_eq_on_nhds F.V hK₀ hK₀V hu
  have hWeq : EqOn (v : (Fin (n + m) → ℝ) → ℝ) u W := hvu
  have h := hid l v
  have e1 : (fun x => a x * v x) = fun x => a x * u x := by
    funext x
    by_cases hx : x ∈ tsupport (a : (Fin (n + m) → ℝ) → ℝ)
    · rw [hvu x (hKW (Or.inr hx))]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have e2 : (Fl l).apply (sumSquares C.Xl (v : (Fin (n + m) → ℝ) → ℝ)) =
      (Fl l).apply (sumSquares C.Xl u) :=
    hs₁.apply_congr ((sumSquares_eqOn C.Xl hW hWeq).mono
      (subset_union_left.trans (subset_union_left.trans hKW)))
  have e3 : (Sl l).apply (v : (Fin (n + m) → ℝ) → ℝ) = (Sl l).apply u :=
    hs₂.apply_congr (hWeq.mono (subset_union_right.trans (subset_union_left.trans hKW)))
  rw [e1, e2, e3] at h
  exact h

/-- **Second-order representation, for smooth noncompact `u`, no drift.** -/
theorem weakExtension_secondOrder_smooth_noDrift (hF : C.IsStandardFrame F H K hQ)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Sml : Fin k → Fin k → TypeOperator F 0}
    {Smlk : Fin k → Fin k → Fin k → TypeOperator F 0} {Sml0 : Fin k → Fin k → TypeOperator F 0}
    (hid : ∀ (i l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
        (fun ξ => (Sml i l).apply (sumSquares C.Xl u) ξ +
          (∑ j : Fin k, (Smlk i l j).apply
            (fieldDerivative (C.Xl j) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
          (Sml0 i l).apply u ξ))
    (i l : Fin k) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ))) :
    hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
      (fun ξ => (Sml i l).apply (sumSquares C.Xl u) ξ +
        (∑ j : Fin k, (Smlk i l j).apply
          (fieldDerivative (C.Xl j) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
        (Sml0 i l).apply u ξ) := by
  have := hF.noAtoms
  obtain ⟨K₁, hK₁, hK₁V, hs₁⟩ := (Sml i l).exists_seesOnly
  obtain ⟨K₂, hK₂, hK₂V, hs₂⟩ := TypeOperator.exists_seesOnly_finset
    (Finset.univ : Finset (Fin k)) (Smlk i l)
  obtain ⟨K₃, hK₃, hK₃V, hs₃⟩ := (Sml0 i l).exists_seesOnly
  have hK₀ : IsCompact (K₁ ∪ K₂ ∪ K₃ ∪ tsupport (a : (Fin (n + m) → ℝ) → ℝ)) :=
    ((hK₁.union hK₂).union hK₃).union a.hasCompactSupport
  have hK₀V : K₁ ∪ K₂ ∪ K₃ ∪ tsupport (a : (Fin (n + m) → ℝ) → ℝ) ⊆
      (F.V : Set (Fin (n + m) → ℝ)) :=
    union_subset (union_subset (union_subset hK₁V hK₂V) hK₃V) a.tsupport_subset
  obtain ⟨v, W, hW, hKW, hWV, hvu⟩ := exists_test_eq_on_nhds F.V hK₀ hK₀V hu
  have hWeq : EqOn (v : (Fin (n + m) → ℝ) → ℝ) u W := hvu
  have h := hid i l v
  have e1 : (fun x => a x * v x) = fun x => a x * u x := by
    funext x
    by_cases hx : x ∈ tsupport (a : (Fin (n + m) → ℝ) → ℝ)
    · rw [hvu x (hKW (Or.inr hx))]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have e2 : (Sml i l).apply (sumSquares C.Xl (v : (Fin (n + m) → ℝ) → ℝ)) =
      (Sml i l).apply (sumSquares C.Xl u) :=
    hs₁.apply_congr ((sumSquares_eqOn C.Xl hW hWeq).mono
      (subset_union_left.trans (subset_union_left.trans (subset_union_left.trans hKW))))
  have e3 : ∀ j : Fin k, (Smlk i l j).apply
      (fieldDerivative (C.Xl j) (v : (Fin (n + m) → ℝ) → ℝ)) =
      (Smlk i l j).apply (fieldDerivative (C.Xl j) u) := fun j =>
    (hs₂ j (Finset.mem_univ j)).apply_congr
      ((wordDerivative_eqOn C.Xl [j] hW hWeq).mono
        (subset_union_right.trans (subset_union_left.trans (subset_union_left.trans hKW))))
  have e4 : (Sml0 i l).apply (v : (Fin (n + m) → ℝ) → ℝ) = (Sml0 i l).apply u :=
    hs₃.apply_congr (hWeq.mono
      (subset_union_right.trans (subset_union_left.trans hKW)))
  have e5 : (fun ξ => (Sml i l).apply (sumSquares C.Xl (v : (Fin (n + m) → ℝ) → ℝ)) ξ +
        (∑ j : Fin k, (Smlk i l j).apply
          (fieldDerivative (C.Xl j) (v : (Fin (n + m) → ℝ) → ℝ)) ξ) +
        (Sml0 i l).apply v ξ) =
      fun ξ => (Sml i l).apply (sumSquares C.Xl u) ξ +
        (∑ j : Fin k, (Smlk i l j).apply (fieldDerivative (C.Xl j) u) ξ) +
          (Sml0 i l).apply u ξ := by
    funext ξ
    rw [e2, e4]
    simp only [e3]
  rw [e1, e5] at h
  exact h

end LiftedChart

end RothschildStein.P1
