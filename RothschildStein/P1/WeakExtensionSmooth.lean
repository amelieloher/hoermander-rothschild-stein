-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionLocal
public import RothschildStein.P1.WeakExtensionBasic
public import RothschildStein.P1.WeakExtensionHigher

/-!
# Hölder and noncompact inputs: smooth noncompact inputs

Smooth noncompact inputs can first be cut off equal to one near every input support in the finite
operator family. The parametrix, first-order, second-order, drift and higher-order identities hold
for tests `u ∈ C_c^∞(V)`. Let `u` be smooth on `V` (`ContDiffOn ℝ ⊤ u V`) but not compactly supported. Every
operator of the finite family sees its input only on a compact subset of `V`
(`TypeOperator.exists_seesOnly`); with `K₀` the union of these supports and of `supp a`, a cutoff
`v = χ u ∈ C_c^∞(V)` agrees with `u` on an open neighbourhood `W` of `K₀`, all derivatives of `v` agree with
those of `u` on `W` (the derivatives of `χ` vanish there), so every term of the identity is unchanged and
the identity for `v` is the identity for `u`. The identities are weak identities on `V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

namespace LiftedChart

variable {n q : ℕ} {w : Fin (q + 1) → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The parametrix identity `a u = P₂ L̃u + F₂ u`, for smooth noncompact `u`**: if the
identity holds on `V` for tests, it holds for every `u` smooth on `V`. -/
theorem weakExtension_parametrix_left_smooth (hF : C.IsStandardFrame F H K hQ)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {P₂ : TypeOperator F 2} {F₂ : TypeOperator F 1}
    (hzero : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
      a ξ * f ξ = P₂.apply (sumSquaresWithDrift C.Xl f) ξ + F₂.apply f ξ)
    {u : (Fin (n + m) → ℝ) → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ))) :
    ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
      a ξ * u ξ = P₂.apply (sumSquaresWithDrift C.Xl u) ξ + F₂.apply u ξ := by
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
  have e2 : P₂.apply (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ)) =
      P₂.apply (sumSquaresWithDrift C.Xl u) :=
    hs₁.apply_congr ((sumSquaresWithDrift_eqOn C.Xl hW hWeq).mono
      (subset_union_left.trans (subset_union_left.trans hKW)))
  have e3 : F₂.apply (v : (Fin (n + m) → ℝ) → ℝ) = F₂.apply u :=
    hs₂.apply_congr (hWeq.mono (subset_union_right.trans (subset_union_left.trans hKW)))
  rw [e1, e2, e3] at h
  exact h

/-- **First-order representation, for smooth noncompact `u`**: if
`X̃_l(a φ) = F_l L̃φ + S_l φ` weakly on `V` for tests `φ`, then the same identity holds weakly on `V` for
every `u` smooth on `V`, with the pointwise actions of the type operators (they only see `u` on a
compact subset of `V`). -/
theorem weakExtension_firstOrder_smooth (hF : C.IsStandardFrame F H K hQ)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Fl : Fin q → TypeOperator F 1}
    {Sl : Fin q → TypeOperator F 0}
    (hid : ∀ (l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
        (fun ξ => (Fl l).apply (sumSquaresWithDrift C.Xl u) ξ + (Sl l).apply u ξ))
    (l : Fin q) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ))) :
    hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
      (fun ξ => (Fl l).apply (sumSquaresWithDrift C.Xl u) ξ + (Sl l).apply u ξ) := by
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
  have e2 : (Fl l).apply (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ)) =
      (Fl l).apply (sumSquaresWithDrift C.Xl u) :=
    hs₁.apply_congr ((sumSquaresWithDrift_eqOn C.Xl hW hWeq).mono
      (subset_union_left.trans (subset_union_left.trans hKW)))
  have e3 : (Sl l).apply (v : (Fin (n + m) → ℝ) → ℝ) = (Sl l).apply u :=
    hs₂.apply_congr (hWeq.mono (subset_union_right.trans (subset_union_left.trans hKW)))
  rw [e1, e2, e3] at h
  exact h

/-- **Second-order representation, for smooth noncompact `u`.** -/
theorem weakExtension_secondOrder_smooth (hF : C.IsStandardFrame F H K hQ)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Sml : Fin q → Fin q → TypeOperator F 0}
    {Smlk : Fin q → Fin q → Fin q → TypeOperator F 0} {Sml0 : Fin q → Fin q → TypeOperator F 0}
    (hid : ∀ (i l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
        (fun ξ => (Sml i l).apply (sumSquaresWithDrift C.Xl u) ξ +
          (∑ k : Fin q, (Smlk i l k).apply
            (fieldDerivative (C.Xl k.succ) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
          (Sml0 i l).apply u ξ))
    (i l : Fin q) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ))) :
    hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
      (fun ξ => (Sml i l).apply (sumSquaresWithDrift C.Xl u) ξ +
        (∑ k : Fin q, (Smlk i l k).apply
          (fieldDerivative (C.Xl k.succ) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
        (Sml0 i l).apply u ξ) := by
  have := hF.noAtoms
  obtain ⟨K₁, hK₁, hK₁V, hs₁⟩ := (Sml i l).exists_seesOnly
  obtain ⟨K₂, hK₂, hK₂V, hs₂⟩ := TypeOperator.exists_seesOnly_finset
    (Finset.univ : Finset (Fin q)) (Smlk i l)
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
  have e2 : (Sml i l).apply (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ)) =
      (Sml i l).apply (sumSquaresWithDrift C.Xl u) :=
    hs₁.apply_congr ((sumSquaresWithDrift_eqOn C.Xl hW hWeq).mono
      (subset_union_left.trans (subset_union_left.trans (subset_union_left.trans hKW))))
  have e3 : ∀ k : Fin q, (Smlk i l k).apply
      (fieldDerivative (C.Xl k.succ) (v : (Fin (n + m) → ℝ) → ℝ)) =
      (Smlk i l k).apply (fieldDerivative (C.Xl k.succ) u) := fun k =>
    (hs₂ k (Finset.mem_univ k)).apply_congr
      ((wordDerivative_eqOn C.Xl [k.succ] hW hWeq).mono
        (subset_union_right.trans (subset_union_left.trans (subset_union_left.trans hKW))))
  have e4 : (Sml0 i l).apply (v : (Fin (n + m) → ℝ) → ℝ) = (Sml0 i l).apply u :=
    hs₃.apply_congr (hWeq.mono
      (subset_union_right.trans (subset_union_left.trans hKW)))
  have e5 : (fun ξ => (Sml i l).apply (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ)) ξ +
        (∑ k : Fin q, (Smlk i l k).apply
          (fieldDerivative (C.Xl k.succ) (v : (Fin (n + m) → ℝ) → ℝ)) ξ) +
        (Sml0 i l).apply v ξ) =
      fun ξ => (Sml i l).apply (sumSquaresWithDrift C.Xl u) ξ +
        (∑ k : Fin q, (Smlk i l k).apply
          (fieldDerivative (C.Xl k.succ) u) ξ) + (Sml0 i l).apply u ξ := by
    funext ξ
    rw [e2, e4]
    simp only [e3]
  rw [e1, e5] at h
  exact h

end LiftedChart

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The higher-order representation for smooth noncompact `u`** (no drift): if
`X̃_I(a φ) = ∑_J S_J X̃_J L̃φ + ∑_K T_K X̃_K φ` weakly on `V` for tests `φ`, the same holds weakly on `V`
for every `u` smooth on `V`. -/
theorem weakExtension_higher_smooth (hF : C.IsStandardFrame F H K hQ)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} (I : List (Fin k)) {Sf Tf : List (Fin k) → TypeOperator F 0}
    (hid : ∀ u : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
        (fun ξ => (∑ J ∈ repWords k (I.length - 2),
            (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl (u : (Fin (n + m) → ℝ) → ℝ))) ξ) +
          ∑ K ∈ repWords k (I.length - 1),
            (Tf K).apply (wordDerivative C.Xl K (u : (Fin (n + m) → ℝ) → ℝ)) ξ))
    {u : (Fin (n + m) → ℝ) → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ))) :
    hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
      (fun ξ => (∑ J ∈ repWords k (I.length - 2),
          (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl u)) ξ) +
        ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (wordDerivative C.Xl K u) ξ) := by
  have := hF.noAtoms
  obtain ⟨K₁, hK₁, hK₁V, hs₁⟩ := TypeOperator.exists_seesOnly_finset (repWords k (I.length - 2)) Sf
  obtain ⟨K₂, hK₂, hK₂V, hs₂⟩ := TypeOperator.exists_seesOnly_finset (repWords k (I.length - 1)) Tf
  have hK₀ : IsCompact (K₁ ∪ K₂ ∪ tsupport (a : (Fin (n + m) → ℝ) → ℝ)) :=
    (hK₁.union hK₂).union a.hasCompactSupport
  have hK₀V : K₁ ∪ K₂ ∪ tsupport (a : (Fin (n + m) → ℝ) → ℝ) ⊆ (F.V : Set (Fin (n + m) → ℝ)) :=
    union_subset (union_subset hK₁V hK₂V) a.tsupport_subset
  obtain ⟨v, W, hW, hKW, hWV, hvu⟩ := exists_test_eq_on_nhds F.V hK₀ hK₀V hu
  have hWeq : EqOn (v : (Fin (n + m) → ℝ) → ℝ) u W := hvu
  have hs1 : K₁ ⊆ W := subset_union_left.trans (subset_union_left.trans hKW)
  have hs2 : K₂ ⊆ W := subset_union_right.trans (subset_union_left.trans hKW)
  have h := hid v
  have e1 : (fun x => a x * v x) = fun x => a x * u x := by
    funext x
    by_cases hx : x ∈ tsupport (a : (Fin (n + m) → ℝ) → ℝ)
    · rw [hvu x (hKW (Or.inr hx))]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have e2 : ∀ J ∈ repWords k (I.length - 2),
      (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl (v : (Fin (n + m) → ℝ) → ℝ))) =
        (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl u)) := fun J hJ =>
    (hs₁ J hJ).apply_congr
      ((wordDerivative_eqOn C.Xl J hW (sumSquares_eqOn C.Xl hW hWeq)).mono hs1)
  have e3 : ∀ K ∈ repWords k (I.length - 1),
      (Tf K).apply (wordDerivative C.Xl K (v : (Fin (n + m) → ℝ) → ℝ)) =
        (Tf K).apply (wordDerivative C.Xl K u) := fun K hK =>
    (hs₂ K hK).apply_congr ((wordDerivative_eqOn C.Xl K hW hWeq).mono hs2)
  have e4 : (fun ξ => (∑ J ∈ repWords k (I.length - 2),
          (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl (v : (Fin (n + m) → ℝ) → ℝ))) ξ) +
        ∑ K ∈ repWords k (I.length - 1),
          (Tf K).apply (wordDerivative C.Xl K (v : (Fin (n + m) → ℝ) → ℝ)) ξ) =
      fun ξ => (∑ J ∈ repWords k (I.length - 2),
          (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl u)) ξ) +
        ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (wordDerivative C.Xl K u) ξ := by
    funext ξ
    congr 1
    · exact Finset.sum_congr rfl fun J hJ => by rw [e2 J hJ]
    · exact Finset.sum_congr rfl fun K hK => by rw [e3 K hK]
  rw [e1, e4] at h
  exact h

end LiftedChart

end RothschildStein.P1
