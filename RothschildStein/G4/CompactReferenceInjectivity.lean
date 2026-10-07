-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.UniformReferenceInjectivity
public import RothschildStein.G4.FiniteReferenceCover

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology

namespace RothschildStein.G4

/-- The local reference-neighborhood hypotheses:
a fixed reference frame and radius stay suboptimal nearby, and its actual
zero-shift chart is injective on one fixed weighted box there. -/
def ReferenceChartNeighborhoods {P : Type*} [TopologicalSpace P] {m n : ℕ}
    (K : Set P) (w : Fin m → ℕ+)
    (Z : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (F : P → (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (x : P → (Fin n → ℝ)) (t : ℝ) : Prop :=
  ∀ p ∈ K, ∃ B : Fin n → Fin m, ∃ R α : ℝ, ∃ U : Set P,
    0 < R ∧ R ≤ 1 ∧ 0 < α ∧ α ≤ 1 ∧ U ∈ 𝓝 p ∧
      ∀ q ∈ K, q ∈ U → IsSuboptimal (Z q) w B (x q) t R ∧
        InjOn (F q B 0) (weightedBox (w ∘ B) (α * R))

/-- Under the local reference-neighborhood hypotheses and same-family chart
data, compactness gives a common injective-box radius. Reference-frame
transfer then gives one final radius for every patch, while each patch
retains its own reference scale (BB pp. 453–458). -/
theorem exists_compact_uniform_chart_injectivity_of_reference_neighborhoods
    {P : Type*} [TopologicalSpace P] {m n s : ℕ} {K : Set P} (hK : IsCompact K)
    (w : Fin m → ℕ+) (hw : ∀ J, (w J : ℕ) ≤ s)
    (Z : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ))
    (hZ : ∀ p ∈ K, ∀ J, ContinuousOn (Z p J) Ω)
    (F : P → (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (Γ : P → (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (x : P → (Fin n → ℝ)) {a D κ t : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D)
    (hκ : 0 ≤ κ) (hsmall : (n : ℝ) * κ ≤ 1 / 4) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hdata : ∀ p ∈ K, ∀ B r, 0 < r → r ≤ 1 → IsSuboptimal (Z p) w B (x p) t r →
      ∀ v ∈ weightedBox w (a * r),
        ChartAnalyticBounds Ω w (Z p) B (F p B v) (weightedBox (w ∘ B) (a * r)) r κ D ∧
        ChartTrajectories Ω (Z p) B (F p B v) (weightedBox (w ∘ B) (a * r)) (x p) v (Γ p B v) ∧
        (v = 0 → F p B v 0 = x p))
    (href : ReferenceChartNeighborhoods K w Z F x t) :
    ∃ r₀ c : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < c ∧ c ≤ a ∧
      ∀ p ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B, IsSuboptimal (Z p) w B (x p) t r →
      ∀ v ∈ weightedBox w (c * r), InjOn (F p B v) (weightedBox (w ∘ B) (c * r)) := by
  classical
  have href' : ∀ p : K, ∃ B : Fin n → Fin m, ∃ R α : ℝ, ∃ U : Set P,
      0 < R ∧ R ≤ 1 ∧ 0 < α ∧ α ≤ 1 ∧ U ∈ 𝓝 p.val ∧
        ∀ q ∈ K, q ∈ U → IsSuboptimal (Z q) w B (x q) t R ∧
          InjOn (F q B 0) (weightedBox (w ∘ B) (α * R)) := fun p => href p.val p.property
  choose B R α U hR hR1 hα hα1 hU hlocal using href'
  obtain ⟨qset, hcover⟩ := hK.elim_nhds_subcover'
    (fun p hp => U ⟨p, hp⟩) (fun p hp => hU ⟨p, hp⟩)
  obtain ⟨r₀, hr₀, hr₀1, hrR⟩ := exists_positive_finset_reference_bound qset R (fun q _ => hR q)
  obtain ⟨α₀, hα₀, hα₀1, hαmin⟩ := exists_positive_finset_reference_bound qset α (fun q _ => hα q)
  obtain ⟨c, hc, hca, htransfer⟩ := exists_uniform_injectivity_from_reference_frame
    (m := m) (n := n) (s := s) hα₀ hα₀1 ha ha1 hD
  refine ⟨r₀, c, hr₀, hr₀1, hc, hca, ?_⟩
  intro p hp r hr hrr Btarget hsub v hv
  obtain ⟨q, hqU⟩ := mem_iUnion.mp (hcover hp)
  obtain ⟨hq, hpU⟩ := mem_iUnion.mp hqU
  obtain ⟨hsubRef, hinjRef⟩ := hlocal q p hp hpU
  have hinjSmall : InjOn (F p (B q) 0) (weightedBox (w ∘ B q) (α₀ * R q)) :=
    hinjRef.mono (weightedBox_subset_of_radius_le _ (mul_nonneg hα₀.le (hR q).le)
      (mul_le_mul_of_nonneg_right (hαmin q hq) (hR q).le))
  exact htransfer w hw (Z p) Ω (hZ p hp) (F p) (Γ p) (x p) κ t hκ hsmall ht ht1
    (hdata p hp) (R q) (B q) (hR q) (hR1 q) hsubRef hinjSmall
    r Btarget hr (hrr.trans (hrR q hq)) hsub v hv

end RothschildStein.G4
