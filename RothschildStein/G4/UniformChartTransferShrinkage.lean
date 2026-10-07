-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ChartDataRestriction
public import RothschildStein.G4.ChartTransferPackage

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Function

namespace RothschildStein.G4

/-- The proved actual chart-transfer implication with both analytic and
trajectory packages on one common domain at the original radius. -/
def ChartTransferRule (m n s : ℕ) (α a c D : ℝ) : Prop :=
  ∀ (w : Fin m → ℕ+) (A B : Fin n → Fin m), Injective A →
    (∀ i, (w (A i) : ℕ) ≤ s) → (∀ i, (w (B i) : ℕ) ≤ s) →
  ∀ (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ)),
    (∀ J, ContinuousOn (Z J) Ω) →
  ∀ (F G : (Fin n → ℝ) → (Fin n → ℝ)) (r κ : ℝ),
    0 < r → r ≤ 1 → 0 ≤ κ → (n : ℝ) * κ ≤ 1 / 4 →
    ChartAnalyticBounds Ω w Z B F (weightedBox (w ∘ B) (a * r)) r κ D →
    ChartAnalyticBounds Ω w Z A G (weightedBox (w ∘ A) (a * r)) r κ D →
    InjOn G (weightedBox (w ∘ A) (α * r)) →
  ∀ (x : Fin n → ℝ), G 0 = x → frameDet Z B x ≠ 0 →
  ∀ v : Fin m → ℝ, v ∈ weightedBox w (c * r) →
  ∀ (ΓF ΓG : (Fin n → ℝ) → ℝ → (Fin n → ℝ)),
    ChartTrajectories Ω Z B F (weightedBox (w ∘ B) (a * r)) x v ΓF →
    ChartTrajectories Ω Z A G (weightedBox (w ∘ A) (a * r)) x 0 ΓG →
    InjOn F (weightedBox (w ∘ B) (c * r))

/-- The actual transfer can use a common fixed analytic domain;
all its internal restrictions retain the original radius and constants
(BB pp. 456–458). -/
theorem exists_uniform_common_domain_chart_transfer {m n s : ℕ} {α a D : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ChartTransferRule m n s α a c D := by
  have hmin : 0 < min α a := lt_min hα ha
  obtain ⟨β, c, hβ, hβα, hc, hca, htransfer⟩ :=
    exists_uniform_chart_transfer_with_trajectories (m := m) (n := n) (s := s)
      hmin ((min_le_left _ _).trans hα1) ha ha1 hD
  have hβa : β ≤ a := hβα.trans (min_le_right _ _)
  have hcm : c ≤ a := hca.le.trans (by linarith)
  refine ⟨c, hc, hcm.trans ha1, ?_⟩
  intro w A B hA hwA hwB Z Ω hZ F G r κ hr hr1 hκ hsmall hF hG hinj x hGzero hBx
    v hv ΓF ΓG hΓF hΓG
  have hsource := weightedBox_subset_of_radius_le (w ∘ A)
    (mul_nonneg hβ.le hr.le) (mul_le_mul_of_nonneg_right hβa hr.le)
  have htarget := weightedBox_subset_of_radius_le (w ∘ B)
    (mul_nonneg hc.le hr.le) (mul_le_mul_of_nonneg_right hcm hr.le)
  have hold := weightedBox_subset_of_radius_le (w ∘ A)
    (mul_nonneg hmin.le hr.le) (mul_le_mul_of_nonneg_right (min_le_left α a) hr.le)
  exact htransfer w A B hA hwA hwB Z Ω hZ F G r κ hr hr1 hκ hsmall hF
    (chartAnalyticBounds_mono hG hsource) (hinj.mono hold) x hGzero hBx v hv ΓF ΓG
    (chartTrajectories_mono hΓF htarget) (chartTrajectories_mono hΓG hsource)

/-- Choose one positive shrinkage map before all fields, charts
and frames. It carries the proved actual transfer rule at every positive
unit input radius, allowing the finite-iteration uniform minimum (BB p. 458). -/
theorem exists_uniform_chart_transfer_shrinkage {m n s : ℕ} {a D : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D) :
    ∃ f : ℝ → ℝ, ∀ α : ℝ, 0 < α → α ≤ 1 →
      0 < f α ∧ f α ≤ 1 ∧ ChartTransferRule m n s α a (f α) D := by
  classical
  have hex : ∀ α : {α : ℝ // 0 < α ∧ α ≤ 1},
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ChartTransferRule m n s α.val a c D :=
    fun α => exists_uniform_common_domain_chart_transfer α.property.1 α.property.2 ha ha1 hD
  let f := fun α : ℝ => if h : 0 < α ∧ α ≤ 1 then Classical.choose (hex ⟨α, h⟩) else 1
  refine ⟨f, ?_⟩
  intro α hα hα1
  simpa only [f, dite_eq_left (show 0 < α ∧ α ≤ 1 from ⟨hα, hα1⟩)] using
    Classical.choose_spec (hex ⟨α, ⟨hα, hα1⟩⟩)

end RothschildStein.G4
