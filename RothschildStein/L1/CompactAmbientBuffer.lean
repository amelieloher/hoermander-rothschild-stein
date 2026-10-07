-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LocalFieldBuffer
public import RothschildStein.G4.FirstExit

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators ENNReal

namespace RothschildStein.L1

/-- Small ambient controlled curves from a compact set stay
inside a smooth coefficient patch. The ambient domain is never replaced
by the patch (BB pp. 519–522; compact-chart uniformity gap fill). -/
theorem exists_compact_ambient_curve_buffer {a n : ℕ}
    {U K : Set (Fin n → ℝ)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U) (w : Fin a → ℕ+) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ Ω : Set (Fin n → ℝ), ∀ δ : ℝ, δ ≤ r₀ →
        ∀ γ : ℝ → (Fin n → ℝ), isControlledCurve Ω w X δ γ → γ 0 ∈ K →
          MapsTo γ (Icc (0 : ℝ) 1) U := by
  classical
  have hex := fun z : K => G4.exists_local_field_buffer hU hX (hKU z.property)
  choose R hR hRU P hP _hLip hbound using hex
  let ρ : K → ℝ := fun z => min 1 (R z / (4 * (1 + a * P z)))
  have hρ : ∀ z, 0 < ρ z := by
    intro z
    have hzR := hR z
    have hzP := hP z
    dsimp [ρ]
    positivity
  obtain ⟨T, hcover⟩ := hK.elim_finite_subcover (fun z : K => ball z.val (R z / 4))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr
      ⟨⟨x, hx⟩, mem_ball_self (div_pos (hR ⟨x, hx⟩) (by norm_num))⟩)
  let S : Finset ℝ := insert 1 (T.image ρ)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hpos : ∀ c ∈ S, 0 < c := by
    intro c hc
    rcases Finset.mem_insert.mp hc with he | hc
    · simpa only [he] using (zero_lt_one : (0 : ℝ) < 1)
    · obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hc
      exact hρ z
  refine ⟨S.min' hS, hpos _ (Finset.min'_mem S hS),
    Finset.min'_le S 1 (Finset.mem_insert_self _ _), ?_⟩
  intro Ω δ hδ γ hγ hγK
  obtain ⟨z, hz, hγz⟩ := mem_iUnion₂.mp (hcover hγK)
  have hδρ : δ ≤ ρ z := hδ.trans (Finset.min'_le S (ρ z)
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z, hz, rfl⟩)))
  have hδ1 : δ ≤ 1 := hδρ.trans (min_le_left _ _)
  have hA : 0 ≤ (a : ℝ) * P z := mul_nonneg (Nat.cast_nonneg _) (hP z).le
  have hcost : δ * ((a : ℝ) * P z) < R z / 2 := by
    have hdiv : δ ≤ R z / (4 * (1 + (a : ℝ) * P z)) :=
      hδρ.trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < 4 * (1 + (a : ℝ) * P z))).mp hdiv
    nlinarith [hγ.1]
  have hnear : ‖γ 0 - z.val‖ < R z / 4 := by
    simpa only [mem_ball, dist_eq_norm] using hγz
  have hb : ∀ v, ‖v - γ 0‖ ≤ R z / 2 → ∑ i, ‖X i v‖ ≤ (a : ℝ) * P z := by
    intro v hv
    apply hbound z v
    rw [mem_closedBall, dist_eq_norm]
    have ht := norm_add_le (v - γ 0) (γ 0 - z.val)
    have he : v - γ 0 + (γ 0 - z.val) = v - z.val := by abel
    rw [he] at ht
    linarith [hR z]
  have hstay := G4.controlledCurve_stays_ball hγ hδ1 hA (half_pos (hR z)) hcost hb
  intro t ht
  apply hRU z
  rw [mem_closedBall, dist_eq_norm]
  have hdist : ‖γ t - γ 0‖ < R z / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hstay t ht
  have hh := norm_add_le (γ t - γ 0) (γ 0 - z.val)
  have he : γ t - γ 0 + (γ 0 - z.val) = γ t - z.val := by abel
  rw [he] at hh
  linarith [hR z]

end RothschildStein.L1
