-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SpatialChartData
public import RothschildStein.G4.FinitePositiveMinimum

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators Topology
namespace RothschildStein.G4

/-- A full chart package on an arbitrary compact spatial patch.
The selected maps retain an actual local flow data at every center;
no continuity of the choice of spatial buffer is asserted. -/
structure CompactSpatialChartData {P : Type*} {m n : ℕ}
    (Ω K : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (t : ℝ) where
  c : ℝ
  r₀ : ℝ
  D : ℝ
  κ : ℝ
  c_pos : 0 < c
  c_le_one : c ≤ 1
  radius_pos : 0 < r₀
  radius_le_one : r₀ ≤ 1
  D_pos : 0 < D
  κ_pos : 0 < κ
  κ_small : (n : ℝ) * κ ≤ 1 / 4
  Φ : (Fin n → ℝ) → P → (Fin n → Fin m) →
    (((Fin (n+m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ)
  provenance : ∀ x ∈ K, ∃ A : SpatialChartData Ω w Z t,
    x ∈ A.U ∧ Φ x = A.Φ
  charts : ∀ p, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
    ∀ B, IsSuboptimal (Z p) w B x t r → ∀ v ∈ weightedBox w (c*r),
    let F := fun u => Φ x p B ((Fin.append u v,x),1)
    let Γ := fun u τ => Φ x p B ((Fin.append u v,x),τ)
    InjOn F (weightedBox (w ∘ B) (c*r)) ∧
    ChartAnalyticBounds Ω w (Z p) B F (weightedBox (w ∘ B) (c*r)) r κ D ∧
    ChartTrajectories Ω (Z p) B F (weightedBox (w ∘ B) (c*r)) x v Γ ∧
    (v = 0 → F 0 = x) ∧
    ∀ u ∈ weightedBox (w ∘ B) (c*r),
      |frameDet (Z p) B x|/4 ≤ |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
      |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤ 4*|frameDet (Z p) B x|

/-- Finitely many actual spatial flow buffers give common positive
coordinate and scale radii on an arbitrary compact patch. -/
theorem exists_compact_spatial_chart_data {P : Type*} {m n : ℕ}
    (hn : 0 < n) (Ω K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (w : Fin m → ℕ+) (Z : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (t : ℝ)
    (hlocal : ∀ x ∈ K, ∃ A : SpatialChartData Ω w Z t, x ∈ A.U) :
    Nonempty (CompactSpatialChartData Ω K w Z t) := by
  classical
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let κ : ℝ := 1 / (4*(n : ℝ))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκeq : (n : ℝ)*κ = 1/4 := by dsimp [κ]; field_simp
  rcases K.eq_empty_or_nonempty with hEmpty | hne
  · exact ⟨{
      c := 1, r₀ := 1, D := 1, κ := κ, c_pos := zero_lt_one,
      c_le_one := le_rfl, radius_pos := zero_lt_one, radius_le_one := le_rfl,
      D_pos := zero_lt_one, κ_pos := hκ, κ_small := hκeq.le,
      Φ := fun _ _ _ _ => 0,
      provenance := by simp [hEmpty], charts := by simp [hEmpty] }⟩
  choose A hA using fun x : K => hlocal x x.property
  obtain ⟨T, hcover⟩ := hK.elim_finite_subcover (fun x : K => (A x).U)
    (fun x => (A x).isOpen_U) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩, hA ⟨x,hx⟩⟩)
  obtain ⟨a, ha, hac⟩ := exists_finite_positive_lower_bound T
    (fun i => (A i).c) (fun i _ => (A i).c_pos)
  obtain ⟨r₀, hr₀, hrr⟩ := exists_finite_positive_lower_bound T
    (fun i => (A i).r₀) (fun i _ => (A i).radius_pos)
  let c := min a 1
  let R := min r₀ 1
  let D := 1 + ∑ i ∈ T, (A i).D
  have hD : 0 < D := by
    have hh : 0 ≤ ∑ i ∈ T, (A i).D := Finset.sum_nonneg (fun i _ => (A i).D_pos.le)
    dsimp [D]; linarith
  have hselect : ∀ x : K, ∃ i ∈ T, x.val ∈ (A i).U := by
    intro x
    rcases mem_iUnion.mp (hcover x.property) with ⟨i, hi⟩
    rcases mem_iUnion.mp hi with ⟨hiT, hiU⟩
    exact ⟨i, hiT, hiU⟩
  choose ix hiT hiU using hselect
  let Φ := fun x : Fin n → ℝ => if hx : x ∈ K then (A (ix ⟨x,hx⟩)).Φ
    else fun _ _ _ => 0
  refine ⟨{
    c := c, r₀ := R, D := D, κ := κ,
    c_pos := lt_min ha zero_lt_one, c_le_one := min_le_right _ _,
    radius_pos := lt_min hr₀ zero_lt_one, radius_le_one := min_le_right _ _,
    D_pos := hD, κ_pos := hκ, κ_small := hκeq.le, Φ := Φ,
    provenance := ?_, charts := ?_ }⟩
  · intro x hx
    refine ⟨A (ix ⟨x,hx⟩), hiU ⟨x,hx⟩, ?_⟩
    simp only [Φ, dite_eq_left hx]
  · intro p x hx r hr hR B hB v hv F Γ
    let i := ix ⟨x,hx⟩
    have hi : i ∈ T := hiT ⟨x,hx⟩
    have hcc : c ≤ (A i).c := (min_le_left _ _).trans (hac i hi)
    have hrad : r ≤ (A i).r₀ := hR.trans ((min_le_left _ _).trans (hrr i hi))
    have hv' := weightedBox_subset_of_radius_le w
      (mul_nonneg (lt_min ha zero_lt_one).le hr.le)
      (mul_le_mul_of_nonneg_right hcc hr.le) hv
    have hh := (A i).charts p x (hiU ⟨x,hx⟩) r hr hrad B hB v hv'
    have hQ : weightedBox (w ∘ B) (c*r) ⊆ weightedBox (w ∘ B) ((A i).c*r) :=
      weightedBox_subset_of_radius_le _ (mul_nonneg (lt_min ha zero_lt_one).le hr.le)
        (mul_le_mul_of_nonneg_right hcc hr.le)
    have hDle : (A i).D ≤ D := by
      have hh' := Finset.single_le_sum (fun j _ => (A j).D_pos.le) hi
      dsimp [D]; linarith
    have hκle : (A i).κ ≤ κ := by
      have hh' := (A i).κ_small
      apply (le_div_iff₀ (by positivity : 0 < 4*(n : ℝ))).mpr
      nlinarith
    have hΦ : Φ x = (A i).Φ := by simp only [Φ, dite_eq_left hx, i]
    dsimp only [F, Γ]
    rw [hΦ]
    exact ⟨hh.1.mono hQ,
      chartAnalyticBounds_enlarge_constants hr.le (chartAnalyticBounds_mono hh.2.1 hQ) hκle hDle,
      chartTrajectories_mono hh.2.2.1 hQ, hh.2.2.2.1,
      fun u hu => hh.2.2.2.2 u (hQ hu)⟩

end RothschildStein.G4
