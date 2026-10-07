-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberAssemblyInterfaces
public import RothschildStein.L1.StarredFiberGeometry

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open RothschildStein.L1.StarredFiber
namespace RothschildStein.L1.CoordinateApproximationData

/-- The finitely many paired chart families of a compact
buffer cover carry common positive radii: a horizontal radius `a`, one shift
radius `bo` valid for the shifted original geometry of every family, one inner
radius `bl` valid for the zero-shift lifted geometry of every family, and a
common application radius `r₀` (BB pp. 519-521). -/
theorem exists_starredFiber_uniform_chart_data {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData k s (n+m) w} (A : CoordinateApproximationData L M)
    (hbuf : CompactChartBuffers A) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ A.U) :
    ∃ N : ℕ, ∃ zo : Fin N → Fin n → ℝ, ∃ zl : Fin N → Fin (n + m) → ℝ,
    ∃ Fo : ∀ i, JointShortChartFamily (s := s) w
      (basePoint (n := n) (m := m) '' (L.U : Set (Fin (n + m) → ℝ))) X (zo i) (1/2),
    ∃ Fl : ∀ i, JointShortChartFamily (s := s) w
      (L.U : Set (Fin (n + m) → ℝ)) (triangularLift X L.P) (zl i) t,
      (∀ η ∈ K, ∃ i, basePoint η ∈ closedBall (zo i) ((Fo i).R / 16) ∧
        η ∈ closedBall (zl i) ((Fl i).R / 16)) ∧
      ∃ a bo bl r₀ : ℝ, 0 < a ∧ a ≤ 1/2 ∧ 0 < bo ∧ bo ≤ a/8 ∧ 0 < bl ∧ 0 < r₀ ∧
        ∀ i, a ≤ (Fo i).a₀ ∧ a ≤ (Fl i).a₀ ∧ r₀ ≤ (Fo i).r₀ ∧ r₀ ≤ (Fl i).r₀ ∧
          ShiftedGeometry (Fo i) a bo ∧ ZeroShiftGeometry (Fl i) a bl := by
  obtain ⟨N,zo,zl,Fo,Fl,hcov⟩ := hbuf t ht ht1 K hK hKU
  refine ⟨N,zo,zl,Fo,Fl,hcov,?_⟩
  obtain ⟨a₁,ha₁,hle₁⟩ := exists_pos_le_of_pos (fun i => (Fo i).a₀) (fun i => (Fo i).a₀_pos)
  obtain ⟨a₂,ha₂,hle₂⟩ := exists_pos_le_of_pos (fun i => (Fl i).a₀) (fun i => (Fl i).a₀_pos)
  have ha : 0 < min (min a₁ a₂) (1/2) := lt_min (lt_min ha₁ ha₂) (by norm_num)
  have haFo : ∀ i, min (min a₁ a₂) (1/2) ≤ (Fo i).a₀ := fun i =>
    ((min_le_left _ _).trans (min_le_left _ _)).trans (hle₁ i)
  have haFl : ∀ i, min (min a₁ a₂) (1/2) ≤ (Fl i).a₀ := fun i =>
    ((min_le_left _ _).trans (min_le_right _ _)).trans (hle₂ i)
  choose bs hbs0 _hbs4 hbsg using fun i => exists_shiftedGeometry (Fo i) ha (haFo i)
  choose cs hcs0 _hcs4 hcsg using fun i => exists_zeroShiftGeometry (Fl i) ha (haFl i)
  obtain ⟨b₁,hb₁,hble⟩ := exists_pos_le_of_pos bs hbs0
  obtain ⟨c₁,hc₁,hcle⟩ := exists_pos_le_of_pos cs hcs0
  obtain ⟨r₁,hr₁,hrle⟩ := exists_pos_le_of_pos (fun i => min (Fo i).r₀ (Fl i).r₀)
    (fun i => lt_min (Fo i).r₀_pos (Fl i).r₀_pos)
  have hbo : 0 < min b₁ (min (min a₁ a₂) (1/2) / 8) := lt_min hb₁ (by positivity)
  refine ⟨min (min a₁ a₂) (1/2),min b₁ (min (min a₁ a₂) (1/2) / 8),c₁,r₁,ha,min_le_right _ _,
    hbo,min_le_right _ _,hc₁,hr₁,fun i => ⟨haFo i,haFl i,(hrle i).trans (min_le_left _ _),
      (hrle i).trans (min_le_right _ _),(hbsg i).mono hbo.le
        ((min_le_left _ _).trans (hble i)),(hcsg i).mono (hcle i)⟩⟩

end RothschildStein.L1.CoordinateApproximationData
