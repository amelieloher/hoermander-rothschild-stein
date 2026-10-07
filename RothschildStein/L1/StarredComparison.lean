-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberAssemblyInterfaces
public import RothschildStein.L1.StarredComparisonCompact
public import RothschildStein.L1.CoordinateBallFacts
public import RothschildStein.L1.CompactDomainBallEquality
public import RothschildStein.L1.ProjectedFreePatch

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.L1.CoordinateApproximationData

/-- Compact-uniform comparison of
ordinary control balls (ambient domains) with starred balls (free patches) at
small radii, with one threshold `r₁` and one constant `C ≥ 1`: ordinary and starred
distances agree on the nose below the first-exit radius (domain equality), `d* ≤ d`,
and `d ≤ C d*` on the smooth bracket-generating lifted patch. -/
theorem compactStarredComparison {n k s m : ℕ}
    {w : Fin (k+1) → ℕ+} {Ω : Set (Fin n → ℝ)} {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData (k+1) s (n+m) w} (A : CoordinateApproximationData L M)
    (hn : 0 < n) (_hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s) :
    CompactStarredComparison A := by
  intro K hK hKU
  have hAU : A.U ⊆ (L.U : Set (Fin (n+m) → ℝ)) :=
    fun _ hξ => A.closure_subset_lift (subset_closure hξ)
  have hKL : K ⊆ (L.U : Set (Fin (n+m) → ℝ)) := hKU.trans hAU
  have hn' : 0 < n + m := by omega
  have hBase : Continuous (basePoint (n := n) (m := m)) := (P1.paddingBaseCLM n m).continuous
  -- original side: domain equality on the projected free patch
  have hsubO : basePoint '' (L.U : Set (Fin (n+m) → ℝ)) ⊆ Ω := by
    rintro x ⟨ξ, hξ, rfl⟩
    exact L.subset_domain hξ
  obtain ⟨ρ₁, hρ₁, _, heq₁⟩ := exists_compact_ball_domain_equalities (s := s)
    (isOpen_basePoint_image L.U.isOpen) (hK.image hBase) (Set.image_mono hKL) X
    (fun i => (hX i).mono hsubO) w
  -- lifted side: domain equality and auxiliary-to-ordinary comparison on `L.U`
  have hXl : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X L.P i) (L.U : Set (Fin (n+m) → ℝ)) :=
    fun i => (L.smooth i).mono L.subset_domain
  have hstep : bracketStepOn (L.U : Set (Fin (n+m) → ℝ)) w (triangularLift X L.P) s :=
    fun ξ hξ => (L.free_spanning ξ hξ).2
  obtain ⟨ρ₂, hρ₂, _, heq₂⟩ := exists_compact_ball_domain_equalities (s := s)
    L.U.isOpen hK hKL (triangularLift X L.P) hXl w
  obtain ⟨Al, εl, hAl, hεl, hincl⟩ := exists_compact_auxiliary_ordinary_ball_inclusion
    hn' hs w hw L.U.isOpen hK hKL (triangularLift X L.P) hXl hstep
  refine ⟨min (min ρ₁ ρ₂) εl, Al, lt_min (lt_min hρ₁ hρ₂) hεl, hAl, ?_⟩
  intro η hη r hr hrr
  have hr₁ : r ≤ ρ₁ := hrr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₂ : r ≤ ρ₂ := hrr.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrε : r ≤ εl := hrr.trans (min_le_right _ _)
  have hrCr : ENNReal.ofReal r ≤ ENNReal.ofReal (Al * r) :=
    ENNReal.ofReal_le_ofReal (by nlinarith)
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have hη' : basePoint η ∈ basePoint '' K := Set.mem_image_of_mem _ hη
    have hstar := (heq₁ Ω hsubO (basePoint η) hη' r hr hr₁).2
    have hlt : G4.auxiliaryDistance (s := s) Ω w X (basePoint η) y < ENNReal.ofReal r :=
      (G4.auxiliaryDistance_le Ω w X hw _ _).trans_lt hy.2
    have hlt' : y ∈ {y | G4.auxiliaryDistance (s := s) (basePoint '' (L.U : Set (Fin (n+m) → ℝ)))
        w X (basePoint η) y < ENNReal.ofReal r} := hstar ▸ hlt
    exact hlt'.trans_le hrCr
  · intro ξ hξ
    have hstar := (heq₂ (basePoint ⁻¹' Ω) L.subset_domain η hη r hr hr₂).2
    have hlt : G4.auxiliaryDistance (s := s) (basePoint ⁻¹' Ω) w (triangularLift X L.P) η ξ <
        ENNReal.ofReal r :=
      (G4.auxiliaryDistance_le (basePoint ⁻¹' Ω) w (triangularLift X L.P) hw _ _).trans_lt hξ.2
    have hlt' : ξ ∈ {ξ | G4.auxiliaryDistance (s := s) (L.U : Set (Fin (n+m) → ℝ)) w
        (triangularLift X L.P) η ξ < ENNReal.ofReal r} := hstar ▸ hlt
    exact hlt'.trans_le hrCr
  · intro ξ hξ
    have hd := hincl η hη r hr hrε hξ
    exact ⟨L.subset_domain (mem_of_controlDistance_lt_ofReal hd),
      (G1.controlDistance_mono_domain w (triangularLift X L.P) L.subset_domain η ξ).trans_lt hd⟩

end RothschildStein.L1.CoordinateApproximationData
