-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Geometry.NumericalDistanceDomainEquality
public import RothschildStein.G4.ParameterLocalBuffer
public import RothschildStein.G4.NumericalUniformDistanceComparisons
public import RothschildStein.G4.MappedShortFieldBudget

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.Geometry

/-- The numerical distance comparison gives a neighborhood of each
center uniformly over a compact external family. Rank is used only in V;
first exit preserves the ambient path domain Ω (BB Theorem 9.6, p. 403,
and Theorem 9.56, pp. 459–460). -/
theorem exists_parameter_local_distance_comparison
    {P : Type*} [UniformSpace P] [CompactSpace P]
    {k n s : ℕ} (hn : 0 < n) (hs : 1 ≤ s)
    (w : Fin (k+1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω V : Set (Fin n → ℝ)} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    (X : P → Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ i, ContDiffOn ℝ (⊤ : ℕ∞) (X σ i) Ω)
    (hstep : ∀ σ, bracketStepOn V w (X σ) s)
    (hjoint : ∀ i j, ContinuousOn
      (fun z : P × (Fin n → ℝ) => iteratedFDeriv ℝ j (X z.1 i) z.2) (univ ×ˢ Ω))
    {z : Fin n → ℝ} (hz : z ∈ V) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ z ∈ U ∧
      ∃ C_eq ε : ℝ, 0 < C_eq ∧ 0 < ε ∧
      ∀ σ, ∀ x ∈ U, ∀ y,
      G4.auxiliaryDistance (s := s) Ω w (X σ) x y < ENNReal.ofReal ε →
        G4.auxiliaryDistance (s := s) Ω w (X σ) x y ≤ controlDistance Ω w (X σ) x y ∧
        controlDistance Ω w (X σ) x y ≤ ENNReal.ofReal C_eq * G4.auxiliaryDistance (s := s) Ω w (X σ) x y := by
  classical
  let L := n*s+s
  let q := L-1
  have horder : q+1 = n*s+s := by dsimp [q,L]; omega
  have hq : q+1 ≤ L := by dsimp [L]; omega
  let H := max (max (2*(n*s)+2*s) (max ((q+1)*s) (L+1+s)))
    (max (4*(s+1)^3) (1+s))
  have hH : s+1 ≤ H := by dsimp [H]; omega
  have hXV := fun σ i => (hX σ i).mono hVΩ
  obtain ⟨R, Δ, M, hR, hΔ, hM, hballV, hjets, hrank⟩ :=
    G4.exists_parameter_local_buffer hV w X hXV hstep H hH
      (fun i j _ => (hjoint i j).mono (Set.prod_mono Subset.rfl hVΩ)) hz
  obtain ⟨C_eq, _C_box, ε, hC_eq, _hC_box, hε, hcomp⟩ :=
    G4.exists_numerical_uniform_distance_comparisons k n s L q hn (by omega) horder hq
      w hw M Δ (R/2) hM.le hΔ (half_pos hR)
  let m := Fintype.card (G4.ShortWord w s)
  let wf : Fin m → ℕ+ := fun j => G4.shortWeight w (G4.shortIndex w j)
  let Z := fun σ (j : Fin m) => G4.shortField w (X σ) (G4.shortIndex w j)
  let B := G4.wordJetBase n 0 s M ^ s
  have hbound : ∀ σ i y, y ∈ closedBall z R → ‖Z σ i y‖ ≤ B := by
    intro σ i y hy
    have hb := G4.mappedShortField_jet_bound hV hballV w (X σ) (hXV σ)
      (id : G4.ShortWord w s → G4.ShortWord w s) hM.le
      (fun j => (hjets σ j).mono (by omega : 0+s ≤ H)) (G4.shortIndex w i) 0 (by omega) y hy
    simpa only [norm_iteratedFDerivWithin_zero, id_eq, Z, B] using hb
  obtain ⟨η, hη, heq⟩ := exists_numerical_controlDistance_domain_equality (m := m) R B hR
  refine ⟨ball z (R/2), isOpen_ball, mem_ball_self (half_pos hR),
    C_eq, min ε η, hC_eq, lt_min hε hη, ?_⟩
  intro σ x hx y hd
  have hxclosed := ball_subset_closedBall hx
  have hinner : closedBall x (R/2) ⊆ closedBall z R := by
    intro a ha
    have hax := mem_closedBall.mp ha
    have hxz := mem_closedBall.mp hxclosed
    have ht := dist_triangle a x z
    exact mem_closedBall.mpr (by linarith)
  have hdist : G4.auxiliaryDistance (s := s) Ω w (X σ) x y =
      G4.auxiliaryDistance (s := s) V w (X σ) x y :=
    heq Ω V wf (Z σ) z hVΩ hballV (hbound σ) x hxclosed y
      (hd.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  have hdV : G4.auxiliaryDistance (s := s) V w (X σ) x y < ENNReal.ofReal ε := by
    rw [← hdist]
    exact hd.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hc := hcomp V hV (X σ) (hXV σ) (hstep σ) x (hinner.trans hballV)
    (fun j a ha b hb => hjets σ j a ha b (hinner hb))
    (fun b hb => hrank σ b (hinner hb)) y hdV
  refine ⟨G4.auxiliaryDistance_le Ω w (X σ) hw x y, ?_⟩
  have hu := hc.2.1
  rw [← hdist] at hu
  exact (G1.controlDistance_mono_domain w (X σ) hVΩ x y).trans hu

end RothschildStein.Geometry
