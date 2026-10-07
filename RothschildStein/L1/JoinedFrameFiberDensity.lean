-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJoinedFiberBounds
public import RothschildStein.L1.FiberDensityRatio
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.L1

/-- Actual joined/shifted chart data and the completed-frame
measure-ratio estimate give both density bounds. The
separate parameter radius and full lifted/original determinant quotient
are retained. There is no supplied fiber inequality or inverse regularity
(BB pp. 520–522, (10.49), corrected lower determinant ratio). -/
theorem fiber_density_bounds_of_joined_weighted_frame_chart {n m : ℕ}
    {D : Set (Fin (n+m) → ℝ)} {U W : Set (Fin n → ℝ)} {V : Set (Fin m → ℝ)}
    (hD : IsOpen D) (hU : IsOpen U) (hW : IsOpen W) (hV : IsOpen V)
    (F : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ))
    (Ψ : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F D) (hfull : InjOn F D)
    (hmixed : ∀ u ∈ U, ∀ v ∈ V, joinPoint u v ∈ D)
    (hproj : ∀ u ∈ U, ∀ v ∈ V, basePoint (F (joinPoint u v)) = Ψ u v)
    (hinj : ∀ v ∈ V, InjOn (fun u => Ψ u v) U)
    (hcover : ∀ y ∈ W, ∀ v ∈ V, ∃ u ∈ U, Ψ u v = y)
    {a b c d dlift dbase cv Cv : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hd : 0 < d) (hdlift : 0 ≤ dlift) (hdbase : 0 < dbase)
    (hcv : 0 < cv) (hCv : 0 < Cv)
    (hAlo : ∀ p ∈ D, a*dlift ≤ |(fderiv ℝ F p).det|)
    (hAhi : ∀ p ∈ D, |(fderiv ℝ F p).det| ≤ b*dlift)
    (hHlo : ∀ u ∈ U, ∀ v ∈ V, c*dbase ≤ |(fderiv ℝ (fun y => Ψ y v) u).det|)
    (hHhi : ∀ u ∈ U, ∀ v ∈ V, |(fderiv ℝ (fun y => Ψ y v) u).det| ≤ d*dbase)
    (wv : Fin m → ℕ+) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (hQV : G4.weightedBox wv (ρ*r) ⊆ V)
    {Small Large : Set (Fin (n+m) → ℝ)}
    (hsmall : Small ⊆ (fun p => F (joinPoint p.1 p.2)) '' (U ×ˢ G4.weightedBox wv (ρ*r)))
    (hlarge : (fun p => F (joinPoint p.1 p.2)) '' (U ×ˢ G4.weightedBox wv (ρ*r)) ⊆ Large)
    (A : Set (Fin n → ℝ)) (B : Set (Fin (n+m) → ℝ))
    (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤) (hpos : 0 < (volume A).toReal)
    (hratio : ENNReal.ofReal cv * ENNReal.ofReal ((dlift/dbase)*r^(∑ i, (wv i : ℕ))) ≤
        volume B / volume A ∧
      volume B / volume A ≤ ENNReal.ofReal Cv *
        ENNReal.ofReal ((dlift/dbase)*r^(∑ i, (wv i : ℕ)))) :
    ∀ y ∈ W,
      ENNReal.ofReal ((((a/d)*(2^m*ρ^(∑ i, (wv i : ℕ))))/Cv) *
        (volume B).toReal / (volume A).toReal) ≤ fiberVolume Large y ∧
      fiberVolume Small y ≤
        ENNReal.ofReal ((((b/c)*(2^m*ρ^(∑ i, (wv i : ℕ))))/cv) *
          (volume B).toReal / (volume A).toReal) := by
  have hraw := weighted_fiberVolume_bounds_of_joined_chart_data hD hU hW hV F Ψ hF hfull
    hmixed hproj hinj hcover (mul_nonneg ha hdlift) (mul_pos hc hdbase)
    hAlo hAhi hHlo hHhi wv hρ hr hQV hsmall hlarge
  have hlo : (a*dlift/(d*dbase))*(2^m*ρ^(∑ i, (wv i : ℕ)))*r^(∑ i, (wv i : ℕ)) =
      ((a/d)*(2^m*ρ^(∑ i, (wv i : ℕ))))*((dlift/dbase)*r^(∑ i, (wv i : ℕ))) := by
    rw [← div_mul_div_comm]
    ring
  have hhi : (b*dlift/(c*dbase))*(2^m*ρ^(∑ i, (wv i : ℕ)))*r^(∑ i, (wv i : ℕ)) =
      ((b/c)*(2^m*ρ^(∑ i, (wv i : ℕ))))*((dlift/dbase)*r^(∑ i, (wv i : ℕ))) := by
    rw [← div_mul_div_comm]
    ring
  intro y hy
  have hh := hraw y hy
  rw [hlo,hhi] at hh
  exact fiber_density_bounds_of_frame_measure_ratio A B Small Large hA hB hpos
    (by positivity) (by positivity) hcv hCv hratio y hh.1 hh.2

end RothschildStein.L1
