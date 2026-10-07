-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JoinedChartFiberBounds
public import RothschildStein.G4.WeightedBoxVolume
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.L1

/-- Joined-chart fiber bounds retain the exact separate
parameter radius factor 2^m ρ^(sum weights), including m=0. No fiber
inequality or parameterized inverse is supplied as a premise
(BB pp. 520–522, (10.49); unequal-radius rescaling). -/
theorem weighted_fiberVolume_bounds_of_joined_chart_data {n m : ℕ}
    {D : Set (Fin (n+m) → ℝ)} {U W : Set (Fin n → ℝ)} {V : Set (Fin m → ℝ)}
    (hD : IsOpen D) (hU : IsOpen U) (hW : IsOpen W) (hV : IsOpen V)
    (F : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ))
    (Ψ : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F D) (hfull : InjOn F D)
    (hmixed : ∀ u ∈ U, ∀ v ∈ V, joinPoint u v ∈ D)
    (hproj : ∀ u ∈ U, ∀ v ∈ V, basePoint (F (joinPoint u v)) = Ψ u v)
    (hinj : ∀ v ∈ V, InjOn (fun u => Ψ u v) U)
    (hcover : ∀ y ∈ W, ∀ v ∈ V, ∃ u ∈ U, Ψ u v = y)
    {a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hAlo : ∀ p ∈ D, a ≤ |(fderiv ℝ F p).det|)
    (hAhi : ∀ p ∈ D, |(fderiv ℝ F p).det| ≤ b)
    (hHlo : ∀ u ∈ U, ∀ v ∈ V, c ≤ |(fderiv ℝ (fun y => Ψ y v) u).det|)
    (hHhi : ∀ u ∈ U, ∀ v ∈ V, |(fderiv ℝ (fun y => Ψ y v) u).det| ≤ d)
    (wv : Fin m → ℕ+) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (hQV : G4.weightedBox wv (ρ*r) ⊆ V)
    {Small Large : Set (Fin (n+m) → ℝ)}
    (hsmall : Small ⊆ (fun p => F (joinPoint p.1 p.2)) '' (U ×ˢ G4.weightedBox wv (ρ*r)))
    (hlarge : (fun p => F (joinPoint p.1 p.2)) '' (U ×ˢ G4.weightedBox wv (ρ*r)) ⊆ Large) :
    ∀ y ∈ W, ENNReal.ofReal ((a/d) * (2^m * ρ^(∑ i, (wv i : ℕ))) * r^(∑ i, (wv i : ℕ))) ≤ fiberVolume Large y ∧
      fiberVolume Small y ≤ ENNReal.ofReal ((b/c) * (2^m * ρ^(∑ i, (wv i : ℕ))) * r^(∑ i, (wv i : ℕ))) := by
  have hb := fiberVolume_bounds_of_joined_chart_data hD hU hW hV F Ψ hF hfull hmixed
    hproj hinj hcover ha hc hAlo hAhi hHlo hHhi
    (G4.isOpen_weightedBox wv (ρ*r)).measurableSet hQV hsmall hlarge
  intro y hy
  have hh := hb y hy
  rw [G4.volume_weightedBox wv (mul_nonneg hρ hr)] at hh
  have hbox : 0 ≤ (2:ℝ)^m * (ρ*r)^(∑ i, (wv i : ℕ)) := by positivity
  have hlo : ENNReal.ofReal (a/d) *
      ENNReal.ofReal ((2:ℝ)^m * (ρ*r)^(∑ i, (wv i : ℕ))) =
      ENNReal.ofReal ((a/d) * (2^m * ρ^(∑ i, (wv i : ℕ))) * r^(∑ i, (wv i : ℕ))) := by
    rw [← ENNReal.ofReal_mul' hbox,mul_pow]
    congr 1
    ring
  have hhi : ENNReal.ofReal (b/c) *
      ENNReal.ofReal ((2:ℝ)^m * (ρ*r)^(∑ i, (wv i : ℕ))) =
      ENNReal.ofReal ((b/c) * (2^m * ρ^(∑ i, (wv i : ℕ))) * r^(∑ i, (wv i : ℕ))) := by
    rw [← ENNReal.ofReal_mul' hbox,mul_pow]
    congr 1
    ring
  exact ⟨hlo ▸ hh.1,hhi ▸ hh.2⟩

end RothschildStein.L1
