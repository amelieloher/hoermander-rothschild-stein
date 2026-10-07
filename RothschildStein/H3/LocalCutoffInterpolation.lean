-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffFlowInterpolation
public import RothschildStein.H3.CutoffInnerNorm
public import RothschildStein.H3.CutoffSquareCoefficients
public import RothschildStein.H3.CutoffLpNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The local cutoff interpolation estimate follows from weak Leibniz and
global interpolation under the flow and density hypotheses. A and B are
the cutoff derivative bounds (BB (8.54), p. 371). -/
theorem local_cutoff_interpolation_of_flow_and_density {n m q : ℕ}
    (G : HomogeneousGroup n) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (ι : Fin q → Fin m) (hι : ∀ i, (w (ι i) : ℕ) = 1)
    (E : Fin q → ℝ → (Fin n → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => X (ι i)))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hdensity : ∀ u, memSobolevX w X ⊤ 2 p u →
      Nonempty (SobolevWordApproximation w X p u))
    (Ω U : Opens (Fin n → ℝ)) {u : (Fin n → ℝ) → ℝ}
    (hu : memSobolevX w X Ω 2 p u)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hplateau : EqOn φ 1 (U : Set (Fin n → ℝ)))
    (A B : ℝ≥0∞)
    (hφ : eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ 1)
    (hA : ∀ i, eLpNorm (fieldDerivative (X (ι i)) φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ A)
    (hB : ∀ i, eLpNorm (fieldDerivative (X (ι i)) (fieldDerivative (X (ι i)) φ)) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    (∑ i, weakWordENorm X U [ι i] p u) ≤
      ENNReal.ofReal (2*(q : ℝ)/ε)*eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) +
      ENNReal.ofReal (ε/2)*
        ((∑ i, weakWordENorm X Ω [ι i,ι i] p u) +
          2*A*(∑ i, weakWordENorm X Ω [ι i] p u) +
          (q : ℝ≥0∞)*B*eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ)))) := by
  classical
  have hglobal := cutoff_memSobolevX_global w X Ω (fun i => (hX i).contDiffOn) 2 p hp u hu φ
  have hfirst : (∑ i, weakWordENorm X U [ι i] p u) ≤
      ∑ i, weakWordENorm X ⊤ [ι i] p (fun x => u x * φ x) := by
    apply Finset.sum_le_sum
    intro i _
    have hi : [ι i] ∈ wordFamily w 2 := by
      simp [S.mem_wordFamily_iff, wordWeight, hι i]
    obtain ⟨g, hg, _⟩ := hglobal.2 [ι i] hi
    exact cutoff_plateau_weakNorm_le X U [ι i] p u φ g hplateau hg
  have hsquare : (∑ i, weakWordENorm X ⊤ [ι i,ι i] p (fun x => u x * φ x)) ≤
      (∑ i, weakWordENorm X Ω [ι i,ι i] p u) +
        2*A*(∑ i, weakWordENorm X Ω [ι i] p u) +
        (q : ℝ≥0∞)*B*eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
    have hb : ∀ i : Fin q,
        weakWordENorm X ⊤ [ι i,ι i] p (fun x => u x * φ x) ≤
        weakWordENorm X Ω [ι i,ι i] p u + 2*A*weakWordENorm X Ω [ι i] p u +
        B*eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
      intro i
      have hi : [ι i] ∈ wordFamily w 2 := by
        simp [S.mem_wordFamily_iff, wordWeight, hι i]
      have hii : [ι i,ι i] ∈ wordFamily w 2 := by
        simp [S.mem_wordFamily_iff, wordWeight, hι i]
      obtain ⟨g, hg, _⟩ := hu.2 [ι i] hi
      obtain ⟨h, hh, _⟩ := hu.2 [ι i,ι i] hii
      exact cutoff_square_global_le_of_bounds X Ω (fun j => (hX j).contDiffOn)
        (ι i) u g h φ hg hh p hp A B hφ (hA i) (hB i)
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc, mul_left_comm] using ht
  have hnorm := cutoff_eLpNorm_le Ω u φ p (lt_of_lt_of_le (by simp) hp) hφ
  have hi := cutoff_interpolation_of_flow_and_density G w X hX ι hι E hE hE0 hflow
    hp hpt hdensity Ω hu φ hε
  exact hfirst.trans (hi.trans (by gcongr))

end RothschildStein.H3
