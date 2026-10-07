-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderFiniteSum
public import RothschildStein.H2.HolderLinear

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- A uniform horizontal second-jet estimate also controls
the drift jet by the equation, with the exact coefficient
q²+θ(1+q) (BB Theorem 8.50, pp. 379–380). -/
theorem second_jet_holder_norm_bound {X : Type*} [MetricSpace X] {q : ℕ}
    (a : ℝ≥0) (U : Set X) (F u0 : X → ℝ) (u : Fin q → Fin q → X → ℝ)
    (θ L : ℝ≥0∞) (hL : 1 ≤ L)
    (heq : F = fun x => u0 x + ∑ i : Fin q, u i i x)
    (hu : ∀ i j, H2.boundedHolderNorm a U (u i j) ≤ L * H2.boundedHolderNorm a U F) :
    (∑ i : Fin q, ∑ j : Fin q, H2.boundedHolderNorm a U (u i j)) +
      θ * H2.boundedHolderNorm a U u0 ≤
      ((q : ℝ≥0∞) ^ 2 + θ * (1 + (q : ℝ≥0∞))) * L * H2.boundedHolderNorm a U F := by
  classical
  let N := H2.boundedHolderNorm a U
  have hdiag : N (fun x => ∑ i : Fin q, u i i x) ≤ (q : ℝ≥0∞) * L * N F := by
    have hh := H2.boundedHolderNorm_sum_le Finset.univ a U (fun i : Fin q => u i i)
    apply hh.trans
    calc
      _ ≤ ∑ i : Fin q, L * N F := Finset.sum_le_sum fun i _ => hu i i
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hneg : N (fun x => -(∑ i : Fin q, u i i x)) = N (fun x => ∑ i : Fin q, u i i x) := by
    have hh := H2.boundedHolderNorm_smul (δ := a) (U := U) (-1) (fun x => ∑ i : Fin q, u i i x)
    have he : (-1 : ℝ) • (fun x => ∑ i : Fin q, u i i x) = (fun x => -(∑ i : Fin q, u i i x)) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul]
    rw [he] at hh
    simpa only [abs_neg, abs_one,
      ENNReal.ofReal_one, one_mul] using hh
  have hz : u0 = fun x => F x + -(∑ i : Fin q, u i i x) := by
    funext x
    rw [heq]
    ring
  have hzero : N u0 ≤ (1 + (q : ℝ≥0∞)) * L * N F := by
    rw [hz]
    apply H2.boundedHolderNorm_add_le.trans
    change N F + N (fun x => -(∑ i : Fin q, u i i x)) ≤ _
    rw [hneg]
    calc
      N F + N (fun x => ∑ i : Fin q, u i i x) ≤ N F + (q : ℝ≥0∞) * L * N F :=
        add_le_add le_rfl hdiag
      _ ≤ L * N F + (q : ℝ≥0∞) * L * N F :=
        add_le_add (by simpa only [one_mul] using mul_le_mul' hL (le_refl (N F))) le_rfl
      _ = _ := by ring
  have hmatrix : (∑ i : Fin q, ∑ j : Fin q, N (u i j)) ≤ (q : ℝ≥0∞)^2 * L * N F := by
    calc
      _ ≤ ∑ i : Fin q, ∑ j : Fin q, L * N F :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hu i j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  exact (add_le_add hmatrix (mul_le_mul' le_rfl hzero)).trans_eq (by ring)

end RothschildStein.H3
