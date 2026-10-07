-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothPotentialJetNorm
public import RothschildStein.H3.HolderCauchyProductLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- The smooth-source estimate (⋆) at a fixed exponent implies that the
corresponding approximating jets form a Cauchy family. -/
theorem smooth_potential_jet_cauchy_of_smooth_source_estimate {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (U : Opens (Fin N → ℝ)) (B : Set (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (k : ℕ) (β C : ℝ)
    (hestimate : ∀ φ : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ B →
      holderXENorm driftWeight H.fields d U k β (G2.groupConvolution G φ K) ≤
        ENNReal.ofReal C * holderENorm d β univ φ)
    (F : ℕ → (Fin N → ℝ) → ℝ)
    (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n) ∧ HasCompactSupport (F n) ∧ tsupport (F n) ⊆ B)
    (hdiff : Tendsto (fun p : ℕ × ℕ => holderENorm d β univ (F p.1 - F p.2))
      (atTop ×ˢ atTop) (𝓝 0))
    (I : List (Fin (q + 1))) (hI : wordWeight (driftWeight (q := q)) I ≤ k) :
    S.holderCauchySeq d β (U : Set (Fin N → ℝ))
      (fun n => wordDerivative H.fields I (G2.groupConvolution G (F n) K)) := by
  classical
  have hbound (n m : ℕ) : holderENorm d β (U : Set (Fin N → ℝ))
      (fun x => wordDerivative H.fields I (G2.groupConvolution G (F n) K) x -
        wordDerivative H.fields I (G2.groupConvolution G (F m) K) x) ≤
      ENNReal.ofReal C * holderENorm d β univ (F n - F m) := by
    have hs : tsupport (F n - F m) ⊆ tsupport (F n) ∪ tsupport (F m) := by
      apply closure_minimal _ ((isClosed_tsupport (F n)).union (isClosed_tsupport (F m)))
      intro x hx
      by_contra hn
      have hn' := not_or.mp hn
      have hzero : (F n - F m) x = 0 := by
        simp only [Pi.sub_apply, image_eq_zero_of_notMem_tsupport hn'.1,
          image_eq_zero_of_notMem_tsupport hn'.2, sub_self]
      exact hx hzero
    have hsB := hs.trans (union_subset (hF n).2.2 (hF m).2.2)
    have he := fundamental_convolution_word_sub G H K hQ I (F n) (F m)
      (hF n).1 (hF n).2.1 (hF m).1 (hF m).2.1
    change holderENorm d β (U : Set (Fin N → ℝ))
      (wordDerivative H.fields I (G2.groupConvolution G (F n) K) -
        wordDerivative H.fields I (G2.groupConvolution G (F m) K)) ≤ _
    rw [he]
    exact (smooth_fundamental_potential_jet_norm_le G H K hQ (F n - F m)
      ((hF n).1.sub (hF m).1) ((hF n).2.1.sub (hF m).2.1) U d k β I hI).trans
      (hestimate _ ((hF n).1.sub (hF m).1) ((hF n).2.1.sub (hF m).2.1) hsB)
  have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hdiff (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hlim
  apply holderCauchySeq_of_product_limit
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun p => hbound p.1 p.2)

end RothschildStein.H3
