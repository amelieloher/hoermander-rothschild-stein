-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderCutoffProduct
public import RothschildStein.H1.Standing
public import RothschildStein.H3.FrozenHolderMetricNorm
public import RothschildStein.S.WordLeibniz
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- Ordered cutoff Leibniz jets have finite global fixed
Hölder norms when the local input jets and the smooth cutoff word jets
have finite norms. Every ordered split, including multiplicities, is kept. -/
theorem leibniz_word_holder_finite_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (U : Opens (Fin N → ℝ)) (a : ℝ≥0) (I : List (Fin (q + 1)))
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (φ : TestFunction U ℝ (⊤ : ℕ∞))
    (hjet : ∀ J, J.Sublist I → holderENorm (controlDistance univ driftWeight H.fields)
      a (U : Set (Fin N → ℝ)) (jet J) < ⊤)
    (hφ : ∀ J, J.Sublist I → holderENorm (controlDistance univ driftWeight H.fields)
      a univ (wordDerivative H.fields J φ) < ⊤) :
    holderENorm (controlDistance univ driftWeight H.fields) a univ
      (S.leibnizWordValue H.fields I jet φ) < ⊤ := by
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  rw [frozen_holderENorm_eq_control_norm G driftWeight H.fields C]
  have hterm (p : List (Fin (q + 1)) × List (Fin (q + 1)))
      (hp : p ∈ S.leibnizSplits I) :
      @H2.BoundedHolder (ControlCarrier N) metric a univ
        (fun x => jet p.1 x * wordDerivative H.fields p.2 φ x) := by
    have hsub := S.leibnizSplits_sublist I p hp
    have hf : @H2.BoundedHolder (ControlCarrier N) metric a
        (U : Set (Fin N → ℝ)) (jet p.1) := by
      have hh := hjet p.1 hsub.1
      rwa [frozen_holderENorm_eq_control_norm G driftWeight H.fields C] at hh
    have hg : @H2.BoundedHolder (ControlCarrier N) metric a univ
        (wordDerivative H.fields p.2 φ) := by
      have hh := hφ p.2 hsub.2
      rwa [frozen_holderENorm_eq_control_norm G driftWeight H.fields C] at hh
    have hs := S.tsupport_wordDerivative_subset H.fields p.2 φ
    have hc := φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hs
    have hb := boundedHolderNorm_cutoff_product_of_controlNorm C U.isOpen hc
      (hs.trans φ.tsupport_subset) hg hf
    have he : (fun x => wordDerivative H.fields p.2 φ x * jet p.1 x) =
        (fun x => jet p.1 x * wordDerivative H.fields p.2 φ x) := by
      funext x
      exact mul_comm _ _
    have heN := congrArg (fun f : (Fin N → ℝ) → ℝ =>
      @H2.boundedHolderNorm (ControlCarrier N) metric a univ f) he
    exact heN.symm.trans_lt (hb.trans_lt (ENNReal.mul_lt_top hg hf))
  have hsum (L : List (List (Fin (q + 1)) × List (Fin (q + 1))))
      (hL : ∀ p ∈ L, @H2.BoundedHolder (ControlCarrier N) metric a univ
        (fun x => jet p.1 x * wordDerivative H.fields p.2 φ x)) :
      @H2.BoundedHolder (ControlCarrier N) metric a univ
        (fun x => (L.map (fun p => jet p.1 x * wordDerivative H.fields p.2 φ x)).sum) := by
    induction L with
    | nil => simp [H2.BoundedHolder, H2.boundedHolderNorm, H2.holderSup, H2.holderSemi]
    | cons p L ih =>
      have hp := hL p List.mem_cons_self
      have hi := ih (fun r hr => hL r (List.mem_cons_of_mem p hr))
      simp only [List.map_cons, List.sum_cons]
      exact (H2.boundedHolderNorm_add_le).trans_lt (ENNReal.add_lt_top.mpr ⟨hp, hi⟩)
  exact hsum (S.leibnizSplits I) hterm

end RothschildStein.H3
