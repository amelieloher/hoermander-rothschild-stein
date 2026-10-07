-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExpandingCutoffWeakWords
public import RothschildStein.Definitions.sobolevXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal BigOperators
namespace RothschildStein.H3

/-- Concentric expanding cutoffs approximate the full weighted Sobolev
norm, for every finite order and finite real exponent at least one. -/
theorem tendsto_expandingCutoff_sobolevXENorm_with_representatives {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (k : ℕ) (u : (Fin N → ℝ) → ℝ)
    (F : List (Fin (q+1)) → (Fin N → ℝ) → ℝ)
    (hF0 : F [] = u) {p : ℝ} (hp : 1 ≤ p)
    (hF : ∀ I ∈ wordFamily driftWeight k,
      hasWeakWordDeriv H.fields ⊤ I u (F I))
    (hFLp : ∀ I ∈ wordFamily driftWeight k, MemLp (F I) (ENNReal.ofReal p) volume) :
    Tendsto (fun R : ℝ => sobolevXENorm driftWeight H.fields ⊤ k (ENNReal.ofReal p)
      (fun x => u x - u x * smoothQuasiballCutoff G ν 0 R (2*R) x)) atTop (𝓝 0) := by
  classical
  have hw (I : List (Fin (q+1))) (hI : I ∈ wordFamily driftWeight k) :
      Tendsto (fun R : ℝ => weakWordENorm H.fields ⊤ I (ENNReal.ofReal p)
        (fun x => u x - u x * smoothQuasiballCutoff G ν 0 R (2*R) x)) atTop (𝓝 0) := by
    have ht := tendsto_expandingCutoff_weakWord_eLpNorm G H ν hν I u F hF0
      (fun J hJ => hF J (S.sublist_mem_wordFamily driftWeight k hJ hI)) hp
      (fun J hJ => hFLp J (S.sublist_mem_wordFamily driftWeight k hJ hI))
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hm := S.hasWeakWordDeriv_mul_word H.fields ⊤
      (fun i => (H.fields_smooth G i).contDiffOn) I u
      (smoothQuasiballCutoff G ν 0 R (2*R))
      (smoothQuasiballCutoff_contDiff G ν hν 0 hR (by linarith)).contDiffOn F hF0
      (fun J hJ => hF J (S.sublist_mem_wordFamily driftWeight k hJ hI))
    have hd := S.hasWeakWordDeriv_sub H.fields ⊤
      (fun i => (H.fields_smooth G i).contDiffOn) (hF I hI) hm
    rw [S.weakWordENorm_eq H.fields ⊤ I (ENNReal.ofReal p) _ _ hd]
    simp only [Opens.coe_top, Measure.restrict_univ]
    have he : (fun x => F I x - S.leibnizWordValue H.fields I F
        (smoothQuasiballCutoff G ν 0 R (2*R)) x) =
        -(fun x => S.leibnizWordValue H.fields I F
          (smoothQuasiballCutoff G ν 0 R (2*R)) x - F I x) := by
      funext x
      simp only [Pi.neg_apply]
      ring
    rw [he, eLpNorm_neg]
  unfold sobolevXENorm
  have hs := tendsto_finsetSum (wordFamily driftWeight k) hw
  simpa only [Finset.sum_const_zero] using hs

/-- The global Sobolev predicate itself supplies all representatives
needed for convergence under expanding cutoff multiplication. -/
theorem tendsto_expandingCutoff_sobolevXENorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (k : ℕ) {p : ℝ} (hp : 1 ≤ p) {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevX driftWeight H.fields ⊤ k (ENNReal.ofReal p) u) :
    Tendsto (fun R : ℝ => sobolevXENorm driftWeight H.fields ⊤ k (ENNReal.ofReal p)
      (fun x => u x - u x * smoothQuasiballCutoff G ν 0 R (2*R) x)) atTop (𝓝 0) := by
  classical
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  let P := fun I => ∃ g : (Fin N → ℝ) → ℝ,
    hasWeakWordDeriv H.fields ⊤ I u g ∧ MemLp g (ENNReal.ofReal p) volume
  let F : List (Fin (q+1)) → (Fin N → ℝ) → ℝ := fun I =>
    if I = [] then u else if h : P I then Classical.choose h else fun _ => 0
  have hF0 : F [] = u := by simp [F]
  have hFI : ∀ I ∈ wordFamily driftWeight k,
      hasWeakWordDeriv H.fields ⊤ I u (F I) ∧ MemLp (F I) (ENNReal.ofReal p) volume := by
    intro I hI
    by_cases he : I = []
    · subst I
      rw [hF0]
      have hup : MemLp u (ENNReal.ofReal p) volume := by
        simpa only [Opens.coe_top, Measure.restrict_univ] using hu.1
      exact ⟨S.hasWeakWordDeriv_nil H.fields ⊤
        (locallyIntegrableOn_of_locallyIntegrable_restrict (by
          simpa only [Opens.coe_top, Measure.restrict_univ] using hup.locallyIntegrable hp')), hup⟩
    · have hi : P I := by
        simpa only [P, Opens.coe_top, Measure.restrict_univ] using hu.2 I hI
      simp only [F, ite_eq_right he, dite_eq_left hi]
      exact Classical.choose_spec hi
  exact tendsto_expandingCutoff_sobolevXENorm_with_representatives G H ν hν k u F hF0 hp
    (fun I hI => (hFI I hI).1) (fun I hI => (hFI I hI).2)

end RothschildStein.H3
