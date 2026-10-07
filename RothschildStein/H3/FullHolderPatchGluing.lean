-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.driftWeight
public import RothschildStein.H3.HolderPatchGluing
public import RothschildStein.H3.FrozenHolderMetricNorm
public import RothschildStein.H3.IntrinsicWordRestriction
public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- A positive pair radius glues complete fixed Holder norms.
The same intrinsic word representative is used on every patch; the
finite word count is absorbed into the input-independent constant. -/
theorem full_holder_norm_patch_gluing_of_controlNorm {N q : ℕ} {ι : Type*}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (U E : Opens (Fin N → ℝ)) (hEU : (E : Set (Fin N → ℝ)) ⊆ U)
    (P : ι → Opens (Fin N → ℝ)) (hPU : ∀ i, (P i : Set (Fin N → ℝ)) ⊆ U)
    (k : ℕ) (a : ℝ≥0) {M ell : ℝ} (hM : 0 ≤ M) (hell : 0 < ell)
    (hcover : ∀ x ∈ (E : Set (Fin N → ℝ)), ∃ i, x ∈ P i)
    (hpairs : ∀ x ∈ (E : Set (Fin N → ℝ)), ∀ y ∈ (E : Set (Fin N → ℝ)),
      (controlDistance univ driftWeight H.fields x y).toReal < ell →
      ∃ i, x ∈ P i ∧ y ∈ P i)
    (u : (Fin N → ℝ) → ℝ)
    (hu : memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U k a u)
    (hn : ∀ i, holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
      (P i) k a u ≤ ENNReal.ofReal M) :
    holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields) E k a u ≤
      ENNReal.ofReal ((wordFamily (driftWeight (q := q)) k).card * ((1 + 2 / ell ^ (a : ℝ)) + 1) * M) := by
  classical
  let metric := gaugeMetric G C.norm C.constant_one C.symmetric
  let c := (1 + 2 / ell ^ (a : ℝ)) + 1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hword (I : List (Fin (q + 1))) (hI : I ∈ wordFamily driftWeight k) :
      intrinsicWordENorm H.fields (controlDistance univ driftWeight H.fields) E I a u ≤
        ENNReal.ofReal (c * M) := by
    obtain ⟨g, hg, _hgn⟩ := hu.2 I hI
    have hgp (i : ι) : hasIntrinsicWordDeriv H.fields (P i) I u g :=
      intrinsic_word_restrict H.fields U (P i) (hPU i) I hg
    have hgE := intrinsic_word_restrict H.fields U E hEU I hg
    have hgn (i : ι) : @H2.boundedHolderNorm (ControlCarrier N) metric a
        (P i : Set (Fin N → ℝ)) g ≤ ENNReal.ofReal M := by
      rw [← frozen_holderENorm_eq_control_norm G driftWeight H.fields C,
        ← RothschildStein.S.intrinsicWordENorm_eq_representative (P i) H.fields
          (controlDistance univ driftWeight H.fields) I a u g (hgp i)]
      exact (Finset.single_le_sum (f := fun J => intrinsicWordENorm H.fields
        (controlDistance univ driftWeight H.fields) (P i) J a u)
        (fun _ _ => zero_le) hI).trans (hn i)
    have hp : ∀ x ∈ (E : Set (Fin N → ℝ)), ∀ y ∈ (E : Set (Fin N → ℝ)),
        @dist (ControlCarrier N) metric.toDist x y < ell →
        ∃ i, x ∈ P i ∧ y ∈ P i := by
      intro x hx y hy hxy
      apply hpairs x hx y hy
      rw [G2.controlDistance_toReal_of_controlNorm G C]
      exact hxy
    have hb := @holder_patch_gluing (ControlCarrier N) ι metric
      (E : Set (Fin N → ℝ)) (fun i => (P i : Set (Fin N → ℝ))) g a M ell
      hM hell hcover hp hgn
    rw [RothschildStein.S.intrinsicWordENorm_eq_representative E H.fields
      (controlDistance univ driftWeight H.fields) I a u g hgE,
      frozen_holderENorm_eq_control_norm G driftWeight H.fields C]
    exact hb.trans_eq (by congr 1; dsimp [c]; ring)
  unfold holderXENorm
  apply (Finset.sum_le_sum fun I hI => hword I hI).trans_eq
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  dsimp [c]
  ring

end RothschildStein.H3
