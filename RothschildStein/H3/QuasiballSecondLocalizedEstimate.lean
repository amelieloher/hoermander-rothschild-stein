-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactFullHolderEstimate
public import RothschildStein.H3.QuasiballControlBuffer
public import RothschildStein.H3.QuasiballCompactHolderInput
public import RothschildStein.H3.QuasiballHolderPlateau
public import RothschildStein.H3.CutoffProductNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The full local weight-two norm is controlled by the actual
ordered cutoff source and the local supremum, uniformly in the center
and both radii under one fixed upper radius. -/
theorem quasiball_second_localized_estimate_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (μ : G2.GroupMollifier G H.norm) (φ₀ : G2.GroupMollifier G C.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1)
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : Fin N → ℝ, ∀ t s : ℝ,
      0 < t → t < s → s / 2 ≤ t → s ≤ Rmax →
      ∀ u : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G ν z s) 2 a u →
      ∃ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
        jet [] = u ∧
        (∀ I, wordWeight driftWeight I ≤ 2 →
          hasWeakWordDeriv H.fields (quasiballDomain G ν z s) I u (jet I) ∧
          holderENorm (controlDistance univ driftWeight H.fields) a
            (quasiballDomain G ν z s : Set (Fin N → ℝ)) (jet I) < ⊤) ∧
        holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
          (quasiballDomain G ν z t) 2 a u ≤
          ENNReal.ofReal A *
            (holderENorm (controlDistance univ driftWeight H.fields) a univ
              (fun x => S.leibnizWordValue H.fields [0] jet (smoothQuasiballCutoff G ν z t s) x +
                ∑ i : Fin q, S.leibnizWordValue H.fields [i.succ, i.succ] jet
                  (smoothQuasiballCutoff G ν z t s) x) +
              eLpNorm u ⊤ (volume.restrict (G2.gaugeBall G ν z s))) := by
  obtain ⟨ρ, hρ, hbuffer⟩ := exists_uniform_gauge_ball_buffer G ν C.norm hRmax
  obtain ⟨A, hA, hb⟩ := compact_full_holder_estimate_of_controlNorm G H K hQ C μ φ₀ ν hν ha ha1 hρ
  refine ⟨A, hA, ?_⟩
  intro z t s ht hts hhalf hs u hu
  let U := quasiballDomain G ν z s
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  let φ : TestFunction U ℝ (⊤ : ℕ∞) :=
    ⟨smoothQuasiballCutoff G ν z t s,
      smoothQuasiballCutoff_contDiff G ν hν z ht hts,
      smoothQuasiballCutoff_compact G ν z hts,
      (smoothQuasiballCutoff_tsupport G ν z hts).trans (intermediate_quasiball_subset G ν z hts)⟩
  obtain ⟨jet, hz, hj, hJ0, hJ⟩ := exists_frozen_cutoff_intrinsic_jets ⊤ U D
    (subset_univ _) driftWeight H.fields (H.fields_smooth G) 2 ha hu φ
  let J := fun I => S.leibnizWordValue H.fields I jet φ
  have hc := quasiball_cutoff_compact_holder_input_of_controlNorm G H C ν hν z ht hts hhalf 2 ha ha1.le u hu
  have hsupport : tsupport (fun x => u x * φ x) ⊆ (U : Set (Fin N → ℝ)) :=
    tsupport_mul_subset_right.trans φ.tsupport_subset
  have hh := hb z U (hbuffer z s hs) (fun x => u x * φ x) hc hsupport J hJ0
    (fun I hI => ⟨(hJ I hI).1, (hJ I hI).2.1, (hJ I hI).2.2.1,
      ((hJ I hI).2.2.2.trans φ.tsupport_subset)⟩)
  have hnφ : eLpNorm φ ⊤ (volume.restrict (U : Set (Fin N → ℝ))) ≤ 1 := by
    rw [eLpNorm_exponent_top φ.contDiff.continuous.aestronglyMeasurable]
    have he : eLpNormEssSup φ (volume.restrict (U : Set (Fin N → ℝ))) ≤ ENNReal.ofReal 1 := by
      apply eLpNormEssSup_le_of_ae_bound
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        change |smoothQuasiballCutoff G ν z t s x| ≤ 1
        rw [abs_of_nonneg (smoothQuasiballCutoff_range G ν z x t s).1]
        exact (smoothQuasiballCutoff_range G ν z x t s).2
    simpa using he
  have hsup := cutoff_product_global_norm_le U ⊤ (by simp) u φ hnφ
  refine ⟨jet, hz, hj, ?_⟩
  exact (quasiball_cutoff_full_holder_norm_le G ν z hts driftWeight H.fields
    (controlDistance univ driftWeight H.fields) 2 a u).trans
    (hh.trans (mul_le_mul' le_rfl (add_le_add le_rfl hsup)))

end RothschildStein.H3
