-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactGlobalHolderIntrinsicJets
public import RothschildStein.H3.FixedSecondRepresentation
public import RothschildStein.H3.SecondJetPrincipalValueHolderBound
public import RothschildStein.H3.HolderBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators ENNReal NNReal
namespace RothschildStein.H3

private theorem boundedHolder_of_compact_global_bound {X : Type*} [MetricSpace X]
    (a : ℝ≥0) {F : X → ℝ} (hF : Continuous F) (hsF : HasCompactSupport F)
    {A : ℝ} (hh : ∀ x y, |F x - F y| ≤ A * dist x y ^ (a : ℝ)) :
    H2.BoundedHolder a univ F := by
  obtain ⟨M, hM⟩ := hsF.exists_bound_of_continuous hF
  have hsup : H2.holderSup univ F < ⊤ :=
    (H2.holderSup_le_of_bound (fun x _ => by simpa only [Real.norm_eq_abs] using hM x)).trans_lt
      ENNReal.ofReal_lt_top
  have hsemi : H2.holderSemi a univ F < ⊤ :=
    (H2.holderSemi_le_of_bound (abs_nonneg A) (fun x _ y _ =>
      (hh x y).trans (mul_le_mul_of_nonneg_right (le_abs_self A)
        (Real.rpow_nonneg dist_nonneg _)))).trans_lt ENNReal.ofReal_lt_top
  exact ENNReal.add_lt_top.mpr ⟨hsup, hsemi⟩

/-- A compact intrinsic input gives the horizontal-plus-drift estimate
under the global control-norm comparison and principal-value bounds.
Its coefficients are uniform in the input (BB Theorem 8.50, pp. 379–380). -/
theorem holder_estimate_of_principal_value_bounds {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields) (hν : C.norm = H.norm)
    (φ : G2.GroupMollifier G H.norm) (U : Opens (Fin N → ℝ))
    (a : ℝ≥0) (ha : 0 < (a : ℝ)) (θ L : ℝ) (hθ : 0 ≤ θ) (hL : 1 ≤ L)
    (B : Fin q → Fin q → ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hcoeff : ∀ i j, B i j + |fundamentalCorrectionCoefficients G H K hQ i j| ≤ L) :
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
    (∀ F : ControlCarrier N → ℝ, Continuous F → HasCompactSupport F → tsupport F ⊆ (U : Set (Fin N → ℝ)) →
      @H2.BoundedHolder (ControlCarrier N) metric a univ F → ∀ i j,
      @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ))
        (fun x => H1.principalValueConvolution G C.norm
          (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F x) ≤
        ENNReal.ofReal (B i j) * @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ)) F) →
    ∀ f : (Fin N → ℝ) → ℝ,
      memHolderXCompact driftWeight H.fields (controlDistance univ driftWeight H.fields) U 2 a f →
      ∃ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
        jet [] = (U : Set (Fin N → ℝ)).indicator f ∧
        (∀ I, wordWeight driftWeight I ≤ 2 →
          hasIntrinsicWordDeriv H.fields ⊤ I ((U : Set (Fin N → ℝ)).indicator f) (jet I) ∧
          Continuous (jet I) ∧ HasCompactSupport (jet I)) ∧
        let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
        (∑ i : Fin q, ∑ j : Fin q,
          @H2.boundedHolderNorm (ControlCarrier N) metric a univ (jet [i.succ, j.succ])) +
          ENNReal.ofReal θ * @H2.boundedHolderNorm (ControlCarrier N) metric a univ (jet [0]) ≤
          ((q : ℝ≥0∞)^2 + ENNReal.ofReal θ * (1 + (q : ℝ≥0∞))) * ENNReal.ofReal L *
            @H2.boundedHolderNorm (ControlCarrier N) metric a univ F := by
  classical
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
  intro hPV f hf
  obtain ⟨T, hTU, jet, hzero, hj⟩ := exists_global_holder_intrinsic_jets_of_memHolderXCompact_of_controlNorm
    G U driftWeight H.fields (H.fields_smooth G) C 2 ha hf
  have hi := fun I hI => (hj I hI).1
  have hc := fun I hI => (hj I hI).2.1
  have hs := fun I hI => (hj I hI).2.2.1
  have hw0 : wordWeight (driftWeight (q := q)) [0] ≤ 2 := by simp [wordWeight, driftWeight]
  have hw2 (i j : Fin q) : wordWeight (driftWeight (q := q)) [i.succ, j.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
  have hF : Continuous F := (hc [0] hw0).add (continuous_finsetSum _ (fun i _ => hc _ (hw2 i i)))
  have hsF : HasCompactSupport F := by
    have hh := (hs [0] hw0).add
      (HasCompactSupport.finset_sum (fun i (_ : i ∈ Finset.univ) => hs _ (hw2 i i)))
    have he : (jet [0] + ∑ i : Fin q, jet [i.succ, i.succ]) = F := by
      funext x
      simp only [F, Pi.add_apply, Finset.sum_apply]
    exact he ▸ hh
  have hsT : tsupport F ⊆ T := by
    apply closure_minimal _ T.isCompact.isClosed
    intro x hx
    by_contra hn
    have hz (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) : jet I x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hn ((hj I hI).2.2.2.1 h))
    have hzdiag (i : Fin q) : jet [i.succ, i.succ] x = 0 := hz _ (hw2 i i)
    exact hx (by simp only [F, hz [0] hw0, hzdiag, Finset.sum_const_zero, add_zero])
  obtain ⟨A0, hA0⟩ := (hj [0] hw0).2.2.2.2
  choose A hA using fun i : Fin q => (hj [i.succ, i.succ] (hw2 i i)).2.2.2.2
  have hsource : ∀ x y, |F x - F y| ≤ (A0 + ∑ i : Fin q, A i) * G2.gaugeDistance G C.norm x y ^ (a : ℝ) := by
    intro x y
    calc
      _ = |(jet [0] x - jet [0] y) + ∑ i : Fin q, (jet [i.succ, i.succ] x - jet [i.succ, i.succ] y)| := by
        dsimp only [F]
        rw [Finset.sum_sub_distrib]
        congr 1
        ring
      _ ≤ |jet [0] x - jet [0] y| + ∑ i : Fin q, |jet [i.succ, i.succ] x - jet [i.succ, i.succ] y| :=
        (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
      _ ≤ A0 * G2.gaugeDistance G C.norm x y ^ (a : ℝ) +
          ∑ i : Fin q, A i * G2.gaugeDistance G C.norm x y ^ (a : ℝ) :=
        add_le_add (hA0 x y) (Finset.sum_le_sum fun i _ => hA i x y)
      _ = _ := by rw [← Finset.sum_mul, add_mul]
  have hbounded : @H2.BoundedHolder (ControlCarrier N) metric a univ F :=
    @boundedHolder_of_compact_global_bound (ControlCarrier N) metric a F hF hsF
      (A0 + ∑ i : Fin q, A i) hsource
  have hrep := second_representation_with_fixed_coefficients G H K hQ (hν ▸ C.symmetric) φ
    ((U : Set (Fin N → ℝ)).indicator f) jet hzero hi hc hs ha (by simpa only [← hν] using hsource)
  have hlocal := second_jet_holder_bound_of_principal_value_estimates G C.norm C.constant_one C.symmetric
    a (U : Set (Fin N → ℝ)) F (jet [0]) (fun i j : Fin q => jet [i.succ, j.succ])
    (fun i j => fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
    (fundamentalCorrectionCoefficients G H K hQ) B θ L hθ hL hB hcoeff rfl
    (by simpa only [← hν] using hrep) (hPV F hF hsF (hsT.trans hTU) hbounded)
  have hnorm (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) :
      @H2.boundedHolderNorm (ControlCarrier N) metric a univ (jet I) =
      @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ)) (jet I) :=
    boundedHolderNorm_global_eq_of_controlNorm C U.isOpen (hs I hI) ((hj I hI).2.2.2.1.trans hTU)
  have hnorm2 (i j : Fin q) := hnorm [i.succ, j.succ] (hw2 i j)
  refine ⟨jet, hzero, fun I hI => ⟨hi I hI, hc I hI, hs I hI⟩, ?_⟩
  simp only [hnorm [0] hw0, hnorm2]
  exact hlocal.trans (mul_le_mul' le_rfl (@H2.boundedHolderNorm_restrict (ControlCarrier N) metric a (U : Set (Fin N → ℝ)) univ F (subset_univ _)))

end RothschildStein.H3
