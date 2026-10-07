-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderLocalUniformEstimate
public import RothschildStein.H3.IntrinsicFirstFrozenEstimate
public import RothschildStein.H3.SecondHolderNormFormula
public import RothschildStein.H3.LocalHolderSupNorm
public import RothschildStein.H3.ControlDistanceGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The actual compact weighted input has its complete global
weight-two norm bounded by its constructed source Hölder norm and its
supremum. One constant precedes all centers, subdomains and jet families. -/
theorem compact_full_holder_estimate_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (μ : G2.GroupMollifier G H.norm) (φ : G2.GroupMollifier G C.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : Fin N → ℝ, ∀ U : Opens (Fin N → ℝ),
      (U : Set (Fin N → ℝ)) ⊆ quasiballDomain G C.norm z R →
      ∀ u : (Fin N → ℝ) → ℝ,
      memHolderXCompact driftWeight H.fields (controlDistance univ driftWeight H.fields) U 2 a u →
      tsupport u ⊆ (U : Set (Fin N → ℝ)) →
      ∀ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
      jet [] = u →
      (∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv H.fields ⊤ I u (jet I) ∧
        Continuous (jet I) ∧ HasCompactSupport (jet I) ∧ tsupport (jet I) ⊆ U) →
      holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields) ⊤ 2 a u ≤
        ENNReal.ofReal A *
          (holderENorm (controlDistance univ driftWeight H.fields) a univ
            (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) + eLpNorm u ⊤ volume) := by
  classical
  obtain ⟨C₂, hC₂, hsecond⟩ := local_uniform_estimate_of_controlNorm G H K hQ C φ a ha ha1 hR
  obtain ⟨C₁, hC₁, hfirst⟩ := intrinsic_first_holderX_estimate_of_controlNorm
    G H K C hQ μ ν hν ha ha1 hR
  let D := C₁ * (1 / 2 : ℝ) ^ (-(2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (a : ℝ))))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let A := 1 + C₂ + D
  refine ⟨A, by dsimp [A]; linarith, ?_⟩
  intro z U hU u hu hs jet hz hj
  have hind : (U : Set (Fin N → ℝ)).indicator u = u := by
    funext x
    by_cases hx : x ∈ (U : Set (Fin N → ℝ))
    · exact indicator_of_mem hx u
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))).symm
  obtain ⟨v, hv0, hv, hsource, _heq, hb⟩ := hsecond z U hU u hu
  rw [hind] at hv0 hv hb
  have he (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) : v I = jet I :=
    funext fun x => S.hasIntrinsicWordDeriv_unique ⊤ H.fields I
      (hv I hI).1 (hj I hI).1 (mem_univ x)
  have he0 := he [0] (by simp [wordWeight, driftWeight])
  have he2 (i : Fin q) := he [i.succ, i.succ] (by simp [wordWeight, driftWeight])
  simp only [he0, he2] at hsource hb
  let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
  have hFfinite : holderENorm (controlDistance univ driftWeight H.fields) a univ F < ⊤ := hsource.1
  let geom := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  have hFsup := eLpNorm_top_le_local_holderNorm ⊤ ⊤ geom (subset_univ _) ha (f := F) hFfinite
  have hFsup' : eLpNorm F ⊤ volume ≤
      holderENorm (controlDistance univ driftWeight H.fields) a univ F := by
    simpa only [geom, controlDistanceGeometry_of_controlNorm, Opens.coe_top, Measure.restrict_univ, NNReal.toReal] using hFsup
  have hFLp : MemLp F ⊤ volume := hFsup'.trans_lt hFfinite
  have huLp : MemLp (jet []) ⊤ volume := (hj [] (by simp [wordWeight])).2.1.memLp_of_hasCompactSupport
    (hj [] (by simp [wordWeight])).2.2.1
  rw [hz] at huLp
  have hbfirst := hfirst z u jet hz (fun I hI => (hj I hI).1)
    (fun I hI => (hj I hI).2.1) (fun I hI => (hj I hI).2.2.1)
    (fun I hI => ((hj I hI).2.2.2.trans hU)) (1 / 2) (by norm_num) (by norm_num)
  dsimp only at hbfirst
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ofReal_lpNorm hFLp,
    ENNReal.ofReal_mul hD, ofReal_lpNorm huLp] at hbfirst
  have hbfirst' : holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
      ⊤ 1 a u ≤ holderENorm (controlDistance univ driftWeight H.fields) a univ F +
        ENNReal.ofReal D * eLpNorm u ⊤ volume :=
    hbfirst.trans (add_le_add (by
      exact (mul_le_mul' (show ENNReal.ofReal (1 / 2 : ℝ) ≤ 1 by norm_num) hFsup').trans_eq (one_mul _)) le_rfl)
  have hc1 : 1 + ENNReal.ofReal C₂ ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hC₂.le]
    exact ENNReal.ofReal_le_ofReal (by dsimp [A]; linarith)
  have hcD : ENNReal.ofReal D ≤ ENNReal.ofReal A :=
    ENNReal.ofReal_le_ofReal (by dsimp [A]; linarith)
  rw [holderXENorm_drift_two_split]
  have hsum := add_le_add hbfirst' hb
  have hrepr : intrinsicWordENorm H.fields (controlDistance univ driftWeight H.fields) ⊤ [0] a u +
      ∑ i : Fin q, ∑ j : Fin q,
        intrinsicWordENorm H.fields (controlDistance univ driftWeight H.fields) ⊤ [i.succ, j.succ] a u =
      ∑ I ∈ driftSecondWordFamily q,
        intrinsicWordENorm H.fields (controlDistance univ driftWeight H.fields) ⊤ I a u :=
    (sum_driftSecondWordFamily (q := q) (fun I =>
      intrinsicWordENorm H.fields (controlDistance univ driftWeight H.fields) ⊤ I a u)).symm
  rw [add_assoc, hrepr]
  exact hsum.trans (by
    calc
      _ = (1 + ENNReal.ofReal C₂) * holderENorm (controlDistance univ driftWeight H.fields) a univ F +
          ENNReal.ofReal D * eLpNorm u ⊤ volume := by rw [add_mul, one_mul]; ac_rfl
      _ ≤ ENNReal.ofReal A * holderENorm (controlDistance univ driftWeight H.fields) a univ F +
          ENNReal.ofReal A * eLpNorm u ⊤ volume := add_le_add (mul_le_mul' hc1 le_rfl) (mul_le_mul' hcD le_rfl)
      _ = _ := (mul_add _ _ _).symm)

end RothschildStein.H3
