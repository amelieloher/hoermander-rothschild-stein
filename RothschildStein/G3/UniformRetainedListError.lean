-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.UniformRetainedListJetBounds
public import RothschildStein.G3.RetainedLieScalarProductJets
public import RothschildStein.G3.FiniteJetPointRemainder
public import RothschildStein.G3.GeneralLieCommonFlowJets
public import RothschildStein.G3.EndpointZeroOnDomain
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- Actual weighted finite lists have a common numerical BCH remainder, with
constants selected before the spatial centre set and primitive fields. -/
theorem exists_uniform_retainedLie_list_BCH_error {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (hs : 1 ≤ s) {r B T : ℝ}
    (hr : 0 < r) (hB : 0 ≤ B) (hT : 0 ≤ T) (L : ℕ) :
    ∃ η M σ : ℝ, 0 < η ∧ 0 < M ∧ 0 < σ ∧
      ∀ (K : Set (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)),
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (centreBuffer K r)) →
        (∀ x ∈ centreBuffer K r, ∀ i j, j ≤ 3*s+2 → ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B) →
        ∃ Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ),
          ContDiffOn ℝ (⊤ : ℕ∞) Φ
            ((ball 0 σ ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ))) ×ˢ Ioo (-2) 2) ∧
          (∀ f : formalSpan a s p, D.basis.equivFun f ∈ ball 0 σ →
            ∀ x ∈ centreBuffer K (r/2), Φ ((D.basis.equivFun f,x),0) = x ∧
              ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun f,x),t) ∈ centreBuffer K r ∧
                HasDerivAt (fun v => Φ ((D.basis.equivFun f,x),v))
                  (finiteLieField D X f (Φ ((D.basis.equivFun f,x),t))) t) ∧
          ∀ fs : List (formalSpan a s p), fs.length ≤ L →
            (∀ f ∈ fs, ‖D.basis.equivFun f‖ ≤ T) →
            ‖D.basis.equivFun (retainedLieListProduct fs)‖ ≤ T →
            ∀ x ∈ K, ∀ t : ℝ, |t| < η →
              ‖runRetainedLiePointList D Φ fs t x - finiteLieTimeOneMap Φ
                (dilatedInputCoordinates D (retainedLieListProduct fs) t,x)‖ ≤ M*|t| ^(s+1) := by
  obtain ⟨η,M,σ,hη,hM,hσ,hflow⟩ := exists_uniform_retainedLie_list_jet_bounds
    (N := N) (R := 3*s+2) (Q := s+1) D hr hB hT (by omega) (by omega) (max L 1)
  refine ⟨η,2*M,σ,hη,by positivity,hσ,?_⟩
  intro K X hX hXjet
  obtain ⟨Φ,hΦ,hODE,hnum⟩ := hflow K X hX hXjet
  refine ⟨Φ,hΦ,hODE,?_⟩
  intro fs hlen hcoeff hprod x hx t ht
  let P := retainedLieListProduct fs
  have hsingle : ∀ f ∈ [P], ‖D.basis.equivFun f‖ ≤ T := by
    intro f hf
    obtain rfl := List.mem_singleton.mp hf
    exact hprod
  have hfsnum := hnum fs (hlen.trans (le_max_left _ _)) hcoeff x hx
  have hPnum := hnum [P] (by simp) hsingle x hx
  let ε := min σ (r/4)
  have hε : 0 < ε := lt_min hσ (by positivity)
  have hxdom : x ∈ centreBuffer K (r/2) := centreBuffer_self_mem (by positivity) hx
  have hlocal : ContDiffOn ℝ (⊤ : ℕ∞) Φ
      ((ball 0 ε ×ˢ ball x ε) ×ˢ Ioo (-2) 2) := by
    apply hΦ.mono
    intro z hz
    refine ⟨⟨ball_subset_ball (min_le_left _ _) hz.1.1,?_⟩,hz.2⟩
    exact mem_centreBuffer_iff.mpr ⟨x,hx,
      ball_subset_ball (by dsimp [ε]; linarith [min_le_right σ (r/4)]) hz.1.2⟩
  have hzero : ∀ y ∈ ball x ε, finiteLieTimeOneMap Φ (0,y) = y := by
    intro y hy
    have hym : y ∈ centreBuffer K (r/2) := mem_centreBuffer_iff.mpr ⟨x,hx,
      ball_subset_ball (by dsimp [ε]; linarith [min_le_right σ (r/4)]) hy⟩
    exact finiteLie_endpoint_zero_on_initial_domain D X hσ Φ
      (fun f hf z hz => ⟨(hODE f hf z hz).1,
        fun u hu => ((hODE f hf z hz).2 u hu).2⟩) y hym
  have hpairs := fun f g => generalLie_joint_BCH_jets_of_common_flow D
    (centreBuffer K r) (centreBuffer K (r/2)) X hX Φ hσ hε hB hODE hXjet
    f g hs hxdom hlocal (hzero x (by simpa using hε))
  let H := fun q : ℝ × (Fin N → ℝ) => (q.1,x+q.2)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := contDiff_fst.prodMk (contDiff_const.add contDiff_snd)
  have hz : |(0 : ℝ)| < η := by simpa using hη
  have hjoint : ContDiffAt ℝ s (fun q : ℝ × (Fin N → ℝ) =>
      runRetainedLiePointList D Φ fs q.1 (x+q.2)) 0 := by
    have hh := (hfsnum 0 hz).1
    have he : H 0 = (0,x) := by change (0,x+0) = (0,x); rw [add_zero]
    rw [← he] at hh
    exact (hh.comp (g := fun q : ℝ × (Fin N → ℝ) =>
      runRetainedLiePointList D Φ fs q.1 q.2) (f := H) 0 (hH.contDiffAt.of_le (by simp))).of_le (by simp)
  have hmatch := retainedLiePointList_scalar_jets_eq_product D hε Φ hlocal hzero hpairs fs hjoint
  have hsegment (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : |u • t| < η := by
    rw [smul_eq_mul,abs_mul,abs_of_nonneg hu.1]
    exact (mul_le_of_le_one_left (abs_nonneg t) hu.2).trans_lt ht
  have hfun : (fun v => runRetainedLiePointList D Φ [P] v x) =
      (fun v => finiteLieTimeOneMap Φ (dilatedInputCoordinates D P v,x)) := rfl
  have he := norm_point_error_of_finite_matching_jets
    (fun v => runRetainedLiePointList D Φ fs v x)
    (fun v => runRetainedLiePointList D Φ [P] v x) s t hM.le hM.le
    (fun u hu => (hfsnum _ (hsegment u hu)).2.1)
    (fun u hu => (hPnum _ (hsegment u hu)).2.1)
    (by simpa only [hfun] using hmatch)
    (fun u hu => (hfsnum _ (hsegment u hu)).2.2 (s+1) (by omega) le_rfl)
    (fun u hu => (hPnum _ (hsegment u hu)).2.2 (s+1) (by omega) le_rfl)
  change ‖runRetainedLiePointList D Φ fs t x - finiteLieTimeOneMap Φ
    (dilatedInputCoordinates D P t,x)‖ ≤ (M+M)*‖t‖^(s+1) at he
  simpa only [Real.norm_eq_abs,two_mul] using he
end RothschildStein.G3
