-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingSolve
public import RothschildStein.P2.SmoothingRegularity
public import RothschildStein.Distribution.SmoothPartitionInfrastructure
public import RothschildStein.Definitions.representsDistribution

/-!
# Distributional smoothing, gluing: overlapping cylinders give the same distribution

The local-to-global step of the proof of BB Thm 11.62 (p. 610). Local representatives of one
distribution `T ∈ 𝒟'(Ω)` on an open cover `{U i}` agree almost everywhere on the overlaps
(`Distribution.ofFun_injective`), and in the continuous case everywhere, and glue to one
representative on `Ω`:

* `distribution_eq_zero_of_local_test_vanishing_real`: a real distribution that vanishes on tests
  supported in a neighborhood of every point is zero (finite smooth partitions of the compact
  support of a test; the real-test version of the complex gluing lemma of the hypoellipticity theorem);
* `exists_locallyIntegrable_gluing`: `L¹_loc` representatives, a.e. equal on the cover (the
  countable subcover is chosen by second countability);
* `exists_continuous_gluing`: continuous representatives glue to a continuous function equal to each
  of them on its open set;
* `exists_hasWeakWordDeriv_gluing`: weak word derivatives that exist locally glue to a weak word
  derivative on `Ω`, equal a.e. to each local one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators Distributions
namespace RothschildStein.P2

section Vanishing

variable {N : ℕ}

/-- A real distribution that vanishes on all tests supported near each point is zero
(a finite smooth partition of the compact support of a test; BB p. 610, gluing). -/
theorem distribution_eq_zero_of_local_test_vanishing_real (Ω : Opens (Fin N → ℝ))
    (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (hlocal : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ W : Set (Fin N → ℝ),
      IsOpen W ∧ x ∈ W ∧ ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), tsupport ψ ⊆ W → T ψ = 0) :
    T = 0 := by
  classical
  choose W hW hxW hzero using fun x : Ω => hlocal x x.property
  let U (x : Fin N → ℝ) := if hx : x ∈ (Ω : Set (Fin N → ℝ)) then W ⟨x, hx⟩ else univ
  ext ψ
  change T ψ = 0
  have hU : ∀ x ∈ tsupport ψ, U x ∈ nhds x := by
    intro x hx
    have hxΩ := ψ.tsupport_subset hx
    simpa only [U, dite_eq_left hxΩ] using (hW ⟨x, hxΩ⟩).mem_nhds (hxW ⟨x, hxΩ⟩)
  obtain ⟨ι, ρ, c, hρfin, hρsum, hρsmooth, hcK, hρsub⟩ :=
    RothschildStein.Distribution.exists_smooth_partition_on_compact (tsupport ψ)
      ψ.hasCompactSupport U hU
  have hfin := hρfin.finite_nonempty_inter_compact ψ.hasCompactSupport
  let s := hfin.toFinset
  let p (i : ι) : TestFunction Ω ℝ (⊤ : ℕ∞) :=
    TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) (hρsmooth i) ψ
  have hpcoe (i : ι) : (p i : (Fin N → ℝ) → ℝ) = fun x => ψ x * ρ i x := by
    simpa only [p, ContinuousLinearMap.mul_apply'] using
      TestFunction.bilinLeftCLM_apply (ContinuousLinearMap.mul ℝ ℝ) (hρsmooth i) ψ
  have hpapply (i : ι) (x : Fin N → ℝ) : p i x = ψ x * ρ i x := congrFun (hpcoe i) x
  have hp (i : ι) : T (p i) = 0 := by
    have hcΩ := ψ.tsupport_subset (hcK i)
    apply hzero ⟨c i, hcΩ⟩ (p i)
    have hsub := (tsupport_mul_subset_right (f := fun x => ψ x) (g := fun x => ρ i x)).trans
      (hρsub i)
    rw [hpcoe]
    simpa only [U, dite_eq_left hcΩ] using hsub
  have he : ∑ i ∈ s, p i = ψ := by
    ext x
    let ev : TestFunction Ω ℝ (⊤ : ℕ∞) →+ ℝ :=
      { toFun := fun φ => φ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    change ev (∑ i ∈ s, p i) = ψ x
    rw [map_sum]
    change (∑ i ∈ s, p i x) = ψ x
    simp_rw [hpapply]
    rw [← Finset.mul_sum]
    by_cases hx : x ∈ tsupport ψ
    · have hsub : Function.support (fun i => ρ i x) ⊆ s := by
        intro i hi
        apply hfin.mem_toFinset.mpr
        exact ⟨x, hi, hx⟩
      rw [← finsum_eq_sum_of_support_subset _ hsub, hρsum x hx, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [← he, map_sum]
  simp only [hp, Finset.sum_const_zero]

/-- Representatives of a distribution on the cover, in the test-supported form: if `T` is represented
by `u` on the open set `A ≤ Ω` (`representsDistribution A (T|_A) u`) then `T ψ = ∫ ψ u` for every test
`ψ` of `Ω` with support in `A`. -/
theorem integral_eq_of_representsDistribution (Ω A : Opens (Fin N → ℝ)) (hA : A ≤ Ω)
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) {u : (Fin N → ℝ) → ℝ}
    (h : representsDistribution A (RothschildStein.S.distributionRestrictionCLM Ω A T) u)
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) (hψ : tsupport (ψ : (Fin N → ℝ) → ℝ) ⊆ A) :
    T ψ = ∫ x, ψ x * u x := by
  let ψ' : TestFunction A ℝ (⊤ : ℕ∞) := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψ⟩
  have h1 := congrArg (fun D : Distribution A ℝ (⊤ : ℕ∞) => D ψ') h.2
  simp only [RothschildStein.S.distributionRestrictionCLM_apply Ω A hA T ψ',
    Distribution.ofFun_apply h.1] at h1
  have : (⟨ψ', ψ'.contDiff, ψ'.hasCompactSupport, ψ'.tsupport_subset.trans hA⟩ :
      TestFunction Ω ℝ (⊤ : ℕ∞)) = ψ := rfl
  rw [this] at h1
  rw [h1]
  simp only [smul_eq_mul]
  rfl

end Vanishing

section Gluing

variable {N : ℕ}

/-- Local integrability is local. -/
theorem locallyIntegrableOn_of_forall_exists_open {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    {F : (Fin N → ℝ) → ℝ}
    (h : ∀ x ∈ Ω, ∃ A : Set (Fin N → ℝ), IsOpen A ∧ x ∈ A ∧ LocallyIntegrableOn F A volume) :
    LocallyIntegrableOn F Ω volume := by
  intro x hx
  obtain ⟨A, hA, hxA, hF⟩ := h x hx
  have := hF x hxA
  rwa [hA.nhdsWithin_eq hxA, ← hΩ.nhdsWithin_eq hx] at this

/-- A test supported in `U` pairs equally with two functions that agree a.e. on `U`. -/
theorem integral_mul_congr_of_ae_eq_on {U : Set (Fin N → ℝ)} (hU : MeasurableSet U)
    {Ω : Opens (Fin N → ℝ)} (ψ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hψ : tsupport (ψ : (Fin N → ℝ) → ℝ) ⊆ U) {F G : (Fin N → ℝ) → ℝ}
    (h : F =ᵐ[volume.restrict U] G) : ∫ x, ψ x * F x = ∫ x, ψ x * G x := by
  have hz : ∀ H : (Fin N → ℝ) → ℝ, ∀ x, x ∉ U → ψ x * H x = 0 := by
    intro H x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hψ ht)), zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (hz F),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (hz G)]
  refine setIntegral_congr_ae hU ?_
  filter_upwards [(ae_restrict_iff' hU).1 h] with x hx hxU
  rw [hx hxU]

variable {ι : Type*} (Ω : Opens (Fin N → ℝ)) (T : Distribution Ω ℝ (⊤ : ℕ∞))
  (U : ι → Opens (Fin N → ℝ)) (u : ι → (Fin N → ℝ) → ℝ)

/-- Local representatives of one distribution agree a.e. on overlaps
(`Distribution.ofFun_injective`). -/
theorem representatives_ae_eq_on_overlap (hUsub : ∀ i, U i ≤ Ω)
    (hu : ∀ i, LocallyIntegrableOn (u i) (U i : Set (Fin N → ℝ)) volume)
    (hrep : ∀ i, ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), tsupport (ψ : (Fin N → ℝ) → ℝ) ⊆ U i →
      T ψ = ∫ x, ψ x * u i x) (i j : ι) :
    u i =ᵐ[volume.restrict ((U i : Set (Fin N → ℝ)) ∩ U j)] u j := by
  let W : Opens (Fin N → ℝ) := U i ⊓ U j
  have hWi : (W : Set (Fin N → ℝ)) ⊆ U i := inter_subset_left
  have hWj : (W : Set (Fin N → ℝ)) ⊆ U j := inter_subset_right
  have hfW : LocallyIntegrableOn (u i) (W : Set (Fin N → ℝ)) volume := (hu i).mono_set hWi
  have hgW : LocallyIntegrableOn (u j) (W : Set (Fin N → ℝ)) volume := (hu j).mono_set hWj
  have he : Distribution.ofFun W (u i) volume (⊤ : ℕ∞) = Distribution.ofFun W (u j) volume (⊤ : ℕ∞) := by
    ext ψ
    let φ : TestFunction Ω ℝ (⊤ : ℕ∞) :=
      ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset.trans (hWi.trans (hUsub i))⟩
    rw [Distribution.ofFun_apply hfW, Distribution.ofFun_apply hgW]
    have h1 := hrep i φ (ψ.tsupport_subset.trans hWi)
    have h2 := hrep j φ (ψ.tsupport_subset.trans hWj)
    simp only [smul_eq_mul]
    exact (h1.symm.trans h2)
  exact Distribution.ofFun_injective hfW hgW he

/-- If a locally integrable `F` equals each local representative a.e. on its open set, then `T` is
the distribution of `F` (local vanishing of `T - ofFun F`). -/
theorem eq_ofFun_of_local_representatives
    (hcover : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ i, x ∈ (U i : Set (Fin N → ℝ)))
    (hrep : ∀ i, ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), tsupport (ψ : (Fin N → ℝ) → ℝ) ⊆ U i →
      T ψ = ∫ x, ψ x * u i x)
    {F : (Fin N → ℝ) → ℝ} (hF : LocallyIntegrableOn F (Ω : Set (Fin N → ℝ)) volume)
    (hae : ∀ i, F =ᵐ[volume.restrict (U i : Set (Fin N → ℝ))] u i) :
    T = Distribution.ofFun Ω F volume (⊤ : ℕ∞) := by
  have hz : T - Distribution.ofFun Ω F volume (⊤ : ℕ∞) = 0 := by
    apply distribution_eq_zero_of_local_test_vanishing_real
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    refine ⟨U i, (U i).isOpen, hi, fun ψ hψ => ?_⟩
    have h4 : (T - Distribution.ofFun Ω F volume (⊤ : ℕ∞)) ψ =
        T ψ - Distribution.ofFun Ω F volume (⊤ : ℕ∞) ψ := rfl
    rw [h4, Distribution.ofFun_apply hF, hrep i ψ hψ]
    simp only [smul_eq_mul]
    exact sub_eq_zero.2 (integral_mul_congr_of_ae_eq_on (U i).isOpen.measurableSet ψ hψ (hae i)).symm
  exact sub_eq_zero.1 hz

/-- **Gluing of locally integrable representatives.** Let `{U i}` be an open cover of
`Ω` and `u i` locally integrable representatives of `T` on `U i` (`T ψ = ∫ ψ u_i` for tests supported
in `U i`). Then there is one locally integrable representative `F` of `T` on `Ω` with
`F = u_i` almost everywhere on every `U i`. Overlapping local representatives agree a.e.
(`Distribution.ofFun_injective`); second countability gives a countable subcover, on which `F` is
defined by the first index (BB p. 610). -/
theorem exists_locallyIntegrable_gluing (hUsub : ∀ i, U i ≤ Ω)
    (hcover : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ i, x ∈ (U i : Set (Fin N → ℝ)))
    (hu : ∀ i, LocallyIntegrableOn (u i) (U i : Set (Fin N → ℝ)) volume)
    (hrep : ∀ i, ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), tsupport (ψ : (Fin N → ℝ) → ℝ) ⊆ U i →
      T ψ = ∫ x, ψ x * u i x) :
    ∃ F : (Fin N → ℝ) → ℝ, LocallyIntegrableOn F (Ω : Set (Fin N → ℝ)) volume ∧
      T = Distribution.ofFun Ω F volume (⊤ : ℕ∞) ∧
      ∀ i, F =ᵐ[volume.restrict (U i : Set (Fin N → ℝ))] u i := by
  classical
  have hij : ∀ i j, ∀ᵐ x ∂(volume : Measure (Fin N → ℝ)), x ∈ (U i : Set (Fin N → ℝ)) →
      x ∈ (U j : Set (Fin N → ℝ)) → u i x = u j x := by
    intro i j
    have := (ae_restrict_iff' ((U i).isOpen.inter (U j).isOpen).measurableSet).1
      (representatives_ae_eq_on_overlap Ω T U u hUsub hu hrep i j)
    filter_upwards [this] with x hx hxi hxj using hx ⟨hxi, hxj⟩
  obtain ⟨S, hSc, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i => (U i : Set (Fin N → ℝ))) (fun i => (U i).isOpen)
  have hΩS : ∀ x : Ω, ∃ i ∈ S, (x : Fin N → ℝ) ∈ (U i : Set (Fin N → ℝ)) := by
    intro x
    obtain ⟨i, hi⟩ := hcover x x.2
    have : (x : Fin N → ℝ) ∈ ⋃ i ∈ S, (U i : Set (Fin N → ℝ)) := by
      rw [hSU]; exact mem_iUnion.2 ⟨i, hi⟩
    simpa using this
  choose idx hidxS hidx using hΩS
  let F : (Fin N → ℝ) → ℝ := fun x => if hx : x ∈ (Ω : Set (Fin N → ℝ)) then
    u (idx ⟨x, hx⟩) x else 0
  have hFae : ∀ j, F =ᵐ[volume.restrict (U j : Set (Fin N → ℝ))] u j := by
    intro j
    have : Countable S := hSc.to_subtype
    have hall : ∀ᵐ x ∂(volume : Measure (Fin N → ℝ)), ∀ i : S, x ∈ (U i : Set (Fin N → ℝ)) →
        x ∈ (U j : Set (Fin N → ℝ)) → u i x = u j x := by
      rw [ae_all_iff]
      intro i
      exact hij i j
    rw [Filter.EventuallyEq, ae_restrict_iff' (U j).isOpen.measurableSet]
    filter_upwards [hall] with x hx hxj
    have hxΩ : x ∈ (Ω : Set (Fin N → ℝ)) := hUsub j hxj
    have hFx : F x = u (idx ⟨x, hxΩ⟩) x := by
      simp only [F]
      split_ifs
      rfl
    rw [hFx]
    exact hx ⟨idx ⟨x, hxΩ⟩, hidxS ⟨x, hxΩ⟩⟩ (hidx ⟨x, hxΩ⟩) hxj
  have hFloc : LocallyIntegrableOn F (Ω : Set (Fin N → ℝ)) volume := by
    refine locallyIntegrableOn_of_forall_exists_open Ω.isOpen fun x hx => ?_
    obtain ⟨j, hj⟩ := hcover x hx
    exact ⟨U j, (U j).isOpen, hj, (hu j).congr (hFae j).symm⟩
  exact ⟨F, hFloc, eq_ofFun_of_local_representatives Ω T U u hcover hrep hFloc hFae, hFae⟩

/-- **Gluing of continuous representatives.** If the local representatives `u i` are
continuous on `U i`, then they agree everywhere on the overlaps (an a.e. identity between continuous
functions on an open set) and glue to a continuous representative `F` of `T` with `F = u i` on all
of `U i` (BB p. 610: "in the continuous case everywhere"). -/
theorem exists_continuous_gluing (hUsub : ∀ i, U i ≤ Ω)
    (hcover : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ i, x ∈ (U i : Set (Fin N → ℝ)))
    (hu : ∀ i, ContinuousOn (u i) (U i : Set (Fin N → ℝ)))
    (hrep : ∀ i, ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), tsupport (ψ : (Fin N → ℝ) → ℝ) ⊆ U i →
      T ψ = ∫ x, ψ x * u i x) :
    ∃ F : (Fin N → ℝ) → ℝ, ContinuousOn F (Ω : Set (Fin N → ℝ)) ∧
      T = Distribution.ofFun Ω F volume (⊤ : ℕ∞) ∧
      ∀ i, EqOn F (u i) (U i : Set (Fin N → ℝ)) := by
  classical
  have hui : ∀ i, LocallyIntegrableOn (u i) (U i : Set (Fin N → ℝ)) volume :=
    fun i => (hu i).locallyIntegrableOn (U i).isOpen.measurableSet
  have hov : ∀ i j, EqOn (u i) (u j) ((U i : Set (Fin N → ℝ)) ∩ U j) := fun i j =>
    Measure.eqOn_open_of_ae_eq (representatives_ae_eq_on_overlap Ω T U u hUsub hui hrep i j)
      ((U i).isOpen.inter (U j).isOpen) ((hu i).mono inter_subset_left)
      ((hu j).mono inter_subset_right)
  choose idx hidx using fun x : Ω => hcover x x.2
  let F : (Fin N → ℝ) → ℝ := fun x => if hx : x ∈ (Ω : Set (Fin N → ℝ)) then
    u (idx ⟨x, hx⟩) x else 0
  have hFeq : ∀ j, EqOn F (u j) (U j : Set (Fin N → ℝ)) := by
    intro j x hxj
    have hxΩ : x ∈ (Ω : Set (Fin N → ℝ)) := hUsub j hxj
    have hFx : F x = u (idx ⟨x, hxΩ⟩) x := by
      simp only [F]
      split_ifs
      rfl
    rw [hFx]
    exact hov _ j ⟨hidx ⟨x, hxΩ⟩, hxj⟩
  have hFc : ContinuousOn F (Ω : Set (Fin N → ℝ)) := by
    intro x hx
    obtain ⟨j, hj⟩ := hcover x hx
    have hat : ContinuousAt F x :=
      ((hu j).continuousAt ((U j).isOpen.mem_nhds hj)).congr
        (Filter.eventuallyEq_of_mem ((U j).isOpen.mem_nhds hj) (fun y hy => (hFeq j hy).symm))
    exact hat.continuousWithinAt
  have hFloc : LocallyIntegrableOn F (Ω : Set (Fin N → ℝ)) volume :=
    hFc.locallyIntegrableOn Ω.isOpen.measurableSet
  have hae : ∀ i, F =ᵐ[volume.restrict (U i : Set (Fin N → ℝ))] u i := fun i =>
    (ae_restrict_iff' (U i).isOpen.measurableSet).2 (Eventually.of_forall fun x hx => hFeq i hx)
  exact ⟨F, hFc, eq_ofFun_of_local_representatives Ω T U u hcover hrep hFloc hae, hFeq⟩

end Gluing

section WeakGluing

variable {N k : ℕ}

/-- A weak word derivative on an open `A ≤ Ω` pairs with tests of `Ω` supported in `A`, in global
integrals: `∫ (X_I^T ψ) f = ∫ ψ g`. -/
theorem integral_wordTranspose_eq_of_supported (X : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    {Ω A : Opens (Fin N → ℝ)} {I : List (Fin k)} {f g : (Fin N → ℝ) → ℝ}
    (h : hasWeakWordDeriv X A I f g) (ψ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hψ : tsupport (ψ : (Fin N → ℝ) → ℝ) ⊆ A) :
    ∫ x, wordTranspose X I ψ x * f x = ∫ x, ψ x * g x := by
  let ψ' : TestFunction A ℝ (⊤ : ℕ∞) := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψ⟩
  have h1 := h.2.2 ψ'
  have hz1 : ∀ x, x ∉ (A : Set (Fin N → ℝ)) → ψ x * g x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hψ ht)), zero_mul]
  have hz2 : ∀ x, x ∉ (A : Set (Fin N → ℝ)) → wordTranspose X I ψ x * f x = 0 := by
    intro x hx
    have : wordTranspose X I ψ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hψ (RothschildStein.S.tsupport_wordTranspose_subset X I ψ ht)))
    rw [this, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz1,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hz2]
  change (∫ x in (A : Set (Fin N → ℝ)), g x * ψ x) =
    ∫ x in (A : Set (Fin N → ℝ)), f x * wordTranspose X I ψ x at h1
  simp_rw [mul_comm] at h1 ⊢
  exact h1.symm

/-- The distribution `X_I T` of `T = u`, evaluated on tests supported in `U i`, is represented by the
local weak derivative `g i`. -/
theorem distributionWord_ofFun_apply_of_supported (X : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ)) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (I : List (Fin k)) {u : (Fin N → ℝ) → ℝ}
    (hu : LocallyIntegrableOn u (Ω : Set (Fin N → ℝ)) volume) {A : Opens (Fin N → ℝ)}
    {g : (Fin N → ℝ) → ℝ} (hg : hasWeakWordDeriv X A I u g) (ψ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hψ : tsupport (ψ : (Fin N → ℝ) → ℝ) ⊆ A) :
    RothschildStein.S.distributionWordCLM Ω X hX I (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) ψ =
      ∫ x, ψ x * g x := by
  rw [RothschildStein.S.distributionWordCLM_apply, Distribution.ofFun_apply hu]
  simp only [smul_eq_mul]
  rw [← integral_wordTranspose_eq_of_supported X hg ψ hψ]
  simp_rw [RothschildStein.S.wordTransposeTest_apply]

/-- If the distribution `X_I T` of `T = u` is the regular distribution of `G`, then `G` is the weak
word derivative `X_I u`. -/
theorem hasWeakWordDeriv_of_distributionWord_eq (X : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ)) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (I : List (Fin k)) {u G : (Fin N → ℝ) → ℝ}
    (hu : LocallyIntegrableOn u (Ω : Set (Fin N → ℝ)) volume)
    (hG : LocallyIntegrableOn G (Ω : Set (Fin N → ℝ)) volume)
    (h : RothschildStein.S.distributionWordCLM Ω X hX I (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) =
      Distribution.ofFun Ω G volume (⊤ : ℕ∞)) : hasWeakWordDeriv X Ω I u G := by
  refine ⟨hu, hG, fun φ => ?_⟩
  have h1 := congrArg (fun T : Distribution Ω ℝ (⊤ : ℕ∞) => T φ) h
  simp only [RothschildStein.S.distributionWordCLM_apply] at h1
  rw [ofFun_apply_eq_setIntegral Ω hu, ofFun_apply_eq_setIntegral Ω hG] at h1
  simp_rw [RothschildStein.S.wordTransposeTest_apply] at h1
  refine h1.symm.trans ?_
  congr 1

/-- **Gluing of weak word derivatives.** If `u ∈ L¹_loc(Ω)` has a weak word derivative
`X_I u = g i` on each set `U i` of an open cover of `Ω`, then it has a weak word derivative `G` on
`Ω`, and `G = g i` almost everywhere on `U i` (the distribution `X_I T` of `T = u` is represented
locally by the `g i`; BB p. 609-610). -/
theorem exists_hasWeakWordDeriv_gluing (X : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ)) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (I : List (Fin k)) {u : (Fin N → ℝ) → ℝ}
    (hu : LocallyIntegrableOn u (Ω : Set (Fin N → ℝ)) volume) {ι : Type*}
    (U : ι → Opens (Fin N → ℝ)) (hUsub : ∀ i, U i ≤ Ω)
    (hcover : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ i, x ∈ (U i : Set (Fin N → ℝ)))
    (g : ι → (Fin N → ℝ) → ℝ) (hg : ∀ i, hasWeakWordDeriv X (U i) I u (g i)) :
    ∃ G : (Fin N → ℝ) → ℝ, hasWeakWordDeriv X Ω I u G ∧
      ∀ i, G =ᵐ[volume.restrict (U i : Set (Fin N → ℝ))] g i := by
  obtain ⟨G, hGloc, hDG, hGae⟩ := exists_locallyIntegrable_gluing Ω
    (RothschildStein.S.distributionWordCLM Ω X hX I (Distribution.ofFun Ω u volume (⊤ : ℕ∞))) U g
    hUsub hcover (fun i => (hg i).2.1)
    (fun i ψ hψ => distributionWord_ofFun_apply_of_supported X Ω hX I hu (hg i) ψ hψ)
  exact ⟨G, hasWeakWordDeriv_of_distributionWord_eq X Ω hX I hu hGloc hDG, hGae⟩

/-- The continuous form: if the local weak derivatives `g i` are continuous on `U i`,
the glued weak derivative `G` is continuous on `Ω` and equal to `g i` on all of `U i`. -/
theorem exists_continuous_hasWeakWordDeriv_gluing (X : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ)) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (I : List (Fin k)) {u : (Fin N → ℝ) → ℝ}
    (hu : LocallyIntegrableOn u (Ω : Set (Fin N → ℝ)) volume) {ι : Type*}
    (U : ι → Opens (Fin N → ℝ)) (hUsub : ∀ i, U i ≤ Ω)
    (hcover : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ i, x ∈ (U i : Set (Fin N → ℝ)))
    (g : ι → (Fin N → ℝ) → ℝ) (hg : ∀ i, hasWeakWordDeriv X (U i) I u (g i))
    (hgc : ∀ i, ContinuousOn (g i) (U i : Set (Fin N → ℝ))) :
    ∃ G : (Fin N → ℝ) → ℝ, ContinuousOn G (Ω : Set (Fin N → ℝ)) ∧ hasWeakWordDeriv X Ω I u G ∧
      ∀ i, EqOn G (g i) (U i : Set (Fin N → ℝ)) := by
  obtain ⟨G, hGc, hDG, hGeq⟩ := exists_continuous_gluing Ω
    (RothschildStein.S.distributionWordCLM Ω X hX I (Distribution.ofFun Ω u volume (⊤ : ℕ∞))) U g
    hUsub hcover hgc
    (fun i ψ hψ => distributionWord_ofFun_apply_of_supported X Ω hX I hu (hg i) ψ hψ)
  exact ⟨G, hGc, hasWeakWordDeriv_of_distributionWord_eq X Ω hX I hu
    (hGc.locallyIntegrableOn Ω.isOpen.measurableSet) hDG, hGeq⟩

end WeakGluing

section Cylinders

variable {n m : ℕ}

/-- The product of two Euclidean balls of radius `ε` is inside the sup-norm ball of radius `ε`. -/
theorem cylinder_ball_subset_ball (x₀ : Fin n → ℝ) (t₀ : Fin m → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ((cylinder ⟨Metric.ball x₀ ε, Metric.isOpen_ball⟩ ⟨Metric.ball t₀ ε, Metric.isOpen_ball⟩ :
      Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) ⊆ Metric.ball (joinPoint x₀ t₀) ε := by
  intro ξ hξ
  obtain ⟨hx, ht⟩ := hξ
  have hx' : ‖basePoint ξ - x₀‖ < ε := by
    rw [← dist_eq_norm]; exact hx
  have ht' : ‖tailPoint ξ - t₀‖ < ε := by
    rw [← dist_eq_norm]; exact ht
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
  intro i
  refine Fin.addCases (fun j => ?_) (fun l => ?_) i
  · have := (norm_le_pi_norm (basePoint ξ - x₀) j).trans_lt hx'
    simpa [basePoint, joinPoint] using this
  · have := (norm_le_pi_norm (tailPoint ξ - t₀) l).trans_lt ht'
    simpa [tailPoint, joinPoint] using this

/-- Around a point `(x₀, 0)` of an open set `UR` there is a product cylinder `A × B` of finite
positive vertical volume whose closure is a compact subset of `UR` (BB p. 610). -/
theorem exists_cylinder_closure_subset {x₀ : Fin n → ℝ} {UR : Opens (Fin (n + m) → ℝ)}
    (h : joinPoint x₀ (0 : Fin m → ℝ) ∈ (UR : Set (Fin (n + m) → ℝ))) :
    ∃ (A : Opens (Fin n → ℝ)) (B : Opens (Fin m → ℝ)), x₀ ∈ (A : Set (Fin n → ℝ)) ∧
      (0 : Fin m → ℝ) ∈ (B : Set (Fin m → ℝ)) ∧
      IsCompact (closure (cylinder A B : Set (Fin (n + m) → ℝ))) ∧
      closure (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ (UR : Set (Fin (n + m) → ℝ)) ∧
      volume (B : Set (Fin m → ℝ)) < ⊤ ∧ 0 < volume (B : Set (Fin m → ℝ)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp UR.isOpen _ h
  have hε2 : 0 < ε / 2 := half_pos hε
  refine ⟨⟨Metric.ball x₀ (ε / 2), Metric.isOpen_ball⟩, ⟨Metric.ball (0 : Fin m → ℝ) (ε / 2),
    Metric.isOpen_ball⟩, Metric.mem_ball_self hε2, Metric.mem_ball_self hε2, ?_, ?_, ?_, ?_⟩
  · have hsub := (cylinder_ball_subset_ball x₀ (0 : Fin m → ℝ) hε2)
    exact (isCompact_closedBall _ (ε / 2)).of_isClosed_subset isClosed_closure
      (closure_minimal (hsub.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
  · have hsub := (cylinder_ball_subset_ball x₀ (0 : Fin m → ℝ) hε2)
    intro ξ hξ
    refine hball ?_
    have := closure_minimal (hsub.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall hξ
    exact Metric.closedBall_subset_ball (by linarith) this
  · exact measure_ball_lt_top
  · exact Metric.measure_ball_pos volume _ hε2

/-- A nonnegative test function of an open set around `t₀` with integral one. -/
theorem exists_test_integral_eq_one (B : Opens (Fin m → ℝ)) {t₀ : Fin m → ℝ}
    (ht₀ : t₀ ∈ (B : Set (Fin m → ℝ))) :
    ∃ η : TestFunction B ℝ (⊤ : ℕ∞), ∫ t : Fin m → ℝ, η t = 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp B.isOpen t₀ ht₀
  let b : ContDiffBump t₀ := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hsub : tsupport (b.normed volume) ⊆ (B : Set (Fin m → ℝ)) := by
    rw [b.tsupport_normed_eq]
    exact (Metric.closedBall_subset_ball (show b.rOut < ε by simp only [b]; linarith)).trans hball
  refine ⟨⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed, hsub⟩, ?_⟩
  exact b.integral_normed

end Cylinders

section LocalDescent

open RothschildStein.P1

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : P1.LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m)

/-- The cylinder data used by the descent at the centre of a chart: a cylinder `A × B` inside the
open set `UR ⊆ U` whose closure is compact in `UR`, the test `η`, and the restriction of the lifted
distribution to the cylinder. -/
theorem exists_cylinder_descent_data {UR : Opens (Fin (n + m) → ℝ)}
    (hξUR : joinPoint x₀ (0 : Fin m → ℝ) ∈ (UR : Set (Fin (n + m) → ℝ)))
    (hURU : (UR : Set (Fin (n + m) → ℝ)) ⊆ C.U) :
    ∃ (A : Opens (Fin n → ℝ)) (B : Opens (Fin m → ℝ)) (η : TestFunction B ℝ (⊤ : ℕ∞)),
      x₀ ∈ (A : Set (Fin n → ℝ)) ∧ (0 : Fin m → ℝ) ∈ (B : Set (Fin m → ℝ)) ∧
      IsCompact (closure (cylinder A B : Set (Fin (n + m) → ℝ))) ∧
      closure (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ (UR : Set (Fin (n + m) → ℝ)) ∧
      volume (B : Set (Fin m → ℝ)) < ⊤ ∧ 0 < volume (B : Set (Fin m → ℝ)) ∧
      (∫ t : Fin m → ℝ, η t = 1) ∧ (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ C.U ∧
      A ≤ liftedChartBaseOpens C := by
  obtain ⟨A, B, hxA, h0B, hcpt, hcl, hBfin, hBpos⟩ := exists_cylinder_closure_subset hξUR
  obtain ⟨η, hη⟩ := exists_test_integral_eq_one B h0B
  have hsubU : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    (subset_closure.trans hcl).trans hURU
  refine ⟨A, B, η, hxA, h0B, hcpt, hcl, hBfin, hBpos, hη, hsubU, fun x hx => ?_⟩
  have h1 : joinPoint x (0 : Fin m → ℝ) ∈ (cylinder A B : Set (Fin (n + m) → ℝ)) :=
    joinPoint_mem_cylinder.2 ⟨hx, h0B⟩
  have := liftedChart_basePoint_mem C (hsubU h1)
  rwa [basePoint_joinPoint] at this

/-- **Local representative, Sobolev case, under a `LocalSolvability` hypothesis.**
In a lifted drift chart `C` centred at `x₀`, let `T ∈ 𝒟'(Ω)` with `L T = f`, `f ∈ L^p(Ω)`,
`1 < p < ∞`. Then there is an open `A ∋ x₀`, `A ⊆ Ω`, and a function `u` representing `T|_A` with
`u ∈ W^{2,p}_X(A)` (`memSobolevX`): lift, solve (local solvability), subtract and descend
(`memSobolevX_descent`), on a cylinder `A × B` around the lift of `x₀` (BB pp. 608-610). -/
theorem exists_local_representative_sobolev_of_localSolvability (hP : LocalSolvability C) {p : ℝ≥0∞}
    (hp : 1 < p) (hpt : p < ⊤) (T : Distribution (liftedChartBaseOpens C) ℝ (⊤ : ℕ∞))
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f p (volume.restrict Ω))
    (hT : hasDistributionEquationWithDrift (liftedChartBaseOpens C) X
      (liftedChart_contDiffOn_base C) T f) :
    ∃ A : Opens (Fin n → ℝ), x₀ ∈ (A : Set (Fin n → ℝ)) ∧ A ≤ liftedChartBaseOpens C ∧
      ∃ u : (Fin n → ℝ) → ℝ,
        representsDistribution A
          (RothschildStein.S.distributionRestrictionCLM (liftedChartBaseOpens C) A T) u ∧
        memSobolevX driftWeight X A 2 p u := by
  obtain ⟨UR, hξUR, hURU, w, hwloc, hrepr, hSob⟩ :=
    solve_subtract_sobolev_of_localSolvability C hP hp hpt T hf hT C.center_mem
  obtain ⟨A, B, η, hxA, h0B, hcpt, hcl, hBfin, hBpos, hη, hsubU, hA⟩ :=
    exists_cylinder_descent_data C hξUR hURU
  have hsub : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ UR := subset_closure.trans hcl
  let S := liftedChart_cylinderFiberSetting C A B hsubU hBfin
  have hS : memSobolevX driftWeight C.Xl (cylinder A B) 2 p w := hSob (cylinder A B) hcpt hcl
  have hrepr_cyl : RothschildStein.S.distributionRestrictionCLM (liftedChartOpens C) (cylinder A B)
      (liftedChartLift C T) = Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞) := by
    rw [← distributionRestriction_restriction (liftedChartOpens C) UR (cylinder A B) hsub hURU,
      hrepr, distributionRestriction_ofFun UR (cylinder A B) hsub hwloc]
  have hT_cyl := (liftedChartFiberIntegration C).restrict_lift_ofFun hsubU hA S T hrepr_cyl
  obtain ⟨hrep, -, hmem⟩ := memSobolevX_descent driftWeight X C.P
    (fun i => (liftedChart_contDiffOn_lift C i).mono hsubU)
    (fun i => (liftedChart_contDiffOn_base C i).mono hA) S hη
    (RothschildStein.S.distributionRestrictionCLM (liftedChartBaseOpens C) A T) hT_cyl hp.le hpt.ne
    hBpos hBfin hS
  exact ⟨A, hxA, hA, fiberAvg w η, hrep, hmem⟩

/-- **Local representative, Hölder case,
under a `LocalSolvability` hypothesis.** In a lifted drift chart `C` centred at `x₀`, let `T ∈ 𝒟'(Ω)` with
`L T = f`, `f ∈ C^α_X(Ω)`, `0 < α < 1`. Then there is an open `A ∋ x₀`, `A ⊆ Ω`, and a continuous
function `u` representing `T|_A`, every word derivative `X_I u`, `I` of weight at most two, of which
exists as a continuous weak derivative on `A` (so is the intrinsic derivative,
`hasIntrinsicWordDeriv_of_continuous_weak_words`). -/
theorem exists_local_representative_holder_of_localSolvability (hP : LocalSolvability C) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (T : Distribution (liftedChartBaseOpens C) ℝ (⊤ : ℕ∞))
    {f : (Fin n → ℝ) → ℝ}
    (hf : memHolderX driftWeight X (controlDistance Ω driftWeight X) (liftedChartBaseOpens C) 0 α f)
    (hT : hasDistributionEquationWithDrift (liftedChartBaseOpens C) X
      (liftedChart_contDiffOn_base C) T f) :
    ∃ A : Opens (Fin n → ℝ), x₀ ∈ (A : Set (Fin n → ℝ)) ∧ A ≤ liftedChartBaseOpens C ∧
      ∃ u : (Fin n → ℝ) → ℝ,
        representsDistribution A
          (RothschildStein.S.distributionRestrictionCLM (liftedChartBaseOpens C) A T) u ∧
        ContinuousOn u (A : Set (Fin n → ℝ)) ∧
        ∀ I ∈ wordFamily driftWeight 2, ∃ g : (Fin n → ℝ) → ℝ,
          hasWeakWordDeriv X A I u g ∧ ContinuousOn g (A : Set (Fin n → ℝ)) := by
  obtain ⟨UR, hξUR, hURU, w, hwc, hrepr, hSob⟩ :=
    solve_subtract_holder_of_localSolvability C hP hα hα1 T hf hT C.center_mem
  obtain ⟨A, B, η, hxA, h0B, hcpt, hcl, hBfin, hBpos, hη, hsubU, hA⟩ :=
    exists_cylinder_descent_data C hξUR hURU
  have hsub : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ UR := subset_closure.trans hcl
  let S := liftedChart_cylinderFiberSetting C A B hsubU hBfin
  have hS : memHolderX driftWeight C.Xl C.dl (cylinder A B) 2 α w := hSob (cylinder A B) hcpt hcl
  have hwc' : ContinuousOn w (cylinder A B : Set (Fin (n + m) → ℝ)) := hwc.mono hsub
  have hwloc : LocallyIntegrableOn w (UR : Set (Fin (n + m) → ℝ)) volume :=
    hwc.locallyIntegrableOn UR.isOpen.measurableSet
  have hrepr_cyl : RothschildStein.S.distributionRestrictionCLM (liftedChartOpens C) (cylinder A B)
      (liftedChartLift C T) = Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞) := by
    rw [← distributionRestriction_restriction (liftedChartOpens C) UR (cylinder A B) hsub hURU,
      hrepr, distributionRestriction_ofFun UR (cylinder A B) hsub hwloc]
  have hT_cyl := (liftedChartFiberIntegration C).restrict_lift_ofFun hsubU hA S T hrepr_cyl
  obtain ⟨jet, hj0, hjet⟩ := exists_jets_of_memHolderX C hα hsubU hS
  have hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X C.P i)
      (cylinder A B : Set (Fin (n + m) → ℝ)) := fun i =>
    (liftedChart_contDiffOn_lift C i).mono hsubU
  have hXb : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (A : Set (Fin n → ℝ)) := fun i =>
    (liftedChart_contDiffOn_base C i).mono hA
  have hdesc : ∀ I ∈ wordFamily driftWeight 2,
      ContinuousOn (fun x => w (joinPoint x (0 : Fin m → ℝ))) (A : Set (Fin n → ℝ)) ∧
      ContinuousOn (fun x => jet I (joinPoint x (0 : Fin m → ℝ))) (A : Set (Fin n → ℝ)) ∧
      representsDistribution A
        (RothschildStein.S.distributionRestrictionCLM (liftedChartBaseOpens C) A T)
        (fun x => w (joinPoint x (0 : Fin m → ℝ))) ∧
      hasWeakWordDeriv X A I (fun x => w (joinPoint x (0 : Fin m → ℝ)))
        (fun x => jet I (joinPoint x (0 : Fin m → ℝ))) := by
    intro I hI
    obtain ⟨-, hweak, hcont, -⟩ := hjet I hI
    obtain ⟨h1, h2, h3, h4, -⟩ := hasWeakWordDeriv_descent_continuous X C.P hXt hXb S hη
      (RothschildStein.S.distributionRestrictionCLM (liftedChartBaseOpens C) A T)
      (hwc'.locallyIntegrableOn (cylinder A B).isOpen.measurableSet) hT_cyl I hweak hwc' hcont h0B
    exact ⟨h1, h2, h3, h4⟩
  have h00 := hdesc [] (RothschildStein.S.nil_mem_wordFamily driftWeight 2)
  exact ⟨A, hxA, hA, fun x => w (joinPoint x (0 : Fin m → ℝ)), h00.2.2.1, h00.1,
    fun I hI => ⟨fun x => jet I (joinPoint x (0 : Fin m → ℝ)), (hdesc I hI).2.2.2,
      (hdesc I hI).2.1⟩⟩

end LocalDescent

end RothschildStein.P2
