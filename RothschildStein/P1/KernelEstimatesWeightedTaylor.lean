-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesHomogeneous
public import RothschildStein.G1.HadamardFactor
public import RothschildStein.G1.LocalProductFactorization
public import RothschildStein.Definitions.rsPartial

/-!
# Weighted Taylor bounds from vanishing weighted jets

A function whose weighted jets of order `< b` vanish at the origin is bounded by `C ‖u‖^b` near
the origin, uniformly on a compact parameter set. The proof is by induction on `b` with the
Hadamard factorization along rays; no Taylor polynomial is formed. This supplies the
"remainder terms improve by one weight" step of the lifted kernel estimates (BB pp. 547–548, Lemma 11.16 and
Remark 11.17; BB pp. 569–571, Prop 11.32).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace RothschildStein.P1

variable {N : ℕ}

/-- Iterated partials compose by appending the index lists. -/
theorem rsPartial_append_single (J : List (Fin N)) (j : Fin N) (f : (Fin N → ℝ) → ℝ) :
    rsPartial J (rsPartial [j] f) = rsPartial (J ++ [j]) f := by
  induction J with
  | nil => rfl
  | cons a J ih =>
    show (fun u => fderiv ℝ (rsPartial J (rsPartial [j] f)) u (Pi.single a 1)) =
      fun u => fderiv ℝ (rsPartial (J ++ [j]) f) u (Pi.single a 1)
    rw [ih]

/-- Iterated coordinate partials of a smooth function are smooth. -/
theorem rsPartial_contDiff (J : List (Fin N)) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (rsPartial J f) := by
  induction J with
  | nil => exact hf
  | cons a J ih =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun u => fderiv ℝ (rsPartial J f) u (Pi.single a 1))
    exact ((contDiff_infty_iff_fderiv.mp ih).2).clm_apply contDiff_const

/-- Differentiation under the ray integral `∫₀¹ θ^k h(θ y) dθ` (Hadamard factor). -/
theorem hasFDerivAt_scaledIntegral (h : (Fin N → ℝ) → ℝ) (hh : ContDiff ℝ 1 h) (k : ℕ)
    (u : Fin N → ℝ) :
    HasFDerivAt (fun y : Fin N → ℝ => ∫ θ in Icc (0 : ℝ) 1, θ ^ k * h (θ • y))
      (∫ θ in Icc (0 : ℝ) 1, (θ ^ (k + 1)) • fderiv ℝ h (θ • u)) u := by
  have hD : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  refine RothschildStein.G1.compactParameterIntegral_hasFDerivAt
    (fun q : (Fin N → ℝ) × ℝ => q.2 ^ k * h (q.2 • q.1))
    (fun q => (q.2 ^ (k + 1)) • fderiv ℝ h (q.2 • q.1)) ?_ ?_ ?_ u
  · exact (continuous_snd.pow k).mul (hh.continuous.comp (continuous_snd.smul continuous_fst))
  · exact (continuous_snd.pow _).smul (hD.comp (continuous_snd.smul continuous_fst))
  · intro x t
    have h1 : HasFDerivAt (fun y : Fin N → ℝ => t • y) (t • ContinuousLinearMap.id ℝ (Fin N → ℝ)) x :=
      (hasFDerivAt_id x).const_smul t
    have h2 := ((hh.differentiable one_ne_zero (t • x)).hasFDerivAt.comp x h1).const_mul (t ^ k)
    refine h2.congr_fderiv ?_
    ext v
    simp [pow_succ, mul_comm]
    ring

/-- Iterated partials of the ray integral `∫₀¹ θ^k h(θ y) dθ`. -/
theorem rsPartial_scaledIntegral (h : (Fin N → ℝ) → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (J : List (Fin N)) (k : ℕ) :
    rsPartial J (fun y : Fin N → ℝ => ∫ θ in Icc (0 : ℝ) 1, θ ^ k * h (θ • y)) =
      fun y => ∫ θ in Icc (0 : ℝ) 1, θ ^ (k + J.length) * rsPartial J h (θ • y) := by
  induction J generalizing k with
  | nil => simp [rsPartial]
  | cons a J ih =>
    have hJ : ContDiff ℝ (⊤ : ℕ∞) (rsPartial J h) := rsPartial_contDiff J hh
    have hd := hasFDerivAt_scaledIntegral (rsPartial J h) (hJ.of_le (by simp)) (k + J.length)
    show (fun u => fderiv ℝ (rsPartial J (fun y : Fin N → ℝ => ∫ θ in Icc (0 : ℝ) 1, θ ^ k * h (θ • y))) u
      (Pi.single a 1)) = _
    rw [ih k]
    funext u
    rw [(hd u).fderiv]
    have hint : Integrable (fun θ : ℝ => (θ ^ (k + J.length + 1)) • fderiv ℝ (rsPartial J h) (θ • u))
        (volume.restrict (Icc (0 : ℝ) 1)) := by
      have hc : Continuous (fun θ : ℝ => (θ ^ (k + J.length + 1)) • fderiv ℝ (rsPartial J h) (θ • u)) :=
        (continuous_id.pow _).smul
          (((hJ.continuous_fderiv (by simp))).comp (continuous_id.smul continuous_const))
      exact hc.integrableOn_Icc
    rw [ContinuousLinearMap.integral_apply hint]
    simp only [smul_apply, smul_eq_mul, List.length_cons]
    congr 1


/-- A vanishing jet of `h` at zero gives a vanishing jet of its ray integral. -/
theorem rsPartial_scaledIntegral_eq_zero (h : (Fin N → ℝ) → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (J : List (Fin N)) (hJ : rsPartial J h 0 = 0) :
    rsPartial J (fun y : Fin N → ℝ => ∫ θ in Icc (0 : ℝ) 1, h (θ • y)) 0 = 0 := by
  have := congrFun (rsPartial_scaledIntegral h hh J 0) 0
  simp only [pow_zero, one_mul] at this
  rw [this]
  simp [hJ]

/-- Hadamard decomposition `F(η,u) - F(η,0) = ∑ⱼ uⱼ Fⱼ(η,u)` along rays. -/
theorem hadamard_decomp_param (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (η u : Fin N → ℝ) :
    F (η, u) - F (η, 0) = ∑ j, u j * ∫ θ in Icc (0 : ℝ) 1,
      fderiv ℝ F (η, θ • u) (0, Pi.single j 1) := by
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun θ : ℝ => F (η, θ • u))
      (fderiv ℝ F (η, θ • u) (0, u)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => ((η, θ • u) : (Fin N → ℝ) × (Fin N → ℝ))) ((0, u)) θ := by
      refine (hasDerivAt_const θ η).prodMk ?_
      simpa using (hasDerivAt_id θ).smul_const u
    exact (hFd (η, θ • u)).hasFDerivAt.comp_hasDerivAt θ h1
  have hc : Continuous (fun θ : ℝ => fderiv ℝ F (η, θ • u) (0, u)) :=
    ((hF.continuous_fderiv (by simp)).comp (continuous_const.prodMk (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hc.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul] at hftc
  rw [← hftc, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  have hsum : ∀ θ : ℝ, fderiv ℝ F (η, θ • u) (0, u) =
      ∑ j, u j * fderiv ℝ F (η, θ • u) (0, Pi.single j 1) := by
    intro θ
    have : ((0 : Fin N → ℝ), u) = ∑ j, u j • ((0 : Fin N → ℝ), (Pi.single j (1 : ℝ) : Fin N → ℝ)) := by
      ext i
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this, map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [map_smul, smul_eq_mul])
  simp_rw [hsum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_const_mul]
  · intro j _
    exact (continuous_const.mul (((hF.continuous_fderiv (by simp)).comp
      (continuous_const.prodMk (continuous_id.smul continuous_const))).clm_apply
        continuous_const)).integrableOn_Icc


/-- The coordinate partial of a parametrized function is the partial derivative. -/
theorem rsPartial_single_eq (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (η y : Fin N → ℝ) (j : Fin N) :
    rsPartial [j] (fun u => F (η, u)) y = fderiv ℝ F (η, y) (0, Pi.single j 1) := by
  have h1 : HasFDerivAt (fun u : Fin N → ℝ => F (η, u))
      ((fderiv ℝ F (η, y)).comp (ContinuousLinearMap.inr ℝ (Fin N → ℝ) (Fin N → ℝ))) y :=
    ((hF.differentiable (by simp)) (η, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right η y)
  show fderiv ℝ (fun u : Fin N → ℝ => F (η, u)) y (Pi.single j 1) = _
  rw [h1.fderiv]
  simp

/-- The Hadamard factors of a smooth parametrized function are smooth. -/
theorem hadamardFactor_param_contDiff (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (j : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      ∫ θ in Icc (0 : ℝ) 1, fderiv ℝ F (p.1, θ • p.2) (0, Pi.single j 1)) := by
  apply RothschildStein.G1.compactParameterIntegral_contDiff
    (fun q : ((Fin N → ℝ) × (Fin N → ℝ)) × ℝ => fderiv ℝ F (q.1.1, q.2 • q.1.2) (0, Pi.single j 1))
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := (contDiff_infty_iff_fderiv.mp hF).2
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun q : ((Fin N → ℝ) × (Fin N → ℝ)) × ℝ =>
      (q.1.1, q.2 • q.1.2)) :=
    contDiff_fst.fst.prodMk (contDiff_snd.smul contDiff_fst.snd)
  exact (hD.comp harg).clm_apply contDiff_const

/-- Weighted Taylor bound with vanishing weighted jets: if the weighted jets of a smooth
`F(η, ·)` of order `< b` vanish at `0` for `η` in a compact set, then `|F(η,u)| ≤ C ‖u‖^b` for
`‖u‖ ≤ 1` (BB p. 548, Lemma 11.16 and Remark 11.17). -/
theorem weighted_taylor_global (G : HomogeneousGroup N) :
    ∀ (b : ℕ) (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
    ∀ K : Set (Fin N → ℝ), IsCompact K →
    (∀ η ∈ K, ∀ J : List (Fin N), (J.map G.weight).sum < b →
        rsPartial J (fun u => F (η, u)) 0 = 0) →
    ∃ C : ℝ, ∀ η ∈ K, ∀ u : Fin N → ℝ, kgauge G u ≤ 1 →
      |F (η, u)| ≤ C * kgauge G u ^ b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro F hF K hK hjet
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have hcomp : IsCompact (K ×ˢ {u : Fin N → ℝ | kgauge G u ≤ 1}) :=
        hK.prod (G2.isCompact_gauge_le (G2.isHomogeneousGauge_max G) 1)
      obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hF.continuous.continuousOn
      exact ⟨C, fun η hη u hu => by simpa using hC (η, u) ⟨hη, hu⟩⟩
    · set Fj : Fin N → (Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun j p =>
        ∫ θ in Icc (0 : ℝ) 1, fderiv ℝ F (p.1, θ • p.2) (0, Pi.single j 1) with hFj
      have hjets : ∀ j : Fin N, ∀ η ∈ K, ∀ J : List (Fin N),
          (J.map G.weight).sum < b - G.weight j →
          rsPartial J (fun u => Fj j (η, u)) 0 = 0 := by
        intro j η hη J hJ
        have hg : ContDiff ℝ (⊤ : ℕ∞) (fun u : Fin N → ℝ => F (η, u)) :=
          hF.comp (contDiff_const.prodMk contDiff_id)
        have heq : (fun u => Fj j (η, u)) = fun y : Fin N → ℝ => ∫ θ in Icc (0 : ℝ) 1,
            rsPartial [j] (fun u => F (η, u)) (θ • y) := by
          funext y
          simp only [hFj]
          refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
          exact (rsPartial_single_eq F hF η _ j).symm
        rw [heq]
        apply rsPartial_scaledIntegral_eq_zero _ (rsPartial_contDiff [j] hg)
        rw [rsPartial_append_single]
        apply hjet η hη
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero]
        omega
      have hC := fun j : Fin N => ih (b - G.weight j)
        (by have := G.weight_pos j; omega) (Fj j) (hadamardFactor_param_contDiff F hF j) K hK
        (hjets j)
      choose C hC using hC
      refine ⟨∑ j, |C j|, fun η hη u hu => ?_⟩
      have hF0 : F (η, 0) = 0 := by
        have := hjet η hη [] (by simpa using hb)
        simpa [rsPartial] using this
      have hdec := hadamard_decomp_param F hF η u
      rw [hF0, sub_zero] at hdec
      have hρ0 : 0 ≤ kgauge G u := kgauge_nonneg G u
      rw [hdec, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
      have h1 := hC j η hη u hu
      rw [abs_mul]
      have h2 : |u j| ≤ kgauge G u ^ G.weight j := abs_apply_le_kgauge_pow G u j
      have h3 : |Fj j (η, u)| ≤ |C j| * kgauge G u ^ (b - G.weight j) :=
        h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hρ0 _))
      calc |u j| * |Fj j (η, u)| ≤ kgauge G u ^ G.weight j * (|C j| * kgauge G u ^ (b - G.weight j)) :=
            mul_le_mul h2 h3 (abs_nonneg _) (pow_nonneg hρ0 _)
        _ = |C j| * kgauge G u ^ (G.weight j + (b - G.weight j)) := by rw [pow_add]; ring
        _ ≤ |C j| * kgauge G u ^ b :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hu (by omega)) (abs_nonneg _)


/-- Iterated partials only depend on the germ of the function. -/
theorem rsPartial_eventuallyEq (J : List (Fin N)) {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (h : f =ᶠ[𝓝 x] g) : rsPartial J f =ᶠ[𝓝 x] rsPartial J g := by
  induction J with
  | nil => exact h
  | cons a J ih =>
    show (fun u => fderiv ℝ (rsPartial J f) u (Pi.single a 1)) =ᶠ[𝓝 x]
      fun u => fderiv ℝ (rsPartial J g) u (Pi.single a 1)
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with u hu
    simp only [hu]


/-- A function smooth on an open set containing `K × {0}` agrees near `K × {0}` with a
globally smooth function. -/
theorem exists_global_extension_param (T : Set ((Fin N → ℝ) × (Fin N → ℝ))) (hT : IsOpen T)
    (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F T)
    (K : Set (Fin N → ℝ)) (hK : IsCompact K) (hKT : ∀ η ∈ K, (η, (0 : Fin N → ℝ)) ∈ T) :
    ∃ F' : (Fin N → ℝ) × (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) F' ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ η ∈ K, ∀ u : Fin N → ℝ, ‖u‖ ≤ ε → F' (η, u) = F (η, u) := by
  set S : Set ((Fin N → ℝ) × (Fin N → ℝ)) := (fun η => (η, (0 : Fin N → ℝ))) '' K with hS
  have hSc : IsCompact S := hK.image (continuous_id.prodMk continuous_const)
  have hST : S ⊆ T := by
    rintro _ ⟨η, hη, rfl⟩
    exact hKT η hη
  obtain ⟨Δ, hΔ, hΔT⟩ := hSc.exists_cthickening_subset_open hT hST
  obtain ⟨f, hf, -, hf0, hf1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞))
    (s := (Metric.thickening Δ S)ᶜ) (t := Metric.cthickening (Δ / 2) S)
    Metric.isOpen_thickening.isClosed_compl Metric.isClosed_cthickening (by
      rw [Set.disjoint_compl_left_iff_subset]
      exact Metric.cthickening_subset_thickening' hΔ (by linarith) S)
  refine ⟨fun p => f p * F p, ?_, Δ / 2, by linarith, ?_⟩
  · have hsupp : tsupport f ⊆ T := by
      have h1 : Function.support f ⊆ Metric.thickening Δ S := by
        intro p hp
        by_contra hnp
        exact hp ((hf0 p).mp hnp)
      exact (closure_mono h1).trans ((Metric.closure_thickening_subset_cthickening Δ S).trans hΔT)
    exact RothschildStein.G1.cutoff_smul_contDiff hT F hF f hf hsupp
  · intro η hη u hu
    have hmem : (η, u) ∈ Metric.cthickening (Δ / 2) S := by
      refine Metric.mem_cthickening_of_dist_le (η, u) (η, (0 : Fin N → ℝ)) (Δ / 2) S
        ⟨η, hη, rfl⟩ ?_
      simpa [Prod.dist_eq, dist_eq_norm] using hu
    simp only [(hf1 _).mp hmem, one_mul]


/-- The sup norm is bounded by the max gauge when the gauge is at most one. -/
theorem norm_le_kgauge (G : HomogeneousGroup N) {u : Fin N → ℝ} (hu : kgauge G u ≤ 1) :
    ‖u‖ ≤ kgauge G u := by
  refine (pi_norm_le_iff_of_nonneg (kgauge_nonneg G u)).mpr (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_apply_le_kgauge_pow G u j).trans
    (pow_le_of_le_one (kgauge_nonneg G u) hu (ne_of_gt (G.weight_pos j)))

/-- Localized weighted Taylor bound for a function smooth only on an open set `T`
containing `K × {0}` (BB p. 548, Lemma 11.16). -/
theorem weighted_taylor_local (G : HomogeneousGroup N) (T : Set ((Fin N → ℝ) × (Fin N → ℝ)))
    (hT : IsOpen T) (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F T)
    (K : Set (Fin N → ℝ)) (hK : IsCompact K) (hKT : ∀ η ∈ K, (η, (0 : Fin N → ℝ)) ∈ T) (b : ℕ)
    (hjet : ∀ η ∈ K, ∀ J : List (Fin N), (J.map G.weight).sum < b →
      rsPartial J (fun u => F (η, u)) 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ C : ℝ, ∀ η ∈ K, ∀ u : Fin N → ℝ, kgauge G u ≤ r →
      |F (η, u)| ≤ C * kgauge G u ^ b := by
  obtain ⟨F', hF', ε, hε, hagree⟩ := exists_global_extension_param T hT F hF K hK hKT
  have hjet' : ∀ η ∈ K, ∀ J : List (Fin N), (J.map G.weight).sum < b →
      rsPartial J (fun u => F' (η, u)) 0 = 0 := by
    intro η hη J hJ
    have hev : (fun u => F' (η, u)) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun u => F (η, u) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Fin N → ℝ) hε] with u hu
      exact hagree η hη u (mem_ball_zero_iff.mp hu).le
    rw [(rsPartial_eventuallyEq J hev).eq_of_nhds]
    exact hjet η hη J hJ
  obtain ⟨C, hC⟩ := weighted_taylor_global G b F' hF' K hK hjet'
  refine ⟨min 1 ε, lt_min one_pos hε, min_le_left _ _, C, fun η hη u hu => ?_⟩
  have hρ : kgauge G u ≤ 1 := hu.trans (min_le_left _ _)
  have hnorm : ‖u‖ ≤ ε := (norm_le_kgauge G hρ).trans (hu.trans (min_le_right _ _))
  rw [← hagree η hη u hnorm]
  exact hC η hη u hρ

end RothschildStein.P1
