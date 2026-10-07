-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuitySingularHolder
public import RothschildStein.H2.DataDLpPair
public import RothschildStein.H2.UniformRealVolume
public import RothschildStein.H2.PrincipalValueCongruence

/-!
# The a priori `L^p` bound of the near part

For one principal term of degree `2` and `1 < p < ∞`, the near part `a(ξ) K^φ(ξ, η) b(η)` has, on
every input `f` of finite Hölder norm on `V` (for some `0 < α < 1`),
`‖T_near f‖_{L^p(V)} ≤ Λ ‖f‖_{L^p(V)}` (`exists_nearOutput_lp_bound`).

H2's `L^p` bound for singular integrals on each doubled ball (`H2.TransposeData.exists_lpPair`, with the actual pair of local
extensions `(T_j, T_j^t)` of the Data D and its separate transpose certificate) gives
`‖T_j g‖_{L^p(B_j)} ≤ Λ_j ‖g‖_{L^p(B_j)}` on bounded Hölder `g`
(`principalValue_memLp_eLpNorm_le`); the local outputs vanish outside `B(z_j, r/4)` and are extended
by zero; `‖b f‖_{L^p} ≤ ‖b‖_∞ ‖f‖_{L^p(V)}`; the finite sum and the multiplier `a` are bounded
by `‖a‖_∞ ∑_j Λ_j`. All norms of the carrier are transferred to the ambient space
(`Carrier.eLpNorm_comp_val`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology
namespace RothschildStein.P1

section Piece

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {D : H2.LocDoubling X} {d : H2.TruncDist D}

/-- **The actual local principal value is bounded on `L^p` of its
ball** by the constant of H2's `L^p` bound for the pair of local extensions: for `g` bounded Hölder on the ball,
`T g` is in `L^p(B)` and `‖T g‖_{L^p(B)} ≤ Λ ‖g‖_{L^p(B)}`. -/
theorem principalValue_memLp_eLpNorm_le {Q : H2.LocalKernelData D d} {P : H2.TransposeData Q}
    {δ : ℝ≥0} {hδ : 0 < δ} {hδ₀ : (δ : ℝ) < Q.β₀} {hδβ : (δ : ℝ) < Q.β}
    {hδν : (δ : ℝ) < Q.ν} {hδ₀' : (δ : ℝ) < P.data.β₀} {hδβ' : (δ : ℝ) < P.data.β}
    {hδν' : (δ : ℝ) < P.data.ν} {m p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal (Real.conjExponent p))]
    (L : H2.DataDLpPair P hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' m p) {g : X → ℝ}
    (hg : H2.BoundedHolder δ (ball Q.z Q.R) g) :
    MemLp (Q.principalValue g) (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R)) ∧
      eLpNorm (Q.principalValue g) (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R)) ≤
        ENNReal.ofReal (P.lpConstant δ m p) *
          eLpNorm g (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R)) := by
  have hU : MeasurableSet (ball Q.z Q.R) := isOpen_ball.measurableSet
  have hμU : D.μ (ball Q.z Q.R) < ⊤ := Q.measure_ball_lt_top
  have hfmem := (H2.holderNormalize hg).property.1.memLp hδ hU hμU (ENNReal.ofReal p)
  have hae := L.apply_principalValue (H2.holderNormalize hg)
  have hcongr : Q.principalValue (H2.holderNormalize hg : X → ℝ) =ᵐ[D.μ.restrict (ball Q.z Q.R)]
      Q.principalValue g := by
    filter_upwards [ae_restrict_mem hU] with x hx
    exact Q.principalValue_congr (fun y hy => indicator_of_mem hy g) hx
  have hpv := hae.trans hcongr
  have hmem : MemLp (Q.principalValue g) (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R)) :=
    (Lp.memLp _).ae_eq hpv
  refine ⟨hmem, ?_⟩
  have hΛ : 0 ≤ P.lpConstant δ m p := (norm_nonneg _).trans L.norm_le
  set v := H2.holderLp δ (ball Q.z Q.R) D.μ hδ hU hμU (ENNReal.ofReal p)
    (H2.holderNormalize hg) with hv
  have hvnorm : ‖v‖ = (eLpNorm ((H2.holderNormalize hg : H2.holderFunctions δ (ball Q.z Q.R)) :
      X → ℝ) (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R))).toReal :=
    Lp.norm_toLp _ hfmem
  have hf'g : eLpNorm ((H2.holderNormalize hg : H2.holderFunctions δ (ball Q.z Q.R)) :
      X → ℝ) (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R)) =
        eLpNorm g (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R)) :=
    eLpNorm_congr_ae (by
      filter_upwards [ae_restrict_mem hU] with x hx
      exact indicator_of_mem hx g)
  calc eLpNorm (Q.principalValue g) (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R))
      = eLpNorm (L.operator v) (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R)) :=
        (eLpNorm_congr_ae hpv).symm
    _ = ENNReal.ofReal ‖L.operator v‖ := by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp _).eLpNorm_ne_top]
    _ ≤ ENNReal.ofReal (P.lpConstant δ m p * ‖v‖) :=
        ENNReal.ofReal_le_ofReal ((L.operator.le_opNorm v).trans
          (mul_le_mul_of_nonneg_right L.norm_le (norm_nonneg v)))
    _ = ENNReal.ofReal (P.lpConstant δ m p) * ENNReal.ofReal ‖v‖ := ENNReal.ofReal_mul hΛ
    _ = ENNReal.ofReal (P.lpConstant δ m p) *
        eLpNorm g (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R)) := by
        rw [hvnorm, ENNReal.ofReal_toReal hfmem.eLpNorm_ne_top, hf'g]

end Piece

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}
variable {ν : (Fin (n + m) → ℝ) → ℝ} {Fs V : Set (Fin (n + m) → ℝ)}
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
  {Γ : (Fin (n + m) → ℝ) → ℝ} {cert : C.NearCertificate ν Fs}
  {a b : (Fin (n + m) → ℝ) → ℝ}

/-- The near output at a point of the carrier. -/
theorem nearOutput_comp_val (dd : C.NearDataD cert D Γ) (a b f : (Fin (n + m) → ℝ) → ℝ)
    (y : C.Carrier) :
    nearOutput dd a b f y.val =
      a y.val * ∑ z : cert.t, (dd.Q z).principalValue (C.inputCarrier b f) y := by
  simp only [nearOutput, y.val_mem, ↓reduceDIte, Carrier.mk_val]

/-- **Zero extension of the local outputs**: the principal
value of a localized operator vanishes outside its ball. -/
theorem principalValue_eq_zero_of_not_mem_ball (dd : C.NearDataD cert D Γ) (z : cert.t)
    (g : C.Carrier → ℝ) {y : C.Carrier} (hy : y ∉ ball z.1 cert.r) :
    (dd.Q z).principalValue g y = 0 := by
  apply H2.LocalKernelData.principalValue_zero_of_cutoff
  apply (dd.Q z).cutoff_a.outside
  rwa [Q_ball_eq dd z]

/-- **The a priori `L^p` bound of the near part** (H2's singular integral `L^p` bound per
doubled ball, the finite reconstruction formula, finite sum). For `1 < p < ∞` and `0 < α < 1` there is `Λ`
with `‖T_near f‖_{L^p(V)} ≤ Λ ‖f‖_{L^p(V)}` for every measurable `f` of finite Hölder norm on `V`
(and `T_near f ∈ L^p(V)`). -/
theorem exists_nearOutput_lp_bound (dd : C.NearDataD cert D Γ) (hc : C.IsTermCutoffs V Fs a b)
    {p : ℝ} (hp : 1 < p) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ f : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α V f ≠ ⊤ →
      AEStronglyMeasurable f (volume.restrict V) →
      MemLp (nearOutput dd a b f) (ENNReal.ofReal p) (volume.restrict V) ∧
        eLpNorm (nearOutput dd a b f) (ENNReal.ofReal p) (volume.restrict V) ≤
          ENNReal.ofReal Λ * eLpNorm f (ENNReal.ofReal p) (volume.restrict V) := by
  classical
  have hμ : cert.S.μ = volume := cert.hS.μ_eq
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ≥0, δ = α.toNNReal := ⟨_, rfl⟩
  have hδα : (δ : ℝ) = α := by rw [hδdef]; exact Real.coe_toNNReal _ hα0.le
  have hδ : 0 < δ := by rw [← NNReal.coe_pos, hδα]; exact hα0
  have hF1 : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hF2 : Fact (1 ≤ ENNReal.ofReal (Real.conjExponent p)) :=
    ⟨ENNReal.one_le_ofReal.mpr (Real.HolderConjugate.conjExponent hp).symm.lt.le⟩
  obtain ⟨K, hK, hKb⟩ := exists_boundedHolder_mul_extension (C := C) hc.open_V hc.V_sub
    hc.b_smooth hc.b_compact hc.b_support hα0 hα1.le
  rw [← hδdef] at hKb
  obtain ⟨Mb, hMb⟩ := hc.b_smooth.continuous.bounded_above_of_compact_support hc.b_compact
  obtain ⟨Ma, hMa⟩ := hc.a_smooth.continuous.bounded_above_of_compact_support hc.a_compact
  have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans (hMb 0)
  have hMa0 : 0 ≤ Ma := (norm_nonneg _).trans (hMa 0)
  have hδ₀ : ∀ z : cert.t, (δ : ℝ) < (dd.Q z).β₀ := fun z => by
    rw [(dd.split z).β₀_eq, hδα]; exact hα1
  have hδβ : ∀ z : cert.t, (δ : ℝ) < (dd.Q z).β := fun z => by
    rw [(dd.split z).β_eq, hδα]; exact hα1
  have hδν : ∀ z : cert.t, (δ : ℝ) < (dd.Q z).ν := fun z => by
    rw [(dd.split z).ν_eq, hδα]; exact hα1
  have hδ₀' : ∀ z : cert.t, (δ : ℝ) < (dd.P z).data.β₀ := fun z => by
    rw [(dd.P_exponents z).1, hδα]; exact hα1
  have hδβ' : ∀ z : cert.t, (δ : ℝ) < (dd.P z).data.β := fun z => by
    rw [(dd.P_exponents z).2.1, hδα]; exact hα1
  have hδν' : ∀ z : cert.t, (δ : ℝ) < (dd.P z).data.ν := fun z => by
    rw [(dd.P_exponents z).2.2, hδα]; exact hα1
  obtain ⟨m0, hm0, hml⟩ := cert.S.exists_uniform_real_volume
  have hL : ∀ z : cert.t, H2.DataDLpPair (dd.P z) hδ (hδ₀ z) (hδβ z) (hδν z) (hδ₀' z) (hδβ' z)
      (hδν' z) m0 p := fun z =>
    Classical.choice ((dd.P z).exists_lpPair hδ (hδ₀ z) (hδβ z) (hδν z) (hδ₀' z) (hδβ' z)
      (hδν' z) hm0 hml hp)
  obtain ⟨Λz, hΛz⟩ : ∃ Λz : cert.t → ℝ, Λz = fun z => (dd.P z).lpConstant δ m0 p := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ≥0∞, E = ENNReal.ofReal Ma * (∑ z, ENNReal.ofReal (Λz z)) *
      ENNReal.ofReal Mb := ⟨_, rfl⟩
  have hEtop : E ≠ ⊤ := by
    rw [hE]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.sum_ne_top.mpr fun z _ => ENNReal.ofReal_ne_top)) ENNReal.ofReal_ne_top
  have hVm : MeasurableSet V := hc.open_V.measurableSet
  have hV'm : MeasurableSet (Carrier.val ⁻¹' V : Set C.Carrier) :=
    hc.open_V.preimage Carrier.continuous_val |>.measurableSet
  have hfinite : IsFiniteMeasure (volume.restrict V) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono (hc.V_sub.trans subset_closure))
        C.isCompact_closure_U.measure_lt_top⟩
  refine ⟨E.toReal + 1, by positivity, fun f hf hfm => ?_⟩
  -- Hölder control of the input
  have hgU : H2.BoundedHolder δ univ (C.inputCarrier b f) :=
    (hKb f).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hf))
  have hgz : ∀ z : cert.t, H2.BoundedHolder δ (ball z.1 cert.r) (C.inputCarrier b f) :=
    fun z => (H2.boundedHolderNorm_restrict (subset_univ _)).trans_lt hgU
  -- (1) the input
  have hfm' : AEStronglyMeasurable (fun y : C.Carrier => f y.val)
      ((volume : Measure C.Carrier).restrict (Carrier.val ⁻¹' V)) :=
    (Carrier.aestronglyMeasurable_comp_val_iff f hVm hc.V_sub).mpr hfm
  have hgm : AEStronglyMeasurable (C.inputCarrier b f) (volume : Measure C.Carrier) := by
    have h1 : AEStronglyMeasurable (fun y : C.Carrier => b y.val * f y.val)
        ((volume : Measure C.Carrier).restrict (Carrier.val ⁻¹' V)) :=
      ((hc.b_smooth.continuous.comp Carrier.continuous_val).aestronglyMeasurable).mul hfm'
    have h2 := (aestronglyMeasurable_indicator_iff (μ := (volume : Measure C.Carrier)) hV'm).mpr h1
    have h3 : (Carrier.val ⁻¹' V : Set C.Carrier).indicator (fun y : C.Carrier => b y.val * f y.val) =
        C.inputCarrier b f := by
      funext y
      by_cases hy : y.val ∈ V
      · rw [indicator_of_mem (show y ∈ Carrier.val ⁻¹' V from hy)]; rfl
      · have hb0 : b y.val = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hc.b_support h))
        rw [indicator_of_notMem (show y ∉ Carrier.val ⁻¹' V from hy)]
        simp [inputCarrier, hb0]
    rwa [h3] at h2
  have hin : eLpNorm (C.inputCarrier b f) (ENNReal.ofReal p) (volume : Measure C.Carrier) ≤
      ENNReal.ofReal Mb * eLpNorm f (ENNReal.ofReal p) (volume.restrict V) := by
    calc eLpNorm (C.inputCarrier b f) (ENNReal.ofReal p) (volume : Measure C.Carrier)
        ≤ eLpNorm ((Carrier.val ⁻¹' V : Set C.Carrier).indicator
            (fun y : C.Carrier => Mb • f y.val)) (ENNReal.ofReal p) volume := by
          refine eLpNorm_mono_ae hgm (ae_of_all _ fun y => ?_)
          by_cases hy : y.val ∈ V
          · rw [indicator_of_mem (show y ∈ Carrier.val ⁻¹' V from hy)]
            simp only [inputCarrier, Real.norm_eq_abs, smul_eq_mul, abs_mul, abs_of_nonneg hMb0]
            exact mul_le_mul_of_nonneg_right (by simpa using hMb y.val) (abs_nonneg _)
          · have hb0 : b y.val = 0 :=
              image_eq_zero_of_notMem_tsupport (fun h => hy (hc.b_support h))
            simp [inputCarrier, hb0]
      _ = eLpNorm (fun y : C.Carrier => Mb • f y.val) (ENNReal.ofReal p)
            ((volume : Measure C.Carrier).restrict (Carrier.val ⁻¹' V)) :=
          eLpNorm_indicator_eq_eLpNorm_restrict hV'm
      _ = ENNReal.ofReal Mb * eLpNorm (fun y : C.Carrier => f y.val) (ENNReal.ofReal p)
            ((volume : Measure C.Carrier).restrict (Carrier.val ⁻¹' V)) := by
          rw [show (fun y : C.Carrier => Mb • f y.val) = Mb • (fun y : C.Carrier => f y.val)
            from rfl, eLpNorm_const_smul, Real.enorm_eq_ofReal hMb0]
      _ = ENNReal.ofReal Mb * eLpNorm f (ENNReal.ofReal p) (volume.restrict V) := by
          rw [Carrier.eLpNorm_comp_val f _ hVm hc.V_sub]
  -- (2) the local pieces
  have hpiece_mem : ∀ z : cert.t,
      MemLp ((dd.Q z).principalValue (C.inputCarrier b f)) (ENNReal.ofReal p)
          (volume.restrict (ball z.1 cert.r)) ∧
        eLpNorm ((dd.Q z).principalValue (C.inputCarrier b f)) (ENNReal.ofReal p)
            (volume.restrict (ball z.1 cert.r)) ≤
          ENNReal.ofReal (Λz z) * eLpNorm (C.inputCarrier b f) (ENNReal.ofReal p)
            (volume.restrict (ball z.1 cert.r)) := fun z => by
    have h := principalValue_memLp_eLpNorm_le (hL z) (boundedHolder_Q_ball dd hgz z)
    rw [hμ, Q_ball_eq dd z] at h
    rw [hΛz]
    exact h
  have hpiece_ind : ∀ z : cert.t, ∀ y : C.Carrier,
      (ball z.1 cert.r).indicator ((dd.Q z).principalValue (C.inputCarrier b f)) y =
        (dd.Q z).principalValue (C.inputCarrier b f) y := fun z y => by
    by_cases hy : y ∈ ball z.1 cert.r
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, principalValue_eq_zero_of_not_mem_ball dd z _ hy]
  have hasm : ∀ z : cert.t, AEStronglyMeasurable
      ((dd.Q z).principalValue (C.inputCarrier b f)) (volume : Measure C.Carrier) := fun z => by
    have h1 := (aestronglyMeasurable_indicator_iff (μ := (volume : Measure C.Carrier))
      (isOpen_ball (x := z.1) (ε := cert.r)).measurableSet).mpr (hpiece_mem z).1.aestronglyMeasurable
    have h2 : (ball z.1 cert.r).indicator ((dd.Q z).principalValue (C.inputCarrier b f)) =
        (dd.Q z).principalValue (C.inputCarrier b f) := funext (hpiece_ind z)
    rwa [h2] at h1
  have hpiece : ∀ z : cert.t, eLpNorm ((dd.Q z).principalValue (C.inputCarrier b f))
      (ENNReal.ofReal p) (volume : Measure C.Carrier) ≤ ENNReal.ofReal (Λz z) *
        eLpNorm (C.inputCarrier b f) (ENNReal.ofReal p) (volume : Measure C.Carrier) :=
    fun z => by
    calc eLpNorm ((dd.Q z).principalValue (C.inputCarrier b f)) (ENNReal.ofReal p) volume
        = eLpNorm ((ball z.1 cert.r).indicator ((dd.Q z).principalValue (C.inputCarrier b f)))
            (ENNReal.ofReal p) volume := by rw [funext (hpiece_ind z)]
      _ = eLpNorm ((dd.Q z).principalValue (C.inputCarrier b f)) (ENNReal.ofReal p)
            (volume.restrict (ball z.1 cert.r)) :=
          eLpNorm_indicator_eq_eLpNorm_restrict isOpen_ball.measurableSet
      _ ≤ ENNReal.ofReal (Λz z) * eLpNorm (C.inputCarrier b f) (ENNReal.ofReal p)
            (volume.restrict (ball z.1 cert.r)) := (hpiece_mem z).2
      _ ≤ ENNReal.ofReal (Λz z) * eLpNorm (C.inputCarrier b f) (ENNReal.ofReal p) volume := by
          gcongr
          exact Measure.restrict_le_self
  -- (3) the sum and the multiplier
  have hsum : eLpNorm (fun y : C.Carrier => ∑ z : cert.t,
      (dd.Q z).principalValue (C.inputCarrier b f) y) (ENNReal.ofReal p) volume ≤
        ∑ z : cert.t, eLpNorm ((dd.Q z).principalValue (C.inputCarrier b f))
          (ENNReal.ofReal p) volume := by
    have h := eLpNorm_sum_le (μ := (volume : Measure C.Carrier)) (p := ENNReal.ofReal p)
      (s := (Finset.univ : Finset cert.t))
      (f := fun z => (dd.Q z).principalValue (C.inputCarrier b f)) hF1.out
    rwa [Finset.sum_fn] at h
  have hOm : AEStronglyMeasurable (fun y : C.Carrier => nearOutput dd a b f y.val)
      (volume : Measure C.Carrier) := by
    have : (fun y : C.Carrier => nearOutput dd a b f y.val) = fun y => a y.val *
        ∑ z : cert.t, (dd.Q z).principalValue (C.inputCarrier b f) y :=
      funext (nearOutput_comp_val dd a b f)
    rw [this]
    have hsm := Finset.aestronglyMeasurable_sum (Finset.univ : Finset cert.t) (fun z _ => hasm z)
    rw [Finset.sum_fn] at hsm
    exact ((hc.a_smooth.continuous.comp Carrier.continuous_val).aestronglyMeasurable).mul hsm
  have hmain : eLpNorm (nearOutput dd a b f) (ENNReal.ofReal p) (volume.restrict V) ≤
      E * eLpNorm f (ENNReal.ofReal p) (volume.restrict V) := by
    calc eLpNorm (nearOutput dd a b f) (ENNReal.ofReal p) (volume.restrict V)
        = eLpNorm (fun y : C.Carrier => nearOutput dd a b f y.val) (ENNReal.ofReal p)
            ((volume : Measure C.Carrier).restrict (Carrier.val ⁻¹' V)) :=
          (Carrier.eLpNorm_comp_val _ _ hVm hc.V_sub).symm
      _ ≤ eLpNorm (fun y : C.Carrier => nearOutput dd a b f y.val) (ENNReal.ofReal p) volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ eLpNorm (fun y : C.Carrier => Ma • ∑ z : cert.t,
            (dd.Q z).principalValue (C.inputCarrier b f) y) (ENNReal.ofReal p) volume := by
          refine eLpNorm_mono_ae hOm (ae_of_all _ fun y => ?_)
          rw [nearOutput_comp_val]
          simp only [Real.norm_eq_abs, smul_eq_mul, abs_mul, abs_of_nonneg hMa0]
          exact mul_le_mul_of_nonneg_right (by simpa using hMa y.val) (abs_nonneg _)
      _ = ENNReal.ofReal Ma * eLpNorm (fun y : C.Carrier => ∑ z : cert.t,
            (dd.Q z).principalValue (C.inputCarrier b f) y) (ENNReal.ofReal p) volume := by
          rw [show (fun y : C.Carrier => Ma • ∑ z : cert.t,
              (dd.Q z).principalValue (C.inputCarrier b f) y) = Ma • (fun y : C.Carrier =>
              ∑ z : cert.t, (dd.Q z).principalValue (C.inputCarrier b f) y) from rfl,
            eLpNorm_const_smul, Real.enorm_eq_ofReal hMa0]
      _ ≤ ENNReal.ofReal Ma * ∑ z : cert.t, (ENNReal.ofReal (Λz z) *
            eLpNorm (C.inputCarrier b f) (ENNReal.ofReal p) (volume : Measure C.Carrier)) := by
          gcongr
          exact hsum.trans (Finset.sum_le_sum fun z _ => hpiece z)
      _ ≤ ENNReal.ofReal Ma * ∑ z : cert.t, (ENNReal.ofReal (Λz z) *
            (ENNReal.ofReal Mb * eLpNorm f (ENNReal.ofReal p) (volume.restrict V))) := by
          gcongr
      _ = E * eLpNorm f (ENNReal.ofReal p) (volume.restrict V) := by
          rw [hE, ← Finset.sum_mul]
          ring
  have hfmem : MemLp f (ENNReal.ofReal p) (volume.restrict V) := by
    refine MemLp.of_bound hfm (holderENorm C.dl α V f).toReal
      (ae_restrict_of_forall_mem hVm fun x hx => ?_)
    rw [Real.norm_eq_abs]
    exact (ENNReal.ofReal_le_iff_le_toReal hf).mp
      (le_trans (le_iSup (fun x : V => ENNReal.ofReal |f x|) ⟨x, hx⟩) le_self_add)
  have hle : E ≤ ENNReal.ofReal (E.toReal + 1) :=
    calc E = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hEtop).symm
      _ ≤ ENNReal.ofReal (E.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  have hbound : eLpNorm (nearOutput dd a b f) (ENNReal.ofReal p) (volume.restrict V) ≤
      ENNReal.ofReal (E.toReal + 1) * eLpNorm f (ENNReal.ofReal p) (volume.restrict V) :=
    hmain.trans (by gcongr)
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfmem.eLpNorm_lt_top),
    hbound⟩

end LiftedChart
end RothschildStein.P1
