-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.Cutoffs
public import Hormander.B.Defs
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Congr

@[expose] public section

noncomputable section

open Filter MeasureTheory Set SchwartzMap Topology
open Hormander.B
open scoped FourierTransform

namespace Hormander.D

/-- The localized Bessel operator `η' Λ^s η₁` on Schwartz functions. -/
def localizedBesselOperator {N : ℕ} (η₁ η' : SchwartzMap (Carrier N) ℝ) (s : ℝ) :
    Operator N :=
  (Hormander.B.realMultiplierOperator η').comp
    ((Hormander.B.lambdaOperator s).comp (Hormander.B.realMultiplierOperator η₁))

@[simp]
theorem realMultiplierOperator_apply {N : ℕ} (η : SchwartzMap (Carrier N) ℝ)
    (u : TestFunction N) (x : Carrier N) :
    realMultiplierOperator η u x = (η x : ℂ) * u x := by
  have hfun : (⇑(complexifyRealSchwartz η) : Carrier N → ℂ) =
      fun y ↦ (η y : ℂ) := by
    funext y
    rfl
  change (SchwartzMap.smulLeftCLM ℂ (complexifyRealSchwartz η) u) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (complexifyRealSchwartz η).hasTemperateGrowth]
  rw [hfun]
  simp only [smul_eq_mul]

theorem vectorFieldOperator_apply {N : ℕ}
    (V : RealSchwartzVectorField N) (u : TestFunction N) (x : Carrier N) :
    vectorFieldOperator V u x =
      ∑ i : Fin N, ((V i x : ℝ) : ℂ) *
        fderiv ℝ (u : Carrier N → ℂ) x (EuclideanSpace.single i (1 : ℝ)) := by
  simp [vectorFieldOperator, coordinateDerivative, LinearMap.sum_apply,
    LinearMap.comp_apply, SchwartzMap.lineDerivOpCLM_eq]

/-- A local differential operator preserves vanishing on an open set. -/
theorem vectorFieldOperator_eq_zero_on_open {N : ℕ}
    (V : RealSchwartzVectorField N) (u : TestFunction N)
    {W : Set (Carrier N)} (hW : IsOpen W)
    (hu : ∀ x ∈ W, u x = 0) {x : Carrier N} (hx : x ∈ W) :
    vectorFieldOperator V u x = 0 := by
  have hlocal : (u : Carrier N → ℂ) =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact hu y hy
  have hderiv : fderiv ℝ (u : Carrier N → ℂ) x = 0 := by
    simpa using hlocal.fderiv_eq
  rw [vectorFieldOperator_apply]
  simp [hderiv]

theorem cutoffPrecedes_eq_one_on_tsupport {N : ℕ} {η₁ η₂ : Carrier N → ℝ}
    (hη : cutoffPrecedes η₁ η₂) : tsupport η₁ ⊆ {x | η₂ x = 1} := by
  have hinterior : tsupport η₁ ⊆ interior {x | η₂ x = 1} :=
    (cutoffPrecedes_eventually_iff_interior η₁ η₂).mp hη.2.2.2.2
  exact fun x hx ↦ interior_subset (hinterior hx)

theorem cutoffPrecedes_mul_eq_self {N : ℕ} {η₁ η₂ : Carrier N → ℝ}
    (hη : cutoffPrecedes η₁ η₂) (x : Carrier N) : η₁ x * η₂ x = η₁ x := by
  by_cases hzero : η₁ x = 0
  · simp [hzero]
  · have hx : x ∈ tsupport η₁ := by
      apply subset_tsupport
      simpa using hzero
    rw [(cutoffPrecedes_eq_one_on_tsupport hη hx)]
    ring

/-- Multiplication by the inner cutoff kills every Schwartz function vanishing near its support. -/
theorem realMultiplierOperator_eq_zero_of_vanish {N : ℕ}
    {η : SchwartzMap (Carrier N) ℝ} {W : Set (Carrier N)}
    (hηW : tsupport η ⊆ W) (v : TestFunction N)
    (hv : ∀ x ∈ W, v x = 0) : realMultiplierOperator η v = 0 := by
  ext x
  rw [realMultiplierOperator_apply]
  by_cases hzero : η x = 0
  · simp [hzero]
  · have hx : x ∈ tsupport η := by
      apply subset_tsupport
      simpa using hzero
    simp [hv x (hηW hx)]

/-- The localized Bessel operator kills inputs whose inner-cutoff product vanishes. -/
theorem localizedBesselOperator_eq_zero_of_cutoff_eq_zero {N : ℕ}
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (s : ℝ) (v : TestFunction N)
    (hv : realMultiplierOperator η₁ v = 0) : localizedBesselOperator η₁ η' s v = 0 := by
  simp [localizedBesselOperator, LinearMap.comp_apply, hv]

/-- A nested input cutoff can be transferred to the outer data before applying the localized
Bessel operator. -/
theorem localizedBesselOperator_right_factorization {N : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (hη₁η₂ : cutoffPrecedes (η₁ : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    localizedBesselOperator η₁ η' s =
      (localizedBesselOperator η₁ η' s).comp (realMultiplierOperator η₂) := by
  have hmul (v : TestFunction N) :
      realMultiplierOperator η₁ (realMultiplierOperator η₂ v) =
      realMultiplierOperator η₁ v := by
    ext x
    simp only [realMultiplierOperator_apply]
    rw [← mul_assoc, ← Complex.ofReal_mul,
      cutoffPrecedes_mul_eq_self hη₁η₂ x]
  ext v
  simp only [localizedBesselOperator, LinearMap.comp_apply]
  rw [hmul]

theorem operator_eq_comp_of_killing_difference {N : ℕ}
    (O M : Operator N)
    (hkill : ∀ v, O (v - M v) = 0) :
    O = O.comp M := by
  apply LinearMap.ext
  intro v
  have hv := hkill v
  rw [map_sub] at hv
  exact sub_eq_zero.mp hv

theorem localizedBesselComm_eq_zero_of_vanish {N : ℕ}
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V : Fin N → SchwartzMap (Carrier N) ℝ) (v : TestFunction N)
    {W : Set (Carrier N)} (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆ W)
    (hW : IsOpen W) (hv : ∀ x ∈ W, v x = 0) :
    operatorComm (vectorFieldOperator V)
      (localizedBesselOperator η₁ η' s) v = 0 := by
  let X := vectorFieldOperator V
  let A := localizedBesselOperator η₁ η' s
  have hcut : realMultiplierOperator η₁ v = 0 :=
    realMultiplierOperator_eq_zero_of_vanish hη₁W v hv
  have hAv : A v = 0 :=
    localizedBesselOperator_eq_zero_of_cutoff_eq_zero η₁ η' s v hcut
  have hvX : ∀ x ∈ W, X v x = 0 := by
    intro x hx
    exact vectorFieldOperator_eq_zero_on_open V v hW hv hx
  have hcutX : realMultiplierOperator η₁ (X v) = 0 :=
    realMultiplierOperator_eq_zero_of_vanish hη₁W (X v) hvX
  have hAXv : A (X v) = 0 :=
    localizedBesselOperator_eq_zero_of_cutoff_eq_zero η₁ η' s (X v) hcutX
  simp [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply, X, A, hAv, hAXv]

theorem localizedBesselComm_eq_comp_of_cutoff {N : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V : Fin N → SchwartzMap (Carrier N) ℝ)
    (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆
      interior {x | η₂ x = 1}) :
    operatorComm (vectorFieldOperator V)
        (localizedBesselOperator η₁ η' s) =
      (operatorComm (vectorFieldOperator V)
        (localizedBesselOperator η₁ η' s)).comp (realMultiplierOperator η₂) := by
  apply operator_eq_comp_of_killing_difference
  intro v
  have hv : ∀ x ∈ interior {x | η₂ x = 1},
      (v - realMultiplierOperator η₂ v) x = 0 := by
    intro x hx
    have hsub : interior {y : Carrier N | η₂ y = 1} ⊆
        {y : Carrier N | η₂ y = 1} := interior_subset
    have hη₂ : η₂ x = 1 := hsub hx
    change v x - (realMultiplierOperator η₂ v) x = 0
    rw [realMultiplierOperator_apply, hη₂]
    simp
  exact localizedBesselComm_eq_zero_of_vanish η₁ η' s V
    (v - realMultiplierOperator η₂ v) hη₁W isOpen_interior hv

theorem nestedLocalizedBesselComm_eq_zero_of_vanish {N : ℕ}
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (Vᵢ Vⱼ : Fin N → SchwartzMap (Carrier N) ℝ) (v : TestFunction N)
    {W : Set (Carrier N)} (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆ W)
    (hW : IsOpen W) (hv : ∀ x ∈ W, v x = 0) :
    operatorComm
      (operatorComm (vectorFieldOperator Vᵢ)
        (localizedBesselOperator η₁ η' s))
      (vectorFieldOperator Vⱼ) v = 0 := by
  let Xᵢ := vectorFieldOperator Vᵢ
  let Xⱼ := vectorFieldOperator Vⱼ
  let A := localizedBesselOperator η₁ η' s
  let T := operatorComm Xᵢ A
  have hTv : T v = 0 :=
    localizedBesselComm_eq_zero_of_vanish η₁ η' s Vᵢ v hη₁W hW hv
  have hvXⱼ : ∀ x ∈ W, Xⱼ v x = 0 := by
    intro x hx
    exact vectorFieldOperator_eq_zero_on_open Vⱼ v hW hv hx
  have hTXⱼv : T (Xⱼ v) = 0 :=
    localizedBesselComm_eq_zero_of_vanish η₁ η' s Vᵢ (Xⱼ v)
      hη₁W hW hvXⱼ
  change T (Xⱼ v) - Xⱼ (T v) = 0
  simp [hTXⱼv, hTv]

theorem nestedLocalizedBesselComm_eq_comp_of_cutoff {N : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (Vᵢ Vⱼ : Fin N → SchwartzMap (Carrier N) ℝ)
    (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆
      interior {x | η₂ x = 1}) :
    operatorComm
        (operatorComm (vectorFieldOperator Vᵢ)
          (localizedBesselOperator η₁ η' s))
        (vectorFieldOperator Vⱼ) =
      (operatorComm
        (operatorComm (vectorFieldOperator Vᵢ)
          (localizedBesselOperator η₁ η' s))
        (vectorFieldOperator Vⱼ)).comp (realMultiplierOperator η₂) := by
  apply operator_eq_comp_of_killing_difference
  intro v
  have hv : ∀ x ∈ interior {x | η₂ x = 1},
      (v - realMultiplierOperator η₂ v) x = 0 := by
    intro x hx
    have hsub : interior {y : Carrier N | η₂ y = 1} ⊆
        {y : Carrier N | η₂ y = 1} := interior_subset
    have hη₂ : η₂ x = 1 := hsub hx
    change v x - (realMultiplierOperator η₂ v) x = 0
    rw [realMultiplierOperator_apply, hη₂]
    simp
  exact nestedLocalizedBesselComm_eq_zero_of_vanish η₁ η' s Vᵢ Vⱼ
    (v - realMultiplierOperator η₂ v) hη₁W isOpen_interior hv

theorem tripleNestedLocalizedBesselComm_eq_zero_of_vanish {N : ℕ}
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V₁ V₂ V₃ : Fin N → SchwartzMap (Carrier N) ℝ) (v : TestFunction N)
    {W : Set (Carrier N)} (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆ W)
    (hW : IsOpen W) (hv : ∀ x ∈ W, v x = 0) :
    operatorComm
        (operatorComm (vectorFieldOperator V₁)
          (operatorComm (vectorFieldOperator V₂)
            (localizedBesselOperator η₁ η' s)))
        (vectorFieldOperator V₃) v = 0 := by
  let A := localizedBesselOperator η₁ η' s
  let X₁ := vectorFieldOperator V₁
  let X₂ := vectorFieldOperator V₂
  let X₃ := vectorFieldOperator V₃
  let P := operatorComm X₂ A
  let Q := operatorComm X₁ P
  have hP : ∀ w : TestFunction N, (∀ x ∈ W, w x = 0) → P w = 0 := by
    intro w hw
    exact localizedBesselComm_eq_zero_of_vanish η₁ η' s V₂ w hη₁W hW hw
  have hQ : ∀ w : TestFunction N, (∀ x ∈ W, w x = 0) → Q w = 0 := by
    intro w hw
    have hwX₁ : ∀ x ∈ W, X₁ w x = 0 := by
      intro x hx
      exact vectorFieldOperator_eq_zero_on_open V₁ w hW hw hx
    have hPw := hP w hw
    have hPX₁w := hP (X₁ w) hwX₁
    change X₁ (P w) - P (X₁ w) = 0
    simp [hPw, hPX₁w]
  have hvX₃ : ∀ x ∈ W, X₃ v x = 0 := by
    intro x hx
    exact vectorFieldOperator_eq_zero_on_open V₃ v hW hv hx
  have hQv := hQ v hv
  have hQX₃v := hQ (X₃ v) hvX₃
  change Q (X₃ v) - X₃ (Q v) = 0
  simp [hQv, hQX₃v]

theorem tripleNestedLocalizedBesselComm_eq_comp_of_cutoff {N : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V₁ V₂ V₃ : Fin N → SchwartzMap (Carrier N) ℝ)
    (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆
      interior {x | η₂ x = 1}) :
    operatorComm
        (operatorComm (vectorFieldOperator V₁)
          (operatorComm (vectorFieldOperator V₂)
            (localizedBesselOperator η₁ η' s)))
        (vectorFieldOperator V₃) =
      (operatorComm
        (operatorComm (vectorFieldOperator V₁)
          (operatorComm (vectorFieldOperator V₂)
            (localizedBesselOperator η₁ η' s)))
        (vectorFieldOperator V₃)).comp (realMultiplierOperator η₂) := by
  apply operator_eq_comp_of_killing_difference
  intro v
  have hv : ∀ x ∈ interior {y : Carrier N | η₂ y = 1},
      (v - realMultiplierOperator η₂ v) x = 0 := by
    intro x hx
    have hη₂ : η₂ x = 1 :=
      (interior_subset : interior {y : Carrier N | η₂ y = 1} ⊆
        {y : Carrier N | η₂ y = 1}) hx
    change v x - (realMultiplierOperator η₂ v) x = 0
    rw [realMultiplierOperator_apply, hη₂]
    simp
  exact tripleNestedLocalizedBesselComm_eq_zero_of_vanish η₁ η' s V₁ V₂ V₃
    (v - realMultiplierOperator η₂ v) hη₁W isOpen_interior hv

theorem outerVectorFieldLocalizedBesselComm_eq_zero_of_vanish {N : ℕ}
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V V₀ : Fin N → SchwartzMap (Carrier N) ℝ) (v : TestFunction N)
    {W : Set (Carrier N)} (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆ W)
    (hW : IsOpen W) (hv : ∀ x ∈ W, v x = 0) :
    operatorComm (vectorFieldOperator V₀)
      (operatorComm (vectorFieldOperator V)
        (localizedBesselOperator η₁ η' s)) v = 0 := by
  let A := localizedBesselOperator η₁ η' s
  let X := vectorFieldOperator V
  let X₀ := vectorFieldOperator V₀
  let P := operatorComm X A
  have hPv : P v = 0 :=
    localizedBesselComm_eq_zero_of_vanish η₁ η' s V v hη₁W hW hv
  have hvX₀ : ∀ x ∈ W, X₀ v x = 0 := by
    intro x hx
    exact vectorFieldOperator_eq_zero_on_open V₀ v hW hv hx
  have hPX₀v : P (X₀ v) = 0 :=
    localizedBesselComm_eq_zero_of_vanish η₁ η' s V (X₀ v) hη₁W hW hvX₀
  change X₀ (P v) - P (X₀ v) = 0
  simp [hPv, hPX₀v]

theorem outerVectorFieldLocalizedBesselComm_eq_comp_of_cutoff {N : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V V₀ : Fin N → SchwartzMap (Carrier N) ℝ)
    (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆
      interior {x | η₂ x = 1}) :
    operatorComm (vectorFieldOperator V₀)
      (operatorComm (vectorFieldOperator V)
        (localizedBesselOperator η₁ η' s)) =
      (operatorComm (vectorFieldOperator V₀)
        (operatorComm (vectorFieldOperator V)
          (localizedBesselOperator η₁ η' s))).comp (realMultiplierOperator η₂) := by
  apply operator_eq_comp_of_killing_difference
  intro v
  have hv : ∀ x ∈ interior {y : Carrier N | η₂ y = 1},
      (v - realMultiplierOperator η₂ v) x = 0 := by
    intro x hx
    have hη₂ : η₂ x = 1 :=
      (interior_subset : interior {y : Carrier N | η₂ y = 1} ⊆
        {y : Carrier N | η₂ y = 1}) hx
    change v x - (realMultiplierOperator η₂ v) x = 0
    rw [realMultiplierOperator_apply, hη₂]
    simp
  exact outerVectorFieldLocalizedBesselComm_eq_zero_of_vanish η₁ η' s V V₀
    (v - realMultiplierOperator η₂ v) hη₁W isOpen_interior hv

theorem outerMultiplierLocalizedBesselComm_eq_zero_of_vanish {N : ℕ}
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V : Fin N → SchwartzMap (Carrier N) ℝ)
    (c : SchwartzMap (Carrier N) ℝ) (v : TestFunction N)
    {W : Set (Carrier N)} (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆ W)
    (hW : IsOpen W)
    (hv : ∀ x ∈ W, v x = 0) :
    operatorComm (realMultiplierOperator c)
      (operatorComm (vectorFieldOperator V)
        (localizedBesselOperator η₁ η' s)) v = 0 := by
  let A := localizedBesselOperator η₁ η' s
  let X := vectorFieldOperator V
  let C := realMultiplierOperator c
  let P := operatorComm X A
  have hPv : P v = 0 :=
    localizedBesselComm_eq_zero_of_vanish η₁ η' s V v hη₁W hW hv
  have hCv : ∀ x ∈ W, C v x = 0 := by
    intro x hx
    simp [C, realMultiplierOperator_apply, hv x hx]
  have hPCv : P (C v) = 0 := by
    apply localizedBesselComm_eq_zero_of_vanish η₁ η' s V (C v) hη₁W hW hCv
  change C (P v) - P (C v) = 0
  simp [hPv, hPCv]

theorem outerMultiplierLocalizedBesselComm_eq_comp_of_cutoff {N : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V : Fin N → SchwartzMap (Carrier N) ℝ) (c : SchwartzMap (Carrier N) ℝ)
    (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆
      interior {x | η₂ x = 1}) :
    operatorComm (realMultiplierOperator c)
      (operatorComm (vectorFieldOperator V)
        (localizedBesselOperator η₁ η' s)) =
      (operatorComm (realMultiplierOperator c)
        (operatorComm (vectorFieldOperator V)
          (localizedBesselOperator η₁ η' s))).comp (realMultiplierOperator η₂) := by
  apply operator_eq_comp_of_killing_difference
  intro v
  have hv : ∀ x ∈ interior {y : Carrier N | η₂ y = 1},
      (v - realMultiplierOperator η₂ v) x = 0 := by
    intro x hx
    have hη₂ : η₂ x = 1 :=
      (interior_subset : interior {y : Carrier N | η₂ y = 1} ⊆
        {y : Carrier N | η₂ y = 1}) hx
    change v x - (realMultiplierOperator η₂ v) x = 0
    rw [realMultiplierOperator_apply, hη₂]
    simp
  exact outerMultiplierLocalizedBesselComm_eq_zero_of_vanish η₁ η' s V c
    (v - realMultiplierOperator η₂ v) hη₁W isOpen_interior hv

theorem multiplicationLocalizedBesselComm_eq_zero_of_vanish {N : ℕ}
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (c : SchwartzMap (Carrier N) ℝ) (v : TestFunction N)
    {W : Set (Carrier N)} (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆ W)
    (hv : ∀ x ∈ W, v x = 0) :
    operatorComm (realMultiplierOperator c)
      (localizedBesselOperator η₁ η' s) v = 0 := by
  let C := realMultiplierOperator c
  let A := localizedBesselOperator η₁ η' s
  have hcut : realMultiplierOperator η₁ v = 0 :=
    realMultiplierOperator_eq_zero_of_vanish hη₁W v hv
  have hAv : A v = 0 :=
    localizedBesselOperator_eq_zero_of_cutoff_eq_zero η₁ η' s v hcut
  have hvC : ∀ x ∈ W, C v x = 0 := by
    intro x hx
    simp [C, realMultiplierOperator_apply, hv x hx]
  have hcutC : realMultiplierOperator η₁ (C v) = 0 :=
    realMultiplierOperator_eq_zero_of_vanish hη₁W (C v) hvC
  have hACv : A (C v) = 0 :=
    localizedBesselOperator_eq_zero_of_cutoff_eq_zero η₁ η' s (C v) hcutC
  simp [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply, C, A, hAv, hACv]

theorem multiplicationLocalizedBesselComm_eq_comp_of_cutoff {N : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (c : SchwartzMap (Carrier N) ℝ)
    (hη₁W : tsupport (η₁ : Carrier N → ℝ) ⊆
      interior {x | η₂ x = 1}) :
    operatorComm (realMultiplierOperator c)
        (localizedBesselOperator η₁ η' s) =
      (operatorComm (realMultiplierOperator c)
        (localizedBesselOperator η₁ η' s)).comp (realMultiplierOperator η₂) := by
  apply operator_eq_comp_of_killing_difference
  intro v
  have hv : ∀ x ∈ interior {x | η₂ x = 1},
      (v - realMultiplierOperator η₂ v) x = 0 := by
    intro x hx
    have hsub : interior {y : Carrier N | η₂ y = 1} ⊆
        {y : Carrier N | η₂ y = 1} := interior_subset
    have hη₂ : η₂ x = 1 := hsub hx
    change v x - (realMultiplierOperator η₂ v) x = 0
    rw [realMultiplierOperator_apply, hη₂]
    simp
  exact multiplicationLocalizedBesselComm_eq_zero_of_vanish η₁ η' s c
    (v - realMultiplierOperator η₂ v) hη₁W hv

/-- The nested commutators act only on data localized
by the larger cutoff. -/
theorem rightSupportFactorization {N k : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V : Fin k → Fin N → SchwartzMap (Carrier N) ℝ)
    (V₀ : Fin N → SchwartzMap (Carrier N) ℝ)
    (c : SchwartzMap (Carrier N) ℝ)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    let A := localizedBesselOperator η₁ η' s
    let M₂ := Hormander.B.realMultiplierOperator η₂
    (∀ i, Hormander.B.operatorComm (Hormander.B.vectorFieldOperator (V i)) A =
      (Hormander.B.operatorComm (Hormander.B.vectorFieldOperator (V i)) A).comp M₂) ∧
    (∀ i j, Hormander.B.operatorComm
        (Hormander.B.operatorComm (Hormander.B.vectorFieldOperator (V i)) A)
        (Hormander.B.vectorFieldOperator (V j)) =
      (Hormander.B.operatorComm
        (Hormander.B.operatorComm (Hormander.B.vectorFieldOperator (V i)) A)
        (Hormander.B.vectorFieldOperator (V j))).comp M₂) ∧
    Hormander.B.operatorComm (Hormander.B.vectorFieldOperator V₀) A =
      (Hormander.B.operatorComm (Hormander.B.vectorFieldOperator V₀) A).comp M₂ ∧
    Hormander.B.operatorComm (Hormander.B.realMultiplierOperator c) A =
      (Hormander.B.operatorComm (Hormander.B.realMultiplierOperator c) A).comp M₂ := by
  have hη₁' : tsupport (η₁ : Carrier N → ℝ) ⊆
      interior {x | η' x = 1} :=
    (cutoffPrecedes_eventually_iff_interior _ _).mp hη₁η'.2.2.2.2
  have hη'₂ : tsupport (η' : Carrier N → ℝ) ⊆
      interior {x | η₂ x = 1} :=
    (cutoffPrecedes_eventually_iff_interior _ _).mp hη'η₂.2.2.2.2
  have hη₁₂ : tsupport (η₁ : Carrier N → ℝ) ⊆
      interior {x | η₂ x = 1} := by
    intro x hx
    have hsub : interior {y : Carrier N | η' y = 1} ⊆
        {y : Carrier N | η' y = 1} := interior_subset
    have hxη' : η' x = 1 := hsub (hη₁' hx)
    have hxSupport : x ∈ tsupport (η' : Carrier N → ℝ) := by
      apply subset_tsupport
      simp [hxη']
    exact hη'₂ hxSupport
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact localizedBesselComm_eq_comp_of_cutoff η₁ η' η₂ s (V i) hη₁₂
  · intro i j
    exact nestedLocalizedBesselComm_eq_comp_of_cutoff η₁ η' η₂ s
      (V i) (V j) hη₁₂
  · exact localizedBesselComm_eq_comp_of_cutoff η₁ η' η₂ s V₀ hη₁₂
  · exact multiplicationLocalizedBesselComm_eq_comp_of_cutoff η₁ η' η₂ s c hη₁₂

/-- Right factorization for every commutator input in the energy expansion. -/
theorem localizedBesselEnergyComm_right_factorization {N k : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V : Fin k → RealSchwartzVectorField N)
    (V₀ : RealSchwartzVectorField N) (c : SchwartzMap (Carrier N) ℝ)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    let A := localizedBesselOperator η₁ η' s
    let M₂ := realMultiplierOperator η₂
    (∀ i, operatorComm (vectorFieldOperator (V i)) A =
      (operatorComm (vectorFieldOperator (V i)) A).comp M₂) ∧
    (∀ i j, operatorComm (vectorFieldOperator (V j))
        (operatorComm (vectorFieldOperator (V i)) A) =
      (operatorComm (vectorFieldOperator (V j))
        (operatorComm (vectorFieldOperator (V i)) A)).comp M₂) ∧
    (∀ i j, operatorComm
        (operatorComm (vectorFieldOperator (V j))
          (operatorComm (vectorFieldOperator (V i)) A))
        (vectorFieldOperator (V j)) =
      (operatorComm
        (operatorComm (vectorFieldOperator (V j))
          (operatorComm (vectorFieldOperator (V i)) A))
        (vectorFieldOperator (V j))).comp M₂) ∧
    (∀ i, operatorComm (vectorFieldOperator V₀)
        (operatorComm (vectorFieldOperator (V i)) A) =
      (operatorComm (vectorFieldOperator V₀)
        (operatorComm (vectorFieldOperator (V i)) A)).comp M₂) ∧
    (∀ i, operatorComm (realMultiplierOperator c)
        (operatorComm (vectorFieldOperator (V i)) A) =
      (operatorComm (realMultiplierOperator c)
        (operatorComm (vectorFieldOperator (V i)) A)).comp M₂) := by
  have hη₁' : tsupport (η₁ : Carrier N → ℝ) ⊆
      interior {x | η' x = 1} :=
    (cutoffPrecedes_eventually_iff_interior _ _).mp hη₁η'.2.2.2.2
  have hη'₂ : tsupport (η' : Carrier N → ℝ) ⊆
      interior {x | η₂ x = 1} :=
    (cutoffPrecedes_eventually_iff_interior _ _).mp hη'η₂.2.2.2.2
  have hη₁₂ : tsupport (η₁ : Carrier N → ℝ) ⊆
      interior {x | η₂ x = 1} := by
    intro x hx
    have hη'one : η' x = 1 :=
      (interior_subset : interior {y : Carrier N | η' y = 1} ⊆
        {y : Carrier N | η' y = 1}) (hη₁' hx)
    have hxη' : x ∈ tsupport (η' : Carrier N → ℝ) := by
      apply subset_tsupport
      simp [hη'one]
    exact hη'₂ hxη'
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact localizedBesselComm_eq_comp_of_cutoff η₁ η' η₂ s (V i) hη₁₂
  · intro i j
    exact outerVectorFieldLocalizedBesselComm_eq_comp_of_cutoff
      η₁ η' η₂ s (V i) (V j) hη₁₂
  · intro i j
    exact tripleNestedLocalizedBesselComm_eq_comp_of_cutoff
      η₁ η' η₂ s (V j) (V i) (V j) hη₁₂
  · intro i
    exact outerVectorFieldLocalizedBesselComm_eq_comp_of_cutoff
      η₁ η' η₂ s (V i) V₀ hη₁₂
  · intro i
    exact outerMultiplierLocalizedBesselComm_eq_comp_of_cutoff
      η₁ η' η₂ s (V i) c hη₁₂

end Hormander.D

end
