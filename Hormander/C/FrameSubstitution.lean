-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.CutoffLocalization
public import Hormander.C.Assembly.Estimate
public import Hormander.C.SobolevNorm
public import Hormander.B.Multipliers
public import Hormander.B.Differential

@[expose] public section

noncomputable section

open Filter MeasureTheory Topology SchwartzMap

namespace Hormander.C

/-- The pointwise vector field represented by its Schwartz coordinate coefficients. -/
def realSchwartzVectorFieldValue {N : ℕ}
    (V : Hormander.B.RealSchwartzVectorField N) (x : Hormander.A.Carrier N) :
    Hormander.A.Carrier N := WithLp.toLp 2 (fun i => V i x)

@[simp] theorem realSchwartzVectorFieldValue_proj {N : ℕ}
    (V : Hormander.B.RealSchwartzVectorField N) (x : Hormander.A.Carrier N) (i : Fin N) :
    EuclideanSpace.proj (𝕜 := ℝ) i (realSchwartzVectorFieldValue V x) = V i x := rfl

/-- Multiplication by a real Schwartz coefficient acts pointwise on complex test functions. -/
@[simp]
theorem realMultiplierOperator_apply {N : ℕ}
    (g : SchwartzMap (Hormander.A.Carrier N) ℝ) (u : Hormander.B.TestFunction N)
    (x : Hormander.A.Carrier N) :
    Hormander.B.realMultiplierOperator g u x = ((g x : ℝ) : ℂ) * u x := by
  change SchwartzMap.smulLeftCLM ℂ (Hormander.B.complexifyRealSchwartz g) u x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (Hormander.B.complexifyRealSchwartz g).hasTemperateGrowth]
  simp [Hormander.B.complexifyRealSchwartz]

/-- Applying the shared Schwartz vector-field operator is its coordinate derivative formula. -/
theorem vectorFieldOperator_apply {N : ℕ}
    (V : Hormander.B.RealSchwartzVectorField N) (u : Hormander.B.TestFunction N)
    (x : Hormander.A.Carrier N) :
    Hormander.B.vectorFieldOperator V u x =
      ∑ i : Fin N, ((V i x : ℝ) : ℂ) *
        fderiv ℝ (u : Hormander.A.Carrier N → ℂ) x (EuclideanSpace.single i (1 : ℝ)) := by
  simp [Hormander.B.vectorFieldOperator, Hormander.B.coordinateDerivative,
    LinearMap.sum_apply, LinearMap.comp_apply, SchwartzMap.lineDerivOpCLM_eq]

/-- On the neighborhood where the matrix identity holds, coordinate differentiation is the
corresponding finite combination of the selected vector fields. -/
theorem coordinateDerivative_eq_frameCombination {N : ℕ}
    {K W : Set (Hormander.A.Carrier N)} (hKW : K ⊆ W)
    (V : Fin N → Hormander.B.RealSchwartzVectorField N)
    (γ : Fin N → Fin N → SchwartzMap (Hormander.A.Carrier N) ℝ)
    (hframe : ∀ x ∈ W, ∀ i j : Fin N,
      ∑ a : Fin N, γ j a x * V a i x = if i = j then 1 else 0)
    (u : SchwartzMap (Hormander.A.Carrier N) ℂ)
    (hu : tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K) (j : Fin N) :
    Hormander.B.coordinateDerivative j u =
      ∑ a : Fin N, Hormander.B.realMultiplierOperator (γ j a)
        (Hormander.B.vectorFieldOperator (V a) u) := by
  ext x
  by_cases hx : x ∈ K
  · have hxW := hKW hx
    have hlocal (i : Fin N) :
        ∑ a : Fin N, γ j a x * V a i x = if i = j then 1 else 0 := hframe x hxW i j
    rw [sum_apply]
    simp only [realMultiplierOperator_apply, vectorFieldOperator_apply]
    rw [show Hormander.B.coordinateDerivative j u x =
        fderiv ℝ (u : Hormander.A.Carrier N → ℂ) x (EuclideanSpace.single j 1) by
      simp [Hormander.B.coordinateDerivative, SchwartzMap.lineDerivOpCLM_eq]]
    calc
      (fderiv ℝ (u : Hormander.A.Carrier N → ℂ) x (EuclideanSpace.single j 1)) =
          ∑ i : Fin N, ((if i = j then 1 else 0 : ℝ) : ℂ) *
            fderiv ℝ (u : Hormander.A.Carrier N → ℂ) x (EuclideanSpace.single i 1) := by
              rw [Finset.sum_eq_single j]
              · simp
              · intro i hi hij
                simp [hij]
              · simp
      _ = ∑ i : Fin N, (∑ a : Fin N, ((γ j a x : ℝ) : ℂ) *
            ((V a i x : ℝ) : ℂ)) *
            fderiv ℝ (u : Hormander.A.Carrier N → ℂ) x (EuclideanSpace.single i 1) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hc :
                  ∑ a : Fin N, ((γ j a x : ℝ) : ℂ) * ((V a i x : ℝ) : ℂ) =
                    ((if i = j then 1 else 0 : ℝ) : ℂ) := by
                have hh := congrArg (fun z : ℝ => (z : ℂ)) (hlocal i)
                calc
                  ∑ a : Fin N, ((γ j a x : ℝ) : ℂ) * ((V a i x : ℝ) : ℂ) =
                      ∑ a : Fin N, ((γ j a x * V a i x : ℝ) : ℂ) := by
                        apply Finset.sum_congr rfl
                        intro a ha
                        exact (Complex.ofReal_mul _ _).symm
                  _ = ((∑ a : Fin N, γ j a x * V a i x : ℝ) : ℂ) := by
                        rw [Complex.ofReal_sum]
                  _ = ((if i = j then 1 else 0 : ℝ) : ℂ) := hh
              rw [hc]
      _ = ∑ i : Fin N, ∑ a : Fin N, (((γ j a x : ℝ) : ℂ) *
            ((V a i x : ℝ) : ℂ)) *
            fderiv ℝ (u : Hormander.A.Carrier N → ℂ) x (EuclideanSpace.single i 1) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_mul]
      _ = ∑ a : Fin N, ∑ i : Fin N, ((γ j a x : ℝ) : ℂ) *
            (((V a i x : ℝ) : ℂ) *
              fderiv ℝ (u : Hormander.A.Carrier N → ℂ) x (EuclideanSpace.single i 1)) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = ∑ a : Fin N, ((γ j a x : ℝ) : ℂ) *
            (∑ i : Fin N, ((V a i x : ℝ) : ℂ) *
              fderiv ℝ (u : Hormander.A.Carrier N → ℂ) x (EuclideanSpace.single i 1)) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum]
  · have hxnot : x ∉ tsupport (u : Hormander.A.Carrier N → ℂ) := fun hu' => hx (hu hu')
    have hnear : (u : Hormander.A.Carrier N → ℂ) =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
      (notMem_tsupport_iff_eventuallyEq).mp hxnot
    have hderiv : fderiv ℝ (u : Hormander.A.Carrier N → ℂ) x = 0 := by
      simpa using hnear.fderiv_eq (𝕜 := ℝ)
    rw [show Hormander.B.coordinateDerivative j u x =
        fderiv ℝ (u : Hormander.A.Carrier N → ℂ) x (EuclideanSpace.single j 1) by
      simp [Hormander.B.coordinateDerivative, SchwartzMap.lineDerivOpCLM_eq], hderiv]
    simp [realMultiplierOperator_apply,
      vectorFieldOperator_apply, hderiv]

/-- The selected Sobolev norm obeys the finite-sum triangle inequality. -/
theorem schwartzSobolevNorm_sum_le {N : ℕ} (s : ℝ)
    (f : Fin N → SchwartzMap (Hormander.A.Carrier N) ℂ) :
    Hormander.A.schwartzSobolevNorm s (∑ a : Fin N, f a) ≤
      ∑ a : Fin N, Hormander.A.schwartzSobolevNorm s (f a) := by
  let T : SchwartzMap (Hormander.A.Carrier N) ℂ →L[ℂ]
      MeasureTheory.Lp ℂ 2 volume :=
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp (Hormander.A.Lambda s)
  change ‖T (∑ a : Fin N, f a)‖ ≤ ∑ a : Fin N, ‖T (f a)‖
  rw [map_sum]
  exact norm_sum_le Finset.univ (fun a => T (f a))

/-- The order-zero bounds control one coordinate derivative by the finite frame. -/
theorem frame_coordinate_sobolev_bound_at {N : ℕ} {K W : Set (Hormander.A.Carrier N)}
    (hKW : K ⊆ W)
    (V : Fin N → Hormander.B.RealSchwartzVectorField N)
    (γ : Fin N → Fin N → SchwartzMap (Hormander.A.Carrier N) ℝ)
    (hframe : ∀ x ∈ W, ∀ i j : Fin N,
      ∑ a : Fin N, γ j a x * V a i x = if i = j then 1 else 0)
    (δ : ℝ) (j : Fin N) :
    ∃ C : NNReal, ∀ (u : SchwartzMap (Hormander.A.Carrier N) ℂ),
      tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K →
      Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.coordinateDerivative j u) ≤
        (C : ℝ) * ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u) := by
  classical
  let hmult : ∀ a : Fin N, ∃ C : NNReal, ∀ u : SchwartzMap (Hormander.A.Carrier N) ℂ,
      Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.realMultiplierOperator (γ j a)
            (Hormander.B.vectorFieldOperator (V a) u)) ≤
        (C : ℝ) * Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u) := by
    intro a
    have horder : Hormander.B.HasOrder 0
        (Hormander.B.realMultiplierOperator (γ j a)) := by
      simpa only [Hormander.B.realMultiplierOperator] using
        (Hormander.B.peetre_and_multiplier_order (N := N)).2
          (Hormander.B.complexifyRealSchwartz (γ j a))
    change ∀ s : ℝ, ∃ C : NNReal, ∀ u : SchwartzMap (Hormander.A.Carrier N) ℂ,
      Hormander.B.sobolevNorm s
          (Hormander.B.realMultiplierOperator (γ j a) u) ≤
        (C : ℝ) * Hormander.B.sobolevNorm (s + 0) u at horder
    obtain ⟨C, hC⟩ := horder (δ - 1)
    refine ⟨C, fun u => ?_⟩
    simpa only [add_zero, Hormander.B.sobolevNorm_eq_schwartzSobolevNorm] using
      hC (Hormander.B.vectorFieldOperator (V a) u)
  let C : Fin N → NNReal := fun a => Classical.choose (hmult a)
  have hC (a : Fin N) (u : SchwartzMap (Hormander.A.Carrier N) ℂ) :
      Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.realMultiplierOperator (γ j a)
            (Hormander.B.vectorFieldOperator (V a) u)) ≤
        (C a : ℝ) * Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u) :=
    Classical.choose_spec (hmult a) u
  let Ctotal : NNReal := ∑ a : Fin N, C a
  have htotal (a : Fin N) : C a ≤ Ctotal := by
    change C a ≤ ∑ b : Fin N, C b
    apply Finset.single_le_sum
    · intro b hb
      exact zero_le
    · exact Finset.mem_univ a
  refine ⟨Ctotal, fun u hu => ?_⟩
  have heq := coordinateDerivative_eq_frameCombination
    (K := K) (W := W) hKW V γ hframe u hu j
  have htriangle := schwartzSobolevNorm_sum_le (δ - 1)
    (fun a : Fin N => Hormander.B.realMultiplierOperator (γ j a)
      (Hormander.B.vectorFieldOperator (V a) u))
  have hterm (a : Fin N) :
      Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.realMultiplierOperator (γ j a)
            (Hormander.B.vectorFieldOperator (V a) u)) ≤
        (Ctotal : ℝ) * Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u) := by
    have hle := hC a u
    have hconst : (C a : ℝ) ≤ (Ctotal : ℝ) := by exact_mod_cast htotal a
    calc
      _ ≤ (C a : ℝ) * Hormander.A.schwartzSobolevNorm (δ - 1)
            (Hormander.B.vectorFieldOperator (V a) u) := by
              exact hle
      _ ≤ (Ctotal : ℝ) * Hormander.A.schwartzSobolevNorm (δ - 1)
            (Hormander.B.vectorFieldOperator (V a) u) :=
        mul_le_mul_of_nonneg_right hconst (norm_nonneg _)
  calc
    Hormander.A.schwartzSobolevNorm (δ - 1)
        (Hormander.B.coordinateDerivative j u) =
      Hormander.A.schwartzSobolevNorm (δ - 1)
        (∑ a : Fin N, Hormander.B.realMultiplierOperator (γ j a)
          (Hormander.B.vectorFieldOperator (V a) u)) := congrArg _ heq
    _ ≤ ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.realMultiplierOperator (γ j a)
            (Hormander.B.vectorFieldOperator (V a) u)) := htriangle
    _ ≤ ∑ a : Fin N, (Ctotal : ℝ) * Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u) :=
      Finset.sum_le_sum fun a ha => hterm a
    _ = (Ctotal : ℝ) * ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u) := by rw [Finset.mul_sum]

/-- The coordinate estimates hold with one constant uniform over the finite frame. -/
theorem frame_coordinate_sobolev_bound {N : ℕ} {K W : Set (Hormander.A.Carrier N)}
    (hKW : K ⊆ W)
    (V : Fin N → Hormander.B.RealSchwartzVectorField N)
    (γ : Fin N → Fin N → SchwartzMap (Hormander.A.Carrier N) ℝ)
    (hframe : ∀ x ∈ W, ∀ i j : Fin N,
      ∑ a : Fin N, γ j a x * V a i x = if i = j then 1 else 0)
    (δ : ℝ) :
    ∃ C : NNReal, ∀ (j : Fin N) (u : SchwartzMap (Hormander.A.Carrier N) ℂ),
      tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K →
      Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.coordinateDerivative j u) ≤
        (C : ℝ) * ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u) := by
  classical
  let hAt : ∀ j : Fin N, ∃ C : NNReal, ∀ u : SchwartzMap (Hormander.A.Carrier N) ℂ,
      tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K →
      Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.coordinateDerivative j u) ≤
        (C : ℝ) * ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u) := by
    intro j
    exact frame_coordinate_sobolev_bound_at hKW V γ hframe δ j
  let C : Fin N → NNReal := fun j => Classical.choose (hAt j)
  have hC (j : Fin N) (u : SchwartzMap (Hormander.A.Carrier N) ℂ)
      (hu : tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K) :
      Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.coordinateDerivative j u) ≤
        (C j : ℝ) * ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u) :=
    Classical.choose_spec (hAt j) u hu
  let Ctotal : NNReal := ∑ j : Fin N, C j
  have htotal (j : Fin N) : C j ≤ Ctotal := by
    change C j ≤ ∑ i : Fin N, C i
    apply Finset.single_le_sum
    · intro i hi
      exact zero_le
    · exact Finset.mem_univ j
  refine ⟨Ctotal, fun j u hu => ?_⟩
  calc
    Hormander.A.schwartzSobolevNorm (δ - 1)
        (Hormander.B.coordinateDerivative j u) ≤
      (C j : ℝ) * ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
        (Hormander.B.vectorFieldOperator (V a) u) := hC j u hu
    _ ≤ (Ctotal : ℝ) * ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast htotal j)
        (Finset.sum_nonneg fun a ha => norm_nonneg _)

/-- Convert compactly supported smooth frame coefficients to Schwartz coefficients. -/
theorem exists_localized_schwartz_frame_coefficients {N : ℕ}
    {K U : Set (Hormander.A.Carrier N)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (V : Fin N → Hormander.B.RealSchwartzVectorField N)
    (hframe : ∀ x ∈ U,
      LinearIndependent ℝ (fun a : Fin N => realSchwartzVectorFieldValue (V a) x)) :
    ∃ W : Set (Hormander.A.Carrier N), IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      ∃ γ : Fin N → Fin N → SchwartzMap (Hormander.A.Carrier N) ℝ,
        ∀ x ∈ W, ∀ i j : Fin N,
          ∑ a : Fin N, γ j a x * V a i x = if i = j then 1 else 0 := by
  let vf : Fin N → Hormander.A.Carrier N → Hormander.A.Carrier N :=
    fun a x => realSchwartzVectorFieldValue (V a) x
  have hvf : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (vf a) := by
    intro a
    dsimp [vf, realSchwartzVectorFieldValue]
    fun_prop
  have hdet : ∀ x ∈ U, (Hormander.C.frameMatrixAt vf x).det ≠ 0 := by
    intro x hx
    exact (Hormander.C.frameMatrix_det_ne_zero_iff (fun a => vf a x)).2
      (hframe x hx)
  obtain ⟨W, hWopen, hKW', hWU, γ, hγsmooth, hγcompact, hγsupport,
      hdetLower, hidentity⟩ :=
    Hormander.C.exists_frame_coefficients_and_determinant_bound vf hvf hK hU hKU hdet
  let γS : Fin N → Fin N → SchwartzMap (Hormander.A.Carrier N) ℝ :=
    fun j a => (hγcompact j a).toSchwartzMap (hγsmooth j a)
  refine ⟨W, hWopen, hKW', hWU, γS, ?_⟩
  have hidS : ∀ x ∈ W, ∀ i j : Fin N,
      ∑ a : Fin N, γS j a x * V a i x = if i = j then 1 else 0 := by
    intro x hx i j
    have h := hidentity x hx i j
    have hγ (a : Fin N) : γS j a x = γ j a x := rfl
    calc
      (∑ a : Fin N, γS j a x * V a i x) =
          ∑ a : Fin N, γ j a x * V a i x := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [hγ a]
      _ = ∑ a : Fin N, γ j a x *
          EuclideanSpace.proj (𝕜 := ℝ) i (vf a x) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [realSchwartzVectorFieldValue_proj]
      _ = if i = j then 1 else 0 := h
  exact hidS

/-- Use the frame data to control each coordinate derivative
by the selected Schwartz vector fields. -/
theorem frame_coordinate_sobolev_bound_of_frame {N : ℕ}
    {K U : Set (Hormander.A.Carrier N)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (V : Fin N → Hormander.B.RealSchwartzVectorField N)
    (hframe : ∀ x ∈ U,
      LinearIndependent ℝ (fun a : Fin N => fieldVec (V a) x))
    (δ : ℝ) :
    ∃ C : NNReal, ∀ (j : Fin N) (u : SchwartzMap (Hormander.A.Carrier N) ℂ),
      tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K →
      Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.coordinateDerivative j u) ≤
        (C : ℝ) * ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u) := by
  obtain ⟨W, hWopen, hKW, hWU, γ, hidentity⟩ :=
    exists_localized_schwartz_frame_coefficients hK hU hKU V hframe
  exact frame_coordinate_sobolev_bound hKW V γ hidentity δ

/-- Squaring the uniform coordinate estimate and summing uses only finite-dimensional
Cauchy--Schwarz. -/
theorem frame_coordinate_square_sum_bound {N : ℕ}
    {K U : Set (Hormander.A.Carrier N)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (V : Fin N → Hormander.B.RealSchwartzVectorField N)
    (hframe : ∀ x ∈ U,
      LinearIndependent ℝ (fun a : Fin N => realSchwartzVectorFieldValue (V a) x))
    (δ : ℝ) :
    ∃ C : NNReal, ∀ (u : SchwartzMap (Hormander.A.Carrier N) ℂ),
      tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K →
      (∑ j : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
        (Hormander.B.coordinateDerivative j u)) ^ 2) ≤
        (N : ℝ) ^ 2 * (C : ℝ) ^ 2 *
          ∑ a : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
            (Hormander.B.vectorFieldOperator (V a) u)) ^ 2 := by
  classical
  obtain ⟨Cframe, hframeBound⟩ :=
    frame_coordinate_sobolev_bound_of_frame hK hU hKU V hframe δ
  refine ⟨Cframe, fun u hu => ?_⟩
  let b : Fin N → ℝ := fun a =>
    Hormander.A.schwartzSobolevNorm (δ - 1) (Hormander.B.vectorFieldOperator (V a) u)
  have hb : ∀ a, 0 ≤ b a := fun a => norm_nonneg _
  have hcs : (∑ a : Fin N, b a) ^ 2 ≤ (N : ℝ) * ∑ a : Fin N, b a ^ 2 := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin N => (1 : ℝ)) b
    simpa using hcs0
  have hcoordinateSq : ∀ j : Fin N,
      (Hormander.A.schwartzSobolevNorm (δ - 1)
        (Hormander.B.coordinateDerivative j u)) ^ 2 ≤
        ((Cframe : ℝ) * ∑ a : Fin N, b a) ^ 2 := by
    intro j
    have hbound := hframeBound j u hu
    have hbound' :
        Hormander.A.schwartzSobolevNorm (δ - 1)
            (Hormander.B.coordinateDerivative j u) ≤
          (Cframe : ℝ) * ∑ a : Fin N, b a := by
      simpa [b] using hbound
    have hsum : 0 ≤ ∑ a : Fin N, b a := Finset.sum_nonneg fun a ha => hb a
    have hprod : 0 ≤ (Cframe : ℝ) * ∑ a : Fin N, b a :=
      mul_nonneg (by exact_mod_cast (NNReal.coe_nonneg Cframe)) hsum
    have hnorm : 0 ≤ Hormander.A.schwartzSobolevNorm (δ - 1)
        (Hormander.B.coordinateDerivative j u) := norm_nonneg _
    nlinarith [hbound', hprod, hnorm]
  calc
    _ ≤ ∑ _j : Fin N, ((Cframe : ℝ) * ∑ a : Fin N, b a) ^ 2 :=
      Finset.sum_le_sum fun j hj => hcoordinateSq j
    _ = (N : ℝ) * ((Cframe : ℝ) * ∑ a : Fin N, b a) ^ 2 := by simp
    _ = (N : ℝ) * (Cframe : ℝ) ^ 2 * (∑ a : Fin N, b a) ^ 2 := by ring
    _ ≤ (N : ℝ) * (Cframe : ℝ) ^ 2 *
          ((N : ℝ) * ∑ a : Fin N, b a ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = (N : ℝ) ^ 2 * (Cframe : ℝ) ^ 2 *
          ∑ a : Fin N, b a ^ 2 := by ring

theorem add_mul_le_one_add_mul (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hc : 0 ≤ c) : x + c * y ≤ (1 + c) * (x + y) := by
  nlinarith [mul_nonneg hc hx]

/-- Squared coordinate derivative norms agree with the directional derivative notation used by
the Fourier estimate. -/
theorem coordinateDerivative_sq_sum_eq_lineDeriv {N : ℕ} {s : ℝ}
    (u : SchwartzMap (Hormander.A.Carrier N) ℂ) :
    (∑ j : Fin N, (Hormander.A.schwartzSobolevNorm s
      (Hormander.B.coordinateDerivative j u)) ^ 2) =
      ∑ j : Fin N, (Hormander.A.schwartzSobolevNorm s
        (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u)) ^ 2 := by
  have hderiv (j : Fin N) :
      LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u =
        Hormander.B.coordinateDerivative j u := by
    ext x
    simp [Hormander.B.coordinateDerivative, SchwartzMap.lineDerivOpCLM_eq,
      SchwartzMap.lineDerivOp_apply_eq_fderiv]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hderiv j]

/-- The coordinate square sum gives a scaled Fourier derivative term. -/
theorem scaled_derivative_square_bound {N : ℕ}
    {K : Set (Hormander.A.Carrier N)}
    (V : Fin N → Hormander.B.RealSchwartzVectorField N) {δ : ℝ}
    (hframeSq : ∃ C : NNReal, ∀ (u : SchwartzMap (Hormander.A.Carrier N) ℂ),
      tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K →
      (∑ j : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
        (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u)) ^ 2) ≤
        (N : ℝ) ^ 2 * (C : ℝ) ^ 2 *
          ∑ a : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
            (Hormander.B.vectorFieldOperator (V a) u)) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SchwartzMap (Hormander.A.Carrier N) ℂ),
      tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K →
      ((2 * Real.pi) ^ 2)⁻¹ *
          ∑ j : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
            (Hormander.B.coordinateDerivative j u)) ^ 2 ≤
        C * ∑ a : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u)) ^ 2 := by
  obtain ⟨Cframe, hframeSq⟩ := hframeSq
  let C : ℝ := ((2 * Real.pi) ^ 2)⁻¹ * (N : ℝ) ^ 2 * (Cframe : ℝ) ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun u hu => ?_⟩
  have hfourierCoeff : 0 ≤ ((2 * Real.pi) ^ 2)⁻¹ :=
    inv_nonneg.mpr (sq_nonneg _)
  have hframeLine :
      (∑ j : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
        (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u)) ^ 2) ≤
        (N : ℝ) ^ 2 * (Cframe : ℝ) ^ 2 *
          ∑ a : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
            (Hormander.B.vectorFieldOperator (V a) u)) ^ 2 := by
    rw [← coordinateDerivative_sq_sum_eq_lineDeriv u]
    exact hframeSq u hu
  calc
    _ ≤ ((2 * Real.pi) ^ 2)⁻¹ *
          ((N : ℝ) ^ 2 * (Cframe : ℝ) ^ 2 *
            ∑ a : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
              (Hormander.B.vectorFieldOperator (V a) u)) ^ 2) :=
      mul_le_mul_of_nonneg_left hframeLine hfourierCoeff
    _ = C * ∑ a : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u)) ^ 2 := by
      dsimp [C]
      ring

/-- The Fourier estimate absorbs any established scaled derivative square bound. -/
theorem coordinate_sobolev_inequality_of_scaled_bound {N : ℕ}
    {K : Set (Hormander.A.Carrier N)}
    (V : Fin N → Hormander.B.RealSchwartzVectorField N)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hscaled : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SchwartzMap (Hormander.A.Carrier N) ℂ),
      tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K →
      ((2 * Real.pi) ^ 2)⁻¹ *
          ∑ j : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
            (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u)) ^ 2 ≤
        C * ∑ a : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u)) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : SchwartzMap (Hormander.A.Carrier N) ℂ),
      tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K →
      Hormander.A.schwartzSobolevNorm δ u ^ 2 ≤
        C * (functionL2Sq u +
          ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
            (Hormander.B.vectorFieldOperator (V a) u) ^ 2) := by
  obtain ⟨Cscaled, hCscaled, hscaled⟩ := hscaled
  let finalCoeff : ℝ := 1 + Cscaled
  have hfinalCoeff : 0 < finalCoeff := by
    dsimp [finalCoeff]
    linarith
  refine ⟨finalCoeff, hfinalCoeff, fun u hu => ?_⟩
  have hwordSq : 0 ≤ ∑ a : Fin N,
      (Hormander.A.schwartzSobolevNorm (δ - 1)
        (Hormander.B.vectorFieldOperator (V a) u)) ^ 2 :=
    Finset.sum_nonneg fun a ha => sq_nonneg _
  have hL2 : 0 ≤ functionL2Sq u := integral_nonneg fun x => sq_nonneg ‖u x‖
  have hFourier := fourier_coordinate_estimate_integral hδ0 hδ1 u
  have hFourierDeriv :
      (∑ j : Fin N, weightedFourierSq (δ - 1)
        (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u)) =
      ∑ j : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
        (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    exact weightedFourierSq_eq_schwartzSobolevNorm_sq (δ - 1)
      (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u)
  have hfirst : Hormander.A.schwartzSobolevNorm δ u ^ 2 ≤
      functionL2Sq u + Cscaled *
        ∑ a : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u)) ^ 2 := by
    calc
      _ = weightedFourierSq δ u :=
        (weightedFourierSq_eq_schwartzSobolevNorm_sq δ u).symm
      _ ≤ functionL2Sq u + ((2 * Real.pi) ^ 2)⁻¹ *
          ∑ j : Fin N, weightedFourierSq (δ - 1)
            (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u) := hFourier
      _ = functionL2Sq u + ((2 * Real.pi) ^ 2)⁻¹ *
          ∑ j : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
            (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u)) ^ 2 := by
        rw [hFourierDeriv]
      _ ≤ _ := by linarith [hscaled u hu]
  have hlast : functionL2Sq u + Cscaled *
      ∑ a : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
        (Hormander.B.vectorFieldOperator (V a) u)) ^ 2 ≤
      finalCoeff * (functionL2Sq u +
        ∑ a : Fin N, (Hormander.A.schwartzSobolevNorm (δ - 1)
          (Hormander.B.vectorFieldOperator (V a) u)) ^ 2) := by
    dsimp [finalCoeff]
    exact add_mul_le_one_add_mul _ _ _ hL2 hwordSq hCscaled
  exact hfirst.trans hlast

/-- The frame substitution and Fourier coordinate estimate give the local Sobolev
inequality on a compactly supported frame. -/
theorem coordinate_sobolev_inequality_of_frame_integral {N : ℕ}
    {K U : Set (Hormander.A.Carrier N)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (V : Fin N → Hormander.B.RealSchwartzVectorField N)
    (hframe : ∀ x ∈ U,
      LinearIndependent ℝ (fun a : Fin N => realSchwartzVectorFieldValue (V a) x))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : SchwartzMap (Hormander.A.Carrier N) ℂ),
      tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K →
    Hormander.A.schwartzSobolevNorm δ u ^ 2 ≤
        C * (functionL2Sq u +
          ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
            (Hormander.B.vectorFieldOperator (V a) u) ^ 2) := by
  exact coordinate_sobolev_inequality_of_scaled_bound V hδ0 hδ1
    (scaled_derivative_square_bound V
      (frame_coordinate_square_sum_bound hK hU hKU V hframe δ))

/- The public coordinate inequality is exactly the shared assembly interface. -/
theorem coordinate_sobolev_inequality_of_frame {N : ℕ} : CoordinateInequality N := by
  intro K U hK hU hKU V hframe δ hδ0 hδ1
  obtain ⟨C, hC, hbound⟩ := coordinate_sobolev_inequality_of_frame_integral
    hK hU hKU V hframe hδ0 hδ1
  refine ⟨C, hC, fun u hu => ?_⟩
  have h := hbound u hu
  simpa only [functionL2Sq_eq_toLp_norm_sq] using h

end Hormander.C
