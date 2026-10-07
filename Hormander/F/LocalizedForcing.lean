-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.Assembly.Hypotheses
public import Hormander.F.TransposedActionBridge
public import Hormander.F.DistributionalRewrite
public import Hormander.Interface.HasWeakHormanderEquation
public import Hormander.F.IntegrabilityTransfer
public import Hormander.F.FrameExtension
public import Hormander.F.Coordinates
public import Hormander.F.DifferentialTransport
public import Hormander.F.SchwartzTransport
public import Hormander.F.AdjointTest
public import Hormander.F.Transpose
public import Mathlib.Analysis.Distribution.TemperedDistribution

@[expose] public section

noncomputable section

open Filter Function MeasureTheory SchwartzMap Set Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace Hormander.F

/-- If a compactly supported cutoff is one near the test support, that test support lies in the
ball containing the cutoff support. -/
theorem localizedTest_tsupport_subset_ball {N : ℕ} {x₀ : E₂ N} {r : ℝ}
    (χ η : E₂ N → ℝ) (hχη : ∀ᶠ x in 𝓝ˢ (tsupport η), χ x = 1)
    (hχ : tsupport χ ⊆ Metric.ball x₀ r) :
    tsupport η ⊆ Metric.ball x₀ r := by
  intro y hy
  have hnear : ∀ᶠ z in 𝓝 y, χ z = 1 :=
    hχη.filter_mono (nhds_le_nhdsSet hy)
  have hvalue : χ y = 1 := hnear.self_of_nhds
  have hysupport : y ∈ support χ := by
    rw [mem_support, hvalue]
    norm_num
  have hysupport' : y ∈ tsupport χ := by
    change y ∈ closure (support χ)
    exact subset_closure hysupport
  exact hχ hysupport'

/-- The adjoint `hormanderAdjointTest` is local in the coefficient fields and multiplier on the open
support neighborhood of its test. -/
theorem hormanderAdjointTest_eq_of_eqOn_open {k N : ℕ} {W : Set (Fin N → ℝ)}
    (hW : IsOpen W) (X Y : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c d φ : (Fin N → ℝ) → ℝ)
    (hXY : ∀ i, EqOn (X i) (Y i) W) (hcd : EqOn c d W)
    (hφW : tsupport φ ⊆ W) (x : Fin N → ℝ) :
    Hormander.Interface.hormanderAdjointTest X c φ x =
      Hormander.Interface.hormanderAdjointTest Y d φ x := by
  by_cases hxW : x ∈ W
  · have hfirst (i : Fin (k + 1)) (x : Fin N → ℝ) (hxW : x ∈ W) :
        Hormander.Interface.euclideanDivergence (fun y => φ y • X i y) x =
          Hormander.Interface.euclideanDivergence (fun y => φ y • Y i y) x := by
      have hnear : (fun y => φ y • X i y) =ᶠ[𝓝 x] (fun y => φ y • Y i y) := by
        filter_upwards [hW.mem_nhds hxW] with y hy
        rw [hXY i hy]
      have hfd := hnear.fderiv_eq (𝕜 := ℝ)
      unfold Hormander.Interface.euclideanDivergence
      rw [hfd]
    have hsecond (i : Fin k) (x : Fin N → ℝ) (hxW : x ∈ W) :
        Hormander.Interface.euclideanDivergence
            (fun y => Hormander.Interface.euclideanDivergence
              (fun z => φ z • X i.succ z) y • X i.succ y) x =
          Hormander.Interface.euclideanDivergence
            (fun y => Hormander.Interface.euclideanDivergence
              (fun z => φ z • Y i.succ z) y • Y i.succ y) x := by
      have hnear :
          (fun y => Hormander.Interface.euclideanDivergence
              (fun z => φ z • X i.succ z) y • X i.succ y) =ᶠ[𝓝 x]
            (fun y => Hormander.Interface.euclideanDivergence
              (fun z => φ z • Y i.succ z) y • Y i.succ y) := by
        filter_upwards [hW.mem_nhds hxW] with y hy
        rw [hfirst i.succ y hy, hXY i.succ hy]
      have hfd := hnear.fderiv_eq (𝕜 := ℝ)
      change (∑ j : Fin N, fderiv ℝ
          (fun y => Hormander.Interface.euclideanDivergence
            (fun z => φ z • X i.succ z) y • X i.succ y)
          x (Hormander.Interface.basisVec j) j) =
        ∑ j : Fin N, fderiv ℝ
          (fun y => Hormander.Interface.euclideanDivergence
            (fun z => φ z • Y i.succ z) y • Y i.succ y)
          x (Hormander.Interface.basisVec j) j
      rw [hfd]
    have hcx : c x = d x := hcd hxW
    simp only [Hormander.Interface.hormanderAdjointTest]
    rw [hfirst 0 x hxW, Finset.sum_congr rfl (fun i _ => hsecond i x hxW), hcx]
  · have hxφ : x ∉ tsupport φ := fun hxφ => hxW (hφW hxφ)
    rw [hormanderAdjointTest_zero_outside X c φ hxφ,
      hormanderAdjointTest_zero_outside Y d φ hxφ]

/-- The adjoint commutes with the carrier transfer. -/
def euclideanAdjointTest₂ {k N : ℕ}
    (X : Fin (k + 1) → E₂ N → E₂ N) (c φ : E₂ N → ℝ) (x : E₂ N) : ℝ :=
  -euclideanDivergence₂ (fun y => φ y • X 0 y) x +
    ∑ i : Fin k,
      euclideanDivergence₂
        (fun y => euclideanDivergence₂ (fun z => φ z • X i.succ z) y • X i.succ y) x +
    c x * φ x

/-- The adjoint `hormanderAdjointTest` commutes with the transfer of fields, multiplier and test
to the Euclidean carrier. -/
theorem hormanderAdjointTest_coordinateConjugate {k N : ℕ}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c φ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    euclideanAdjointTest₂ (pushVectorFields X)
        (fun y => c ((coordinateEquiv N).symm y))
        (fun y => φ ((coordinateEquiv N).symm y)) (coordinateEquiv N x) =
      Hormander.Interface.hormanderAdjointTest X c φ x := by
  let e := coordinateEquiv N
  let φ₂ : E₂ N → ℝ := fun y => φ (e.symm y)
  have hfirst (i : Fin (k + 1)) (x : Fin N → ℝ) :
      euclideanDivergence₂ (fun y => φ₂ y • pushVectorFields X i y) (e x) =
        Hormander.Interface.euclideanDivergence (fun y => φ y • X i y) x := by
    have hpush : pushVectorField (fun y => φ y • X i y) =
        fun y => φ₂ y • pushVectorFields X i y := by
      funext y
      simp only [pushVectorField, pushVectorFields, φ₂]
      rw [map_smul]
    have hdiv := euclideanDivergence_coordinateConjugate (fun y => φ y • X i y) x
    change euclideanDivergence₂ (pushVectorField (fun y => φ y • X i y)) (e x) = _ at hdiv
    rw [hpush] at hdiv
    exact hdiv
  have hsecond (i : Fin k) (x : Fin N → ℝ) :
      euclideanDivergence₂
          (fun y => euclideanDivergence₂ (fun z => φ₂ z • pushVectorFields X i.succ z) y •
            pushVectorFields X i.succ y) (e x) =
        Hormander.Interface.euclideanDivergence
          (fun y => Hormander.Interface.euclideanDivergence
            (fun z => φ z • X i.succ z) y • X i.succ y) x := by
    let S : (Fin N → ℝ) → (Fin N → ℝ) := fun y =>
      Hormander.Interface.euclideanDivergence (fun z => φ z • X i.succ z) y • X i.succ y
    have hpush : pushVectorField S = fun y =>
        euclideanDivergence₂ (fun z => φ₂ z • pushVectorFields X i.succ z) y •
          pushVectorFields X i.succ y := by
      funext y
      change e (S (e.symm y)) = _
      simp only [S]
      rw [map_smul]
      have hf := hfirst i.succ (e.symm y)
      have hf' : euclideanDivergence₂
          (fun z => φ₂ z • pushVectorFields X i.succ z) y =
            Hormander.Interface.euclideanDivergence
              (fun z => φ z • X i.succ z) (e.symm y) := by
        simpa [e] using hf
      rw [← hf']
      rfl
    have hdiv := euclideanDivergence_coordinateConjugate S x
    change euclideanDivergence₂ (pushVectorField S) (e x) = _ at hdiv
    rw [hpush] at hdiv
    exact hdiv
  simp only [euclideanAdjointTest₂, Hormander.Interface.hormanderAdjointTest]
  rw [hfirst 0 x, Finset.sum_congr rfl (fun i _ => hsecond i x)]
  rfl

/-- The complex coordinate-trace divergence used by the Schwartz transpose. -/
def euclideanDivergence₂C {N : ℕ} (V : E₂ N → E₂ N) (φ : E₂ N → ℂ)
    (x : E₂ N) : ℂ :=
  ∑ i : Fin N, fderiv ℝ (fun y => ((V y i : ℝ) : ℂ) * φ y) x
    (EuclideanSpace.single i (1 : ℝ))

/-- On a smooth compactly supported field, the first-order Schwartz transpose is the
negative complex coordinate divergence. -/
theorem vectorFieldTransposeSchwartz_apply_eq_euclideanDivergence₂C {N : ℕ}
    (V : E₂ N → E₂ N) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V)
    (φ : Hormander.B.TestFunction N) (x : E₂ N) :
    vectorFieldTransposeSchwartz V φ x = -euclideanDivergence₂C V φ x := by
  have hcoeff (i : Fin N) :
      (fun y : E₂ N => ((V y i : ℝ) : ℂ)).HasTemperateGrowth := by
    have h := (Hormander.B.complexifyRealSchwartz
      (Hormander.C.c9SchwartzVectorField (fun _ : Fin 1 => V)
        (fun _ => hV) (fun _ => hVc) 0 i)).hasTemperateGrowth
    convert h using 1
    funext y
    simp [Hormander.C.c9SchwartzVectorField_apply,
      Hormander.B.complexifyRealSchwartz_apply_ofRealCLM]
  unfold vectorFieldTransposeSchwartz euclideanDivergence₂C
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    neg_apply, LineDeriv.lineDerivOpCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [Finset.sum_neg_distrib]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i hi
  have hfun : (⇑(SchwartzMap.smulLeftCLM ℂ
      (fun y => ((V y i : ℝ) : ℂ)) φ) : E₂ N → ℂ) =
      fun y => ((V y i : ℝ) : ℂ) * φ y := by
    funext y
    exact SchwartzMap.smulLeftCLM_apply_apply (hcoeff i) φ y
  have hfd := congrArg (fun f : E₂ N → ℂ => fderiv ℝ f x) hfun
  exact congrArg (fun L : E₂ N →L[ℝ] ℂ => L (EuclideanSpace.single i 1)) hfd

/-- Real and imaginary components of the complex divergence are the corresponding real
divergences. -/
theorem euclideanDivergence₂C_re {N : ℕ} (V : E₂ N → E₂ N)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (φ : E₂ N → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : E₂ N) :
    (euclideanDivergence₂C V φ x).re =
      euclideanDivergence₂ (fun y => (φ y).re • V y) x := by
  unfold euclideanDivergence₂C euclideanDivergence₂
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let F : E₂ N → ℂ := fun y => ((V y i : ℝ) : ℂ) * φ y
  let G : E₂ N → ℝ := fun y => (φ y).re * V y i
  have hFG : (fun y => (F y).re) = G := by
    funext y
    simp [F, G, mul_comm]
  have hVcoord : ContDiff ℝ (⊤ : ℕ∞) (fun y => V y i) := by
    simpa [Function.comp_def] using (EuclideanSpace.proj i).contDiff.comp hV
  have hF : DifferentiableAt ℝ F x := by
    exact ((Complex.ofRealCLM.contDiff.comp hVcoord).mul hφ).differentiable
      (by simp) x
  have hG : DifferentiableAt ℝ G x := by
    have hG' := (Complex.reCLM.contDiff.comp hφ).mul hVcoord
    have hG'' : ContDiff ℝ (⊤ : ℕ∞) G := by simpa [G] using hG'
    exact hG''.differentiable (by simp) x
  have hcomp := fderiv_comp x Complex.reCLM.differentiableAt hF
  have hderiv : fderiv ℝ G x = Complex.reCLM.comp (fderiv ℝ F x) := by
    rw [← hFG]
    simpa [Function.comp_def, ContinuousLinearMap.fderiv] using hcomp
  have hEval := congrArg (fun L : E₂ N →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hderiv
  let W : E₂ N → E₂ N := fun y => (φ y).re • V y
  have hW : DifferentiableAt ℝ W x := by
    exact ((Complex.reCLM.contDiff.comp hφ).smul hV).differentiable (by simp) x
  have hcompW := fderiv_comp x (EuclideanSpace.proj i).differentiableAt hW
  have hproj : fderiv ℝ (EuclideanSpace.proj i : E₂ N →L[ℝ] ℝ) (W x) =
      EuclideanSpace.proj i := (EuclideanSpace.proj i : E₂ N →L[ℝ] ℝ).fderiv
  have hcompW' : fderiv ℝ (fun y => W y i) x =
      (EuclideanSpace.proj i).comp (fderiv ℝ W x) := by
    have htmp := hcompW
    rw [hproj] at htmp
    have hfun : (fun y => W y i) = (fun y => (EuclideanSpace.proj i) (W y)) := by
      funext y
      simp
    calc
      _ = fderiv ℝ (fun y => (EuclideanSpace.proj i) (W y)) x :=
        congrArg (fun f : E₂ N → ℝ => fderiv ℝ f x) hfun
      _ = (EuclideanSpace.proj i).comp (fderiv ℝ W x) := by
        simpa only [Function.comp_def] using htmp
  have hGW : G = fun y => W y i := by
    funext y
    simp [G, W, smul_eq_mul]
  have hderivGW := congrArg (fun f : E₂ N → ℝ => fderiv ℝ f x) hGW
  calc
    _ = fderiv ℝ G x (EuclideanSpace.single i 1) := hEval.symm
    _ = fderiv ℝ (fun y => W y i) x (EuclideanSpace.single i 1) :=
      congrArg (fun L : E₂ N →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hderivGW
    _ = (fderiv ℝ W x (EuclideanSpace.single i 1)) i := by
      rw [hcompW']
      rfl

/-- Imaginary components of the complex divergence are the corresponding real divergences. -/
theorem euclideanDivergence₂C_im {N : ℕ} (V : E₂ N → E₂ N)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (φ : E₂ N → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : E₂ N) :
    (euclideanDivergence₂C V φ x).im =
      euclideanDivergence₂ (fun y => (φ y).im • V y) x := by
  unfold euclideanDivergence₂C euclideanDivergence₂
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let F : E₂ N → ℂ := fun y => ((V y i : ℝ) : ℂ) * φ y
  let G : E₂ N → ℝ := fun y => (φ y).im * V y i
  have hFG : (fun y => (F y).im) = G := by
    funext y
    simp [F, G, mul_comm]
  have hVcoord : ContDiff ℝ (⊤ : ℕ∞) (fun y => V y i) := by
    simpa [Function.comp_def] using (EuclideanSpace.proj i).contDiff.comp hV
  have hF : DifferentiableAt ℝ F x := by
    exact ((Complex.ofRealCLM.contDiff.comp hVcoord).mul hφ).differentiable
      (by simp) x
  have hG : DifferentiableAt ℝ G x := by
    have hG' := (Complex.imCLM.contDiff.comp hφ).mul hVcoord
    have hG'' : ContDiff ℝ (⊤ : ℕ∞) G := by simpa [G] using hG'
    exact hG''.differentiable (by simp) x
  have hcomp := fderiv_comp x Complex.imCLM.differentiableAt hF
  have hderiv : fderiv ℝ G x = Complex.imCLM.comp (fderiv ℝ F x) := by
    rw [← hFG]
    simpa [Function.comp_def, ContinuousLinearMap.fderiv] using hcomp
  have hEval := congrArg (fun L : E₂ N →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hderiv
  let W : E₂ N → E₂ N := fun y => (φ y).im • V y
  have hW : DifferentiableAt ℝ W x := by
    exact ((Complex.imCLM.contDiff.comp hφ).smul hV).differentiable (by simp) x
  have hcompW := fderiv_comp x (EuclideanSpace.proj i).differentiableAt hW
  have hproj : fderiv ℝ (EuclideanSpace.proj i : E₂ N →L[ℝ] ℝ) (W x) =
      EuclideanSpace.proj i := (EuclideanSpace.proj i : E₂ N →L[ℝ] ℝ).fderiv
  have hcompW' : fderiv ℝ (fun y => W y i) x =
      (EuclideanSpace.proj i).comp (fderiv ℝ W x) := by
    have htmp := hcompW
    rw [hproj] at htmp
    have hfun : (fun y => W y i) = (fun y => (EuclideanSpace.proj i) (W y)) := by
      funext y
      simp
    calc
      _ = fderiv ℝ (fun y => (EuclideanSpace.proj i) (W y)) x :=
        congrArg (fun f : E₂ N → ℝ => fderiv ℝ f x) hfun
      _ = (EuclideanSpace.proj i).comp (fderiv ℝ W x) := by
        simpa only [Function.comp_def] using htmp
  have hGW : G = fun y => W y i := by
    funext y
    simp [G, W, smul_eq_mul]
  have hderivGW := congrArg (fun f : E₂ N → ℝ => fderiv ℝ f x) hGW
  calc
    _ = fderiv ℝ G x (EuclideanSpace.single i 1) := hEval.symm
    _ = fderiv ℝ (fun y => W y i) x (EuclideanSpace.single i 1) :=
      congrArg (fun L : E₂ N →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hderivGW
    _ = (fderiv ℝ W x (EuclideanSpace.single i 1)) i := by
      rw [hcompW']
      rfl

/-- The real component of the Schwartz transpose of a real vector field is the usual negative
divergence test. -/
theorem vectorFieldTransposeSchwartz_re {N : ℕ}
    (V : E₂ N → E₂ N) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V)
    (φ : Hormander.B.TestFunction N) (x : E₂ N) :
    (vectorFieldTransposeSchwartz V φ x).re =
      -euclideanDivergence₂ (fun y => (φ y).re • V y) x := by
  rw [vectorFieldTransposeSchwartz_apply_eq_euclideanDivergence₂C V hV hVc φ x]
  simp only [Complex.neg_re, euclideanDivergence₂C_re V hV φ (φ.smooth ⊤) x]

/-- Applying the Schwartz transpose twice gives the real second-order formal adjoint on the real
component of its test. -/
theorem vectorFieldTransposeSchwartz_comp_re {N : ℕ}
    (V : E₂ N → E₂ N) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V)
    (φ : Hormander.B.TestFunction N) (x : E₂ N) :
    (vectorFieldTransposeSchwartz V (vectorFieldTransposeSchwartz V φ) x).re =
      euclideanDivergence₂ (fun y =>
        euclideanDivergence₂ (fun z => (φ z).re • V z) y • V y) x := by
  let d : E₂ N → ℝ := fun y => euclideanDivergence₂ (fun z => (φ z).re • V z) y
  have hinner : (fun y => (vectorFieldTransposeSchwartz V φ y).re) = fun y => -d y := by
    funext y
    exact vectorFieldTransposeSchwartz_re V hV hVc φ y
  rw [vectorFieldTransposeSchwartz_re V hV hVc (vectorFieldTransposeSchwartz V φ) x]
  have hfield : (fun y => (vectorFieldTransposeSchwartz V φ y).re • V y) =
      fun y => -(d y • V y) := by
    funext y
    rw [congrFun hinner y]
    simp
  rw [hfield]
  simp [euclideanDivergence₂, d, Finset.sum_neg_distrib]

/-- The imaginary component of the Schwartz transpose of a real vector field is the usual
negative divergence test. -/
theorem vectorFieldTransposeSchwartz_im {N : ℕ}
    (V : E₂ N → E₂ N) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V)
    (φ : Hormander.B.TestFunction N) (x : E₂ N) :
    (vectorFieldTransposeSchwartz V φ x).im =
      -euclideanDivergence₂ (fun y => (φ y).im • V y) x := by
  rw [vectorFieldTransposeSchwartz_apply_eq_euclideanDivergence₂C V hV hVc φ x]
  simp only [Complex.neg_im, euclideanDivergence₂C_im V hV φ (φ.smooth ⊤) x]

/-- Applying the Schwartz transpose twice gives the real second-order formal adjoint on the
imaginary component of its test. -/
theorem vectorFieldTransposeSchwartz_comp_im {N : ℕ}
    (V : E₂ N → E₂ N) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V)
    (φ : Hormander.B.TestFunction N) (x : E₂ N) :
    (vectorFieldTransposeSchwartz V (vectorFieldTransposeSchwartz V φ) x).im =
      euclideanDivergence₂ (fun y =>
        euclideanDivergence₂ (fun z => (φ z).im • V z) y • V y) x := by
  let d : E₂ N → ℝ := fun y => euclideanDivergence₂ (fun z => (φ z).im • V z) y
  have hinner : (fun y => (vectorFieldTransposeSchwartz V φ y).im) = fun y => -d y := by
    funext y
    exact vectorFieldTransposeSchwartz_im V hV hVc φ y
  rw [vectorFieldTransposeSchwartz_im V hV hVc (vectorFieldTransposeSchwartz V φ) x]
  have hfield : (fun y => (vectorFieldTransposeSchwartz V φ y).im • V y) =
      fun y => -(d y • V y) := by
    funext y
    rw [congrFun hinner y]
    simp
  rw [hfield]
  simp [euclideanDivergence₂, d, Finset.sum_neg_distrib]

/-- The real component of the full Schwartz transpose is the copied Euclidean adjoint test. -/
theorem hormanderTransposeSchwartz_re {k N : ℕ}
    (X : Fin (k + 1) → E₂ N → E₂ N) (c : E₂ N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    (φ : Hormander.B.TestFunction N) (x : E₂ N) :
    (hormanderTransposeSchwartz X c φ x).re =
      euclideanAdjointTest₂ X c (fun y => (φ y).re) x := by
  unfold hormanderTransposeSchwartz euclideanAdjointTest₂
  simp only [add_apply, sum_apply,
    ContinuousLinearMap.comp_apply]
  rw [Complex.add_re, Complex.add_re, Complex.re_sum]
  have hsum : (∑ i : Fin k,
      (vectorFieldTransposeSchwartz (X i.succ)
        (vectorFieldTransposeSchwartz (X i.succ) φ) x).re) =
      ∑ i : Fin k, euclideanDivergence₂ (fun y =>
        euclideanDivergence₂ (fun z => (φ z).re • X i.succ z) y • X i.succ y) x := by
    apply Finset.sum_congr rfl
    intro i hi
    exact vectorFieldTransposeSchwartz_comp_re (X i.succ) (hX i.succ) (hXc i.succ) φ x
  have hzero := vectorFieldTransposeSchwartz_re (X 0) (hX 0) (hXc 0) φ x
  have hcoeff : (fun y : E₂ N => ((c y : ℝ) : ℂ)).HasTemperateGrowth := by
    have h := (Hormander.B.complexifyRealSchwartz
      (Hormander.C.c9SchwartzMultiplier c hc hcc)).hasTemperateGrowth
    convert h using 1
    funext y
    simp [Hormander.B.complexifyRealSchwartz_apply]
  rw [hsum, hzero, SchwartzMap.smulLeftCLM_apply_apply hcoeff]
  simp [Complex.mul_re, Complex.ofReal_re]
  ring

/-- The imaginary component of the full Schwartz transpose is the copied Euclidean adjoint test. -/
theorem hormanderTransposeSchwartz_im {k N : ℕ}
    (X : Fin (k + 1) → E₂ N → E₂ N) (c : E₂ N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    (φ : Hormander.B.TestFunction N) (x : E₂ N) :
    (hormanderTransposeSchwartz X c φ x).im =
      euclideanAdjointTest₂ X c (fun y => (φ y).im) x := by
  unfold hormanderTransposeSchwartz euclideanAdjointTest₂
  simp only [add_apply, sum_apply,
    ContinuousLinearMap.comp_apply]
  rw [Complex.add_im, Complex.add_im, Complex.im_sum]
  have hsum : (∑ i : Fin k,
      (vectorFieldTransposeSchwartz (X i.succ)
        (vectorFieldTransposeSchwartz (X i.succ) φ) x).im) =
      ∑ i : Fin k, euclideanDivergence₂ (fun y =>
        euclideanDivergence₂ (fun z => (φ z).im • X i.succ z) y • X i.succ y) x := by
    apply Finset.sum_congr rfl
    intro i hi
    exact vectorFieldTransposeSchwartz_comp_im (X i.succ) (hX i.succ) (hXc i.succ) φ x
  have hzero := vectorFieldTransposeSchwartz_im (X 0) (hX 0) (hXc 0) φ x
  have hcoeff : (fun y : E₂ N => ((c y : ℝ) : ℂ)).HasTemperateGrowth := by
    have h := (Hormander.B.complexifyRealSchwartz
      (Hormander.C.c9SchwartzMultiplier c hc hcc)).hasTemperateGrowth
    convert h using 1
    funext y
    simp [Hormander.B.complexifyRealSchwartz_apply]
  rw [hsum, hzero, SchwartzMap.smulLeftCLM_apply_apply hcoeff]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The full complex Schwartz transpose is determined by its real and imaginary real adjoint
tests. -/
theorem hormanderTransposeSchwartz_eq_components {k N : ℕ}
    (X : Fin (k + 1) → E₂ N → E₂ N) (c : E₂ N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    (φ : Hormander.B.TestFunction N) (x : E₂ N) :
    hormanderTransposeSchwartz X c φ x =
      ((euclideanAdjointTest₂ X c (fun y => (φ y).re) x : ℝ) : ℂ) +
        Complex.I * ((euclideanAdjointTest₂ X c (fun y => (φ y).im) x : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [hormanderTransposeSchwartz_re X c hX hXc hc hcc φ x]
  · simp [hormanderTransposeSchwartz_im X c hX hXc hc hcc φ x]

/-- The Euclidean adjoint of the patch coefficients agrees with `hormanderAdjointTest` on tests
supported inside its ball. -/
theorem euclideanAdjointTest₂_patch_eq {k N : ℕ} (hN : 0 < N)
    {Ω : Set (Fin N → ℝ)} (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c : (Fin N → ℝ) → ℝ) (x₀ : Fin N → ℝ)
    (P : LocalPatch hN (coordinateEquiv N '' Ω) (pushVectorFields X)
      (fun y => c ((coordinateEquiv N).symm y)) (coordinateEquiv N x₀))
    (φ : (Fin N → ℝ) → ℝ)
    (hφ : tsupport φ ⊆ (coordinateEquiv N) ⁻¹' Metric.ball
      (coordinateEquiv N x₀) P.radius) (x : Fin N → ℝ) :
    euclideanAdjointTest₂ P.extendedX P.extendedC
        (fun y => φ ((coordinateEquiv N).symm y)) (coordinateEquiv N x) =
      Hormander.Interface.hormanderAdjointTest X c φ x := by
  let e := coordinateEquiv N
  let W : Set (Fin N → ℝ) := e ⁻¹' Metric.ball (e x₀) P.radius
  let Y : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ) :=
    fun i y => e.symm (P.extendedX i (e y))
  let d : (Fin N → ℝ) → ℝ := fun y => P.extendedC (e y)
  have hW : IsOpen W := by
    exact Metric.isOpen_ball.preimage e.continuous
  have hext (i : Fin (k + 1)) (y : E₂ N) (hy : y ∈ Metric.ball (e x₀) P.radius) :
      P.extendedX i y = pushVectorFields X i y :=
    (P.extendedX_eq_near_ball i).self_of_nhdsSet y (subset_closure hy)
  have hextc (y : E₂ N) (hy : y ∈ Metric.ball (e x₀) P.radius) :
      P.extendedC y = c ((coordinateEquiv N).symm y) :=
    P.extendedC_eq_near_ball.self_of_nhdsSet y (subset_closure hy)
  have hXY : ∀ i, EqOn (X i) (Y i) W := by
    intro i y hy
    have hy' : e y ∈ Metric.ball (e x₀) P.radius := hy
    calc
      X i y = e.symm (pushVectorFields X i (e y)) := by
        simp [pushVectorFields, pushVectorField, e]
      _ = e.symm (P.extendedX i (e y)) := congrArg e.symm (hext i (e y) hy').symm
      _ = Y i y := rfl
  have hcd : EqOn c d W := by
    intro y hy
    have hy' : e y ∈ Metric.ball (e x₀) P.radius := hy
    calc
      c y = c (e.symm (e y)) := by simp
      _ = P.extendedC (e y) := (hextc (e y) hy').symm
      _ = d y := rfl
  have hpush : pushVectorFields Y = P.extendedX := by
    funext i y
    simp [pushVectorFields, pushVectorField, Y, e]
  have hd : (fun y => d (e.symm y)) = P.extendedC := by
    funext y
    simp [d, e]
  have hcoord := hormanderAdjointTest_coordinateConjugate Y d φ x
  have hlocal := hormanderAdjointTest_eq_of_eqOn_open hW X Y c d φ hXY hcd hφ x
  calc
    euclideanAdjointTest₂ P.extendedX P.extendedC (fun y => φ (e.symm y)) (e x) =
        euclideanAdjointTest₂ (pushVectorFields Y) (fun y => d (e.symm y))
          (fun y => φ (e.symm y)) (e x) := by rw [hpush, hd]
    _ = Hormander.Interface.hormanderAdjointTest Y d φ x := hcoord
    _ = Hormander.Interface.hormanderAdjointTest X c φ x := hlocal.symm

/-- The localized product `η g`, transported to `E₂`, is a Schwartz function. The coefficients
of `g` are used only on the open set containing the support of `η`. -/
theorem localizedForcing_schwartz_rhs {N : ℕ} {Ω : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) (g : (Fin N → ℝ) → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
    (η : E₂ N → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ coordinateEquiv N '' Ω) :
    ∃ f : SchwartzMap (E₂ N) ℂ,
      ∀ y, f y = ((η y * g ((coordinateEquiv N).symm y) : ℝ) : ℂ) := by
  let Ω₂ := coordinateEquiv N '' Ω
  let g₂ : E₂ N → ℝ := fun y => g ((coordinateEquiv N).symm y)
  have hΩ₂ : IsOpen Ω₂ := (coordinateEquiv N).toHomeomorph.isOpenMap _ hΩ
  have hpre : (coordinateEquiv N).symm ⁻¹' Ω = Ω₂ := by
    ext y
    change (coordinateEquiv N).symm y ∈ Ω ↔ ∃ x ∈ Ω, coordinateEquiv N x = y
    constructor
    · intro hy
      exact ⟨(coordinateEquiv N).symm y, hy,
        (coordinateEquiv N).apply_symm_apply y⟩
    · rintro ⟨x, hx, hxy⟩
      have heq : (coordinateEquiv N).symm y = x := by
        rw [← hxy]
        exact (coordinateEquiv N).symm_apply_apply x
      rw [heq]
      exact hx
  have hg₂ : ContDiffOn ℝ (⊤ : ℕ∞) g₂ Ω₂ := by
    have hcomp := hg.comp_continuousLinearMap
      ((coordinateEquiv N).symm : E₂ N →L[ℝ] (Fin N → ℝ))
    change ContDiffOn ℝ (⊤ : ℕ∞) (g ∘ (coordinateEquiv N).symm) Ω₂
    rw [← hpre]
    exact hcomp
  have hηg : ContDiff ℝ (⊤ : ℕ∞) (fun y => η y * g₂ y) := by
    rw [← contDiffOn_univ]
    apply isOpen_univ.contDiffOn_iff.mpr
    intro y hy
    by_cases hyΩ : y ∈ Ω₂
    · exact hη.contDiffAt.mul (hg₂.contDiffAt (hΩ₂.mem_nhds hyΩ))
    · have hyK : y ∉ tsupport η := fun hyK => hyΩ (hηΩ hyK)
      have hηzero : η =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
        (notMem_tsupport_iff_eventuallyEq).mp hyK
      have hprod : (fun z => η z * g₂ z) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [hηzero] with z hz
        simp [hz]
      exact contDiffAt_const.congr_of_eventuallyEq hprod
  have hηgCompact : HasCompactSupport (fun y => η y * g₂ y) := hηc.mul_right
  let f : SchwartzMap (E₂ N) ℂ :=
    Hormander.B.complexifyRealSchwartz (hηgCompact.toSchwartzMap hηg)
  refine ⟨f, ?_⟩
  intro y
  simp [f, g₂, Hormander.B.complexifyRealSchwartz_apply]

/-- The cutoff input in the localized forcing statement `LocalizedForcingStatement` is integrable
after transport to the Euclidean carrier. -/
theorem localizedInput_integrable {k N : ℕ} (hN : 0 < N) {Ω : Set (Fin N → ℝ)}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c u : (Fin N → ℝ) → ℝ) (x₀ : Fin N → ℝ)
    (P : LocalPatch hN (coordinateEquiv N '' Ω) (pushVectorFields X)
      (fun y => c ((coordinateEquiv N).symm y)) (coordinateEquiv N x₀))
    (hu : LocallyIntegrableOn u Ω volume)
    (χ : E₂ N → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχball : tsupport χ ⊆ Metric.ball (coordinateEquiv N x₀) P.radius) :
    Integrable (localizedInput χ u) volume := by
  let K : Set (E₂ N) := tsupport χ
  let K₀ : Set (Fin N → ℝ) := (coordinateEquiv N).symm '' K
  let u₂ : E₂ N → ℝ := fun y => u ((coordinateEquiv N).symm y)
  have hKcompact : IsCompact K := by
    exact hχc
  have hKΩ₂ : K ⊆ coordinateEquiv N '' Ω := by
    exact (hχball.trans (subset_closure (s := Metric.ball (coordinateEquiv N x₀) P.radius))).trans
      P.ball_closure_subset
  have hK₀compact : IsCompact K₀ := by
    exact hKcompact.image (coordinateEquiv N).symm.continuous
  have hK₀Ω : K₀ ⊆ Ω := by
    rintro x ⟨y, hy, rfl⟩
    rcases hKΩ₂ hy with ⟨z, hz, hzy⟩
    have : z = (coordinateEquiv N).symm y := by
      simpa using congrArg (coordinateEquiv N).symm hzy
    simpa [this] using hz
  have huK₀ : IntegrableOn u K₀ volume :=
    hu.integrableOn_compact_subset hK₀Ω hK₀compact
  have htransport := (coordinateEquiv_measurePreserving N).integrableOn_image
    (coordinateEquiv N).toHomeomorph.measurableEmbedding (f := u₂) (s := K₀)
  have himage : coordinateEquiv N '' K₀ = K := by
    ext y
    simp [K₀, K]
  have huK : IntegrableOn u₂ K volume := by
    rw [← himage]
    exact htransport.mpr (by simpa [u₂, Function.comp_def] using huK₀)
  have hprodK : IntegrableOn (fun y => χ y * u₂ y) K volume := by
    simpa [mul_comm] using
      huK.mul_continuousOn hχ.continuous.continuousOn hKcompact
  have hprodSupport : support (fun y => χ y * u₂ y) ⊆ K := by
    exact (support_mul_subset_left _ _).trans (subset_tsupport χ)
  have hprod : Integrable (fun y => χ y * u₂ y) volume :=
    (integrableOn_iff_integrable_of_support_subset hprodSupport).mp hprodK
  have hcomplex : Integrable (fun y : E₂ N => ((χ y * u₂ y : ℝ) : ℂ)) volume :=
    Complex.ofRealCLM.integrable_comp hprod
  change Integrable (fun y => ((χ y * u ((coordinateEquiv N).symm y) : ℝ) : ℂ)) volume
  exact hcomplex

private theorem tsupport_re_subset_local {E : Type*} [TopologicalSpace E] (φ : E → ℂ) :
    tsupport (fun x => (φ x).re) ⊆ tsupport φ := by
  change closure (support (fun x => (φ x).re)) ⊆ tsupport φ
  refine closure_minimal ?_ (isClosed_tsupport φ)
  intro x hx
  by_contra hnot
  have hφzero : φ x = 0 := by
    have hxSupport : x ∉ support φ := fun hxs => hnot (subset_tsupport φ hxs)
    simpa only [mem_support, not_not] using hxSupport
  exact (mem_support.mp hx) (by simp [hφzero])

private theorem tsupport_im_subset_local {E : Type*} [TopologicalSpace E] (φ : E → ℂ) :
    tsupport (fun x => (φ x).im) ⊆ tsupport φ := by
  change closure (support (fun x => (φ x).im)) ⊆ tsupport φ
  refine closure_minimal ?_ (isClosed_tsupport φ)
  intro x hx
  by_contra hnot
  have hφzero : φ x = 0 := by
    have hxSupport : x ∉ support φ := fun hxs => hnot (subset_tsupport φ hxs)
    simpa only [mem_support, not_not] using hxSupport
  exact (mem_support.mp hx) (by simp [hφzero])

private theorem tsupport_comp_coordinateEquiv_subset {N : ℕ} (φ : E₂ N → ℂ) :
    tsupport (fun x : Fin N → ℝ => φ (coordinateEquiv N x)) ⊆
      (coordinateEquiv N) ⁻¹' tsupport φ := by
  change closure (support (fun x : Fin N → ℝ => φ (coordinateEquiv N x))) ⊆ _
  refine closure_minimal ?_ ((isClosed_tsupport φ).preimage (coordinateEquiv N).continuous)
  intro x hx
  change coordinateEquiv N x ∈ tsupport φ
  apply subset_tsupport φ
  apply mem_support.mpr
  simpa [Function.comp_def] using (mem_support.mp hx)

/-- A local weak solution supplies exactly the pinned Schwartz localized-forcing identity for
every local patch. -/
theorem localized_forcing_of_weak_equation {k N : ℕ} (hN : 0 < N)
    {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c g u : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (hEq : Hormander.Interface.HasWeakHormanderEquation Ω X c g u)
    (x₀ : Fin N → ℝ)
    (P : LocalPatch hN (coordinateEquiv N '' Ω) (pushVectorFields X)
      (fun y => c ((coordinateEquiv N).symm y)) (coordinateEquiv N x₀)) :
    LocalizedForcingStatement hN X c g u x₀ P := by
  rcases hEq with ⟨hu, hg, hweak⟩
  let e := coordinateEquiv N
  intro χ η hχ hχc hχball hη hηc hηone
  have hηball : tsupport η ⊆ Metric.ball (e x₀) P.radius :=
    localizedTest_tsupport_subset_ball χ η hηone hχball
  have hηΩ : tsupport η ⊆ e '' Ω :=
    hηball.trans (subset_closure.trans P.ball_closure_subset)
  have hv : Integrable (localizedInput χ u) volume :=
    localizedInput_integrable hN X c u x₀ P hu χ hχ hχc hχball
  obtain ⟨f, hfeq⟩ := localizedForcing_schwartz_rhs hΩ g hg η hη hηc hηΩ
  have hηTG : (fun y : E₂ N => ((η y : ℝ) : ℂ)).HasTemperateGrowth := by
    have h := (Hormander.B.complexifyRealSchwartz
      (Hormander.C.c9SchwartzMultiplier η hη hηc)).hasTemperateGrowth
    convert h using 1
    funext y
    simp [Hormander.B.complexifyRealSchwartz_apply]
  have hweakComplex := weakEquation_complexified X c g u ⟨hu, hg, hweak⟩
  refine ⟨hv, f, hfeq, ?_⟩
  ext ψ
  let θ : Hormander.B.TestFunction N :=
    SchwartzMap.smulLeftCLM ℂ (fun y => ((η y : ℝ) : ℂ)) ψ
  let Θ : (Fin N → ℝ) → ℂ := fun x => θ (e x)
  let φR : (Fin N → ℝ) → ℝ := fun x => (Θ x).re
  let φI : (Fin N → ℝ) → ℝ := fun x => (Θ x).im
  have hθpoint (y : E₂ N) : θ y = ((η y : ℝ) : ℂ) * ψ y :=
    SchwartzMap.smulLeftCLM_apply_apply hηTG ψ y
  have hθsupport : tsupport (fun y : E₂ N => θ y) ⊆ tsupport η := by
    have h := SchwartzMap.tsupport_smulLeftCLM_subset
      (fun y : E₂ N => ((η y : ℝ) : ℂ)) ψ
    have hcast : tsupport (fun y : E₂ N => ((η y : ℝ) : ℂ)) ⊆ tsupport η := by
      change closure (support (fun y : E₂ N => ((η y : ℝ) : ℂ))) ⊆
        closure (support η)
      apply closure_mono
      intro y hy
      simpa only [mem_support, Complex.ofReal_ne_zero] using hy
    exact h.trans (Set.inter_subset_right.trans hcast)
  have hθcompact : HasCompactSupport θ := by
    apply HasCompactSupport.of_support_subset_isCompact hηc
    exact (subset_tsupport θ).trans hθsupport
  have hΘsmooth : ContDiff ℝ (⊤ : ℕ∞) Θ := by
    exact (θ.smooth ⊤).comp_continuousLinearMap
      (g := (e : (Fin N → ℝ) →L[ℝ] E₂ N))
  have hΘcompact : HasCompactSupport Θ :=
    hθcompact.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding
  have hΘsupportEta : tsupport Θ ⊆ e ⁻¹' tsupport η := by
    exact (tsupport_comp_coordinateEquiv_subset θ).trans (preimage_mono hθsupport)
  have hΘsupport : tsupport Θ ⊆ Ω := by
    intro x hx
    rcases hηΩ (hΘsupportEta hx) with ⟨z, hz, hze⟩
    have hzx : z = x := e.injective hze
    simpa [hzx] using hz
  have hφRsmooth : ContDiff ℝ (⊤ : ℕ∞) φR :=
    Complex.reCLM.contDiff.comp hΘsmooth
  have hφIsmooth : ContDiff ℝ (⊤ : ℕ∞) φI :=
    Complex.imCLM.contDiff.comp hΘsmooth
  have hφRcompact : HasCompactSupport φR := by
    apply HasCompactSupport.of_support_subset_isCompact hΘcompact
    exact (subset_tsupport φR).trans (tsupport_re_subset_local Θ)
  have hφIcompact : HasCompactSupport φI := by
    apply HasCompactSupport.of_support_subset_isCompact hΘcompact
    exact (subset_tsupport φI).trans (tsupport_im_subset_local Θ)
  have hφRsupport : tsupport φR ⊆ Ω :=
    (tsupport_re_subset_local Θ).trans hΘsupport
  have hφIsupport : tsupport φI ⊆ Ω :=
    (tsupport_im_subset_local Θ).trans hΘsupport
  have hφRball : tsupport φR ⊆ e ⁻¹' Metric.ball (e x₀) P.radius := by
    intro x hx
    exact hηball (hΘsupportEta ((tsupport_re_subset_local Θ) hx))
  have hφIball : tsupport φI ⊆ e ⁻¹' Metric.ball (e x₀) P.radius := by
    intro x hx
    exact hηball (hΘsupportEta ((tsupport_im_subset_local Θ) hx))
  have hweakParts := hweakComplex Θ hΘsmooth hΘcompact hΘsupport
  have hpairR := adjoint_pairing_integrable_and_integral_transfer hΩ X hX c g u
    hc hg hu φR hφRsmooth hφRcompact hφRsupport
  have hpairI := adjoint_pairing_integrable_and_integral_transfer hΩ X hX c g u
    hc hg hu φI hφIsmooth hφIcompact hφIsupport
  have hglobalR : (∫ x, u x * Hormander.Interface.hormanderAdjointTest X c φR x) =
      ∫ x, g x * φR x := by
    calc
      _ = ∫ x in Ω, u x * Hormander.Interface.hormanderAdjointTest X c φR x :=
        hpairR.2.1.symm
      _ = ∫ x in Ω, g x * φR x := by simpa [φR, Θ] using hweakParts.1
      _ = ∫ x, g x * φR x := hpairR.2.2.2
  have hglobalI : (∫ x, u x * Hormander.Interface.hormanderAdjointTest X c φI x) =
      ∫ x, g x * φI x := by
    calc
      _ = ∫ x in Ω, u x * Hormander.Interface.hormanderAdjointTest X c φI x :=
        hpairI.2.1.symm
      _ = ∫ x in Ω, g x * φI x := by simpa [φI, Θ] using hweakParts.2
      _ = ∫ x, g x * φI x := hpairI.2.2.2
  let UR : E₂ N → ℝ := fun y => u (e.symm y) *
    Hormander.Interface.hormanderAdjointTest X c φR (e.symm y)
  let UI : E₂ N → ℝ := fun y => u (e.symm y) *
    Hormander.Interface.hormanderAdjointTest X c φI (e.symm y)
  let VR : E₂ N → ℝ := fun y => g (e.symm y) * φR (e.symm y)
  let VI : E₂ N → ℝ := fun y => g (e.symm y) * φI (e.symm y)
  have hURint : Integrable UR volume := by
    have hcomp := (coordinateEquiv_symm_measurePreserving N).integrable_comp
      hpairR.1.aestronglyMeasurable
    exact hcomp.mpr hpairR.1
  have hUIint : Integrable UI volume := by
    have hcomp := (coordinateEquiv_symm_measurePreserving N).integrable_comp
      hpairI.1.aestronglyMeasurable
    exact hcomp.mpr hpairI.1
  have hVRint : Integrable VR volume := by
    have hcomp := (coordinateEquiv_symm_measurePreserving N).integrable_comp
      hpairR.2.2.1.aestronglyMeasurable
    exact hcomp.mpr hpairR.2.2.1
  have hVIint : Integrable VI volume := by
    have hcomp := (coordinateEquiv_symm_measurePreserving N).integrable_comp
      hpairI.2.2.1.aestronglyMeasurable
    exact hcomp.mpr hpairI.2.2.1
  have hcoordinateR : (∫ y, UR y) = ∫ y, VR y := by
    calc
      _ = ∫ x, u x * Hormander.Interface.hormanderAdjointTest X c φR x := by
        simpa [UR, e] using (integral_comp_coordinateEquiv
          (fun y : E₂ N => u (e.symm y) *
            Hormander.Interface.hormanderAdjointTest X c φR (e.symm y))).symm
      _ = ∫ x, g x * φR x := hglobalR
      _ = ∫ y, VR y := by
        simpa [VR, e] using (integral_comp_coordinateEquiv
          (fun y : E₂ N => g (e.symm y) * φR (e.symm y)))
  have hcoordinateI : (∫ y, UI y) = ∫ y, VI y := by
    calc
      _ = ∫ x, u x * Hormander.Interface.hormanderAdjointTest X c φI x := by
        simpa [UI, e] using (integral_comp_coordinateEquiv
          (fun y : E₂ N => u (e.symm y) *
            Hormander.Interface.hormanderAdjointTest X c φI (e.symm y))).symm
      _ = ∫ x, g x * φI x := hglobalI
      _ = ∫ y, VI y := by
        simpa [VI, e] using (integral_comp_coordinateEquiv
          (fun y : E₂ N => g (e.symm y) * φI (e.symm y)))
  have hpatchR (y : E₂ N) :
      euclideanAdjointTest₂ P.extendedX P.extendedC (fun z => (θ z).re) y =
        Hormander.Interface.hormanderAdjointTest X c φR (e.symm y) := by
    have h := euclideanAdjointTest₂_patch_eq hN X c x₀ P φR hφRball (e.symm y)
    simpa [φR, Θ, e] using h
  have hpatchI (y : E₂ N) :
      euclideanAdjointTest₂ P.extendedX P.extendedC (fun z => (θ z).im) y =
        Hormander.Interface.hormanderAdjointTest X c φI (e.symm y) := by
    have h := euclideanAdjointTest₂_patch_eq hN X c x₀ P φI hφIball (e.symm y)
    simpa [φI, Θ, e] using h
  have htranspose (y : E₂ N) :
      hormanderTransposeSchwartz P.extendedX P.extendedC θ y =
        ((euclideanAdjointTest₂ P.extendedX P.extendedC (fun z => (θ z).re) y : ℝ) : ℂ) +
          Complex.I * ((euclideanAdjointTest₂ P.extendedX P.extendedC
            (fun z => (θ z).im) y : ℝ) : ℂ) :=
    hormanderTransposeSchwartz_eq_components P.extendedX P.extendedC P.extendedX_smooth
      P.extendedX_compact P.extendedC_smooth P.extendedC_compact θ y
  have hchiOn (y : E₂ N) (hy : y ∈ tsupport η) : χ y = 1 :=
    hηone.self_of_nhdsSet y hy
  have hrealSupportEta : tsupport φR ⊆ e ⁻¹' tsupport η :=
    (tsupport_re_subset_local Θ).trans hΘsupportEta
  have himagSupportEta : tsupport φI ⊆ e ⁻¹' tsupport η :=
    (tsupport_im_subset_local Θ).trans hΘsupportEta
  have hleftPoint (y : E₂ N) :
      hormanderTransposeSchwartz P.extendedX P.extendedC θ y *
          localizedInput χ u y =
        ((UR y : ℝ) : ℂ) + Complex.I * ((UI y : ℝ) : ℂ) := by
    rw [htranspose y, hpatchR y, hpatchI y]
    by_cases hy : y ∈ tsupport η
    · simp [UR, UI, localizedInput, e, coordinateEquiv_symm_apply, hchiOn y hy]
      ring_nf
    · have hRnot : e.symm y ∉ tsupport φR := by
        intro h
        exact hy (hrealSupportEta h)
      have hInot : e.symm y ∉ tsupport φI := by
        intro h
        exact hy (himagSupportEta h)
      have hRzero : Hormander.Interface.hormanderAdjointTest X c φR (e.symm y) = 0 :=
        hormanderAdjointTest_zero_outside X c φR hRnot
      have hIzero : Hormander.Interface.hormanderAdjointTest X c φI (e.symm y) = 0 :=
        hormanderAdjointTest_zero_outside X c φI hInot
      simp [UR, UI, localizedInput, hRzero, hIzero]
  have hrightPoint (y : E₂ N) :
      ψ y * f y = ((VR y : ℝ) : ℂ) + Complex.I * ((VI y : ℝ) : ℂ) := by
    rw [hfeq y]
    change ψ y * ((η y * g (e.symm y) : ℝ) : ℂ) =
      ((g (e.symm y) * (θ y).re : ℝ) : ℂ) +
        Complex.I * ((g (e.symm y) * (θ y).im : ℝ) : ℂ)
    rw [hθpoint y]
    apply Complex.ext
    · simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    · simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
  have hleftSumInt : Integrable
      (fun y : E₂ N => ((UR y : ℝ) : ℂ) + Complex.I * ((UI y : ℝ) : ℂ)) volume := by
    exact (Complex.ofRealCLM.integrable_comp hURint).add
      ((Complex.ofRealCLM.integrable_comp hUIint).const_mul Complex.I)
  have hrightSumInt : Integrable
      (fun y : E₂ N => ((VR y : ℝ) : ℂ) + Complex.I * ((VI y : ℝ) : ℂ)) volume := by
    exact (Complex.ofRealCLM.integrable_comp hVRint).add
      ((Complex.ofRealCLM.integrable_comp hVIint).const_mul Complex.I)
  have hleftInt : Integrable
      (fun y : E₂ N => hormanderTransposeSchwartz
        P.extendedX P.extendedC θ y * localizedInput χ u y) volume :=
    hleftSumInt.congr (Filter.Eventually.of_forall fun y => (hleftPoint y).symm)
  have hrightInt : Integrable (fun y : E₂ N => ψ y * f y) volume :=
    hrightSumInt.congr (Filter.Eventually.of_forall fun y => (hrightPoint y).symm)
  have hdistributionIntegral :
      (∫ y, hormanderTransposeSchwartz P.extendedX P.extendedC θ y *
        localizedInput χ u y) = ∫ y, ψ y * f y := by
    apply Complex.ext
    · calc
        (∫ y, hormanderTransposeSchwartz P.extendedX P.extendedC θ y *
            localizedInput χ u y).re =
          ∫ y, (hormanderTransposeSchwartz P.extendedX P.extendedC θ y *
            localizedInput χ u y).re := (integral_re hleftInt).symm
        _ = ∫ y, UR y := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by simp [hleftPoint y]
        _ = ∫ y, VR y := hcoordinateR
        _ = ∫ y, (ψ y * f y).re := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by simp [hrightPoint y]
        _ = (∫ y, ψ y * f y).re := integral_re hrightInt
    · calc
        (∫ y, hormanderTransposeSchwartz P.extendedX P.extendedC θ y *
            localizedInput χ u y).im =
          ∫ y, (hormanderTransposeSchwartz P.extendedX P.extendedC θ y *
            localizedInput χ u y).im := (integral_im hleftInt).symm
        _ = ∫ y, UI y := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by simp [hleftPoint y]
        _ = ∫ y, VI y := hcoordinateI
        _ = ∫ y, (ψ y * f y).im := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by simp [hrightPoint y]
        _ = (∫ y, ψ y * f y).im := integral_im hrightInt
  calc
    (TemperedDistribution.smulLeftCLM ℂ (fun y => ((η y : ℝ) : ℂ))
        (Hormander.hormanderOp P.extendedX P.extendedC
          (Lp.toTemperedDistribution (hv.toL1 (localizedInput χ u))))) ψ =
        ∫ y, hormanderTransposeSchwartz P.extendedX P.extendedC θ y *
          localizedInput χ u y := by
      rw [TemperedDistribution.smulLeftCLM_apply_apply,
        hormanderOp_apply_transpose, Lp.toTemperedDistribution_apply]
      simp only [smul_eq_mul]
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toL1] with y hy
      rw [hy]
    _ = ∫ y, ψ y * f y := hdistributionIntegral
    _ = (f : 𝓢'(E₂ N, ℂ)) ψ := by
      rw [Hormander.B.testToTempered_apply]
      simp [Hormander.B.bilinearPairing]

end Hormander.F
