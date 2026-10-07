-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Extension.Localized
public import Hormander.B.Calculus.TransposeAlgebra
public import Hormander.A.Mollifier.FourierConvolution

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate FourierTransform

namespace Hormander.B

theorem bilinearPairing_add_left {N : ℕ} (u v w : TestFunction N) :
    bilinearPairing (u + v) w = bilinearPairing u w + bilinearPairing v w := by
  unfold bilinearPairing
  rw [← integral_add (integrable_mul_test u w) (integrable_mul_test v w)]
  congr 1; funext x; simp [add_mul]

theorem bilinearPairing_add_right {N : ℕ} (u v w : TestFunction N) :
    bilinearPairing u (v + w) = bilinearPairing u v + bilinearPairing u w := by
  unfold bilinearPairing
  rw [← integral_add (integrable_mul_test u v) (integrable_mul_test u w)]
  congr 1; funext x; simp [mul_add]

theorem bilinearPairing_smul_left {N : ℕ} (c : ℂ) (u v : TestFunction N) :
    bilinearPairing (c • u) v = c * bilinearPairing u v := by
  unfold bilinearPairing
  rw [← integral_const_mul]
  congr 1; funext x; simp [mul_assoc]

theorem bilinearPairing_smul_right {N : ℕ} (c : ℂ) (u v : TestFunction N) :
    bilinearPairing u (c • v) = c * bilinearPairing u v := by
  unfold bilinearPairing
  rw [← integral_const_mul]
  congr 1; funext x; simp; ring

theorem HasBilinearTranspose.add {N : ℕ} {A At B Bt : Operator N}
    (hA : HasBilinearTranspose A At) (hB : HasBilinearTranspose B Bt) :
    HasBilinearTranspose (A + B) (At + Bt) := by
  intro u v
  simp only [LinearMap.add_apply, bilinearPairing_add_left, bilinearPairing_add_right, hA u v, hB u v]

theorem HasBilinearTranspose.smul {N : ℕ} {A At : Operator N} (c : ℂ)
    (hA : HasBilinearTranspose A At) : HasBilinearTranspose (c • A) (c • At) := by
  intro u v
  simp only [LinearMap.smul_apply, bilinearPairing_smul_left, bilinearPairing_smul_right, hA u v]

theorem HasBilinearTranspose.id {N : ℕ} : HasBilinearTranspose (LinearMap.id : Operator N) LinearMap.id :=
  fun _ _ => rfl

theorem HasBilinearTranspose.zero {N : ℕ} : HasBilinearTranspose (0 : Operator N) 0 := by
  intro u v
  simp [bilinearPairing]

/-- The operator has a bilinear transpose, and both are continuous on `𝓢`. -/
def HasContinuousTranspose {N : ℕ} (T : Operator N) : Prop :=
  ∃ Tt : Operator N, HasBilinearTranspose T Tt ∧
    Continuous (fun u : TestFunction N => T u) ∧ Continuous (fun u : TestFunction N => Tt u)

theorem HasContinuousTranspose.id {N : ℕ} : HasContinuousTranspose (LinearMap.id : Operator N) :=
  ⟨LinearMap.id, HasBilinearTranspose.id, continuous_id, continuous_id⟩

theorem HasContinuousTranspose.zero {N : ℕ} : HasContinuousTranspose (0 : Operator N) :=
  ⟨0, HasBilinearTranspose.zero, continuous_const, continuous_const⟩

theorem HasContinuousTranspose.comp {N : ℕ} {A B : Operator N}
    (hA : HasContinuousTranspose A) (hB : HasContinuousTranspose B) :
    HasContinuousTranspose (A.comp B) := by
  obtain ⟨At, hAt, hAc, hAtc⟩ := hA
  obtain ⟨Bt, hBt, hBc, hBtc⟩ := hB
  exact ⟨Bt.comp At, bilinearTranspose_comp hAt hBt, hAc.comp hBc, hBtc.comp hAtc⟩

theorem HasContinuousTranspose.add {N : ℕ} {A B : Operator N}
    (hA : HasContinuousTranspose A) (hB : HasContinuousTranspose B) :
    HasContinuousTranspose (A + B) := by
  obtain ⟨At, hAt, hAc, hAtc⟩ := hA
  obtain ⟨Bt, hBt, hBc, hBtc⟩ := hB
  exact ⟨At + Bt, hAt.add hBt, hAc.add hBc, hAtc.add hBtc⟩

theorem HasContinuousTranspose.smul {N : ℕ} {A : Operator N} (c : ℂ)
    (hA : HasContinuousTranspose A) : HasContinuousTranspose (c • A) := by
  obtain ⟨At, hAt, hAc, hAtc⟩ := hA
  exact ⟨c • At, hAt.smul c, hAc.const_smul c, hAtc.const_smul c⟩

theorem HasContinuousTranspose.sum {N : ℕ} {ι : Type*} (I : Finset ι) (T : ι → Operator N)
    (h : ∀ i ∈ I, HasContinuousTranspose (T i)) : HasContinuousTranspose (∑ i ∈ I, T i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using HasContinuousTranspose.zero (N := N)
  | insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i I)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem multiplierOperator_apply_continuity {N : ℕ} (g : SchwartzMap (Carrier N) ℂ) (u : TestFunction N)
    (x : Carrier N) : multiplierOperator g u x = g x * u x := by
  simp [multiplierOperator, SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]

/-- A Schwartz multiplier is self-transpose. -/
theorem multiplierOperator_transpose {N : ℕ} (g : SchwartzMap (Carrier N) ℂ) :
    HasBilinearTranspose (multiplierOperator g) (multiplierOperator g) := by
  intro u v
  unfold bilinearPairing
  apply integral_congr_ae
  filter_upwards with x
  rw [multiplierOperator_apply_continuity, multiplierOperator_apply_continuity]
  ring

/-- Multiplication by a Schwartz function is continuous on `𝓢`. -/
theorem multiplierOperator_continuous {N : ℕ} (g : SchwartzMap (Carrier N) ℂ) :
    Continuous (fun u : TestFunction N => multiplierOperator g u) :=
  (SchwartzMap.smulLeftCLM ℂ (⇑g)).continuous

theorem multiplierOperator_hasContinuousTranspose {N : ℕ} (g : SchwartzMap (Carrier N) ℂ) :
    HasContinuousTranspose (multiplierOperator g) :=
  ⟨_, multiplierOperator_transpose g, multiplierOperator_continuous g,
    multiplierOperator_continuous g⟩

theorem realMultiplierOperator_hasContinuousTranspose {N : ℕ} (g : SchwartzMap (Carrier N) ℝ) :
    HasContinuousTranspose (realMultiplierOperator g) :=
  multiplierOperator_hasContinuousTranspose _

theorem coordinateDerivative_apply {N : ℕ} (i : Fin N) (u : TestFunction N) (x : Carrier N) :
    coordinateDerivative i u x = fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) := rfl

/-- Coordinate derivatives are continuous on `𝓢`. -/
theorem coordinateDerivative_continuous {N : ℕ} (i : Fin N) :
    Continuous (fun u : TestFunction N => coordinateDerivative i u) :=
  (LineDeriv.lineDerivOpCLM ℂ (TestFunction N) (EuclideanSpace.single i (1 : ℝ))).continuous

/-- `∂ᵢᵗ = −∂ᵢ`. -/
theorem coordinateDerivative_transpose {N : ℕ} (i : Fin N) :
    HasBilinearTranspose (coordinateDerivative i) (-coordinateDerivative i) := by
  intro u v
  unfold bilinearPairing
  have h := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume) v u
    (EuclideanSpace.single i (1 : ℝ))
  have e1 : ∀ (w : TestFunction N) x, coordinateDerivative i w x =
      (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) w) x := fun w x => rfl
  calc ∫ x, coordinateDerivative i u x * v x = ∫ x, v x * (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) u) x := by
        apply integral_congr_ae; filter_upwards with x; rw [e1 u]; ring
    _ = -∫ x, (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) v) x * u x := h
    _ = _ := by
        rw [← integral_neg]
        apply integral_congr_ae; filter_upwards with x
        have : ((-coordinateDerivative i) v) x = -(coordinateDerivative i v x) := rfl
        rw [this, e1 v]
        ring

/-- A Fourier multiplier with even temperate symbol is self-transpose
for the bilinear pairing. -/
theorem fourierMultiplier_transpose {N : ℕ} (m : Carrier N → ℂ) (hm : m.HasTemperateGrowth)
    (heven : ∀ ξ, m (-ξ) = m ξ) :
    HasBilinearTranspose (SchwartzMap.fourierMultiplierCLM ℂ m).toLinearMap
      (SchwartzMap.fourierMultiplierCLM ℂ m).toLinearMap := by
  intro u v
  have key : ∀ u v : TestFunction N, bilinearPairing (SchwartzMap.fourierMultiplierCLM ℂ m u) v =
      ∫ x, m x * 𝓕 u x * 𝓕⁻ v x := by
    intro u v
    unfold bilinearPairing
    rw [SchwartzMap.fourierMultiplierCLM_apply]
    have := SchwartzMap.integral_fourierInv_mul_eq (SchwartzMap.smulLeftCLM ℂ m (𝓕 u)) v
    refine this.trans ?_
    apply integral_congr_ae
    filter_upwards with x
    rw [SchwartzMap.smulLeftCLM_apply_apply hm]
    simp [smul_eq_mul]
  show bilinearPairing (SchwartzMap.fourierMultiplierCLM ℂ m u) v =
    bilinearPairing u (SchwartzMap.fourierMultiplierCLM ℂ m v)
  rw [key u v, bilinearPairing_comm u, key v u]
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards with x
  have h1 : 𝓕⁻ v (-x) = 𝓕 v x := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg]; rfl
  have h2 : 𝓕⁻ u x = 𝓕 u (-x) := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]; rfl
  rw [h1, h2, heven]
  ring

theorem lambdaOperator_continuous {N : ℕ} (s : ℝ) :
    Continuous (fun u : TestFunction N => lambdaOperator s u) :=
  (SchwartzMap.fourierMultiplierCLM ℂ
    (fun ξ : Carrier N => Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2)))).continuous

/-- `Λ^s` is self-transpose. -/
theorem lambdaOperator_transpose {N : ℕ} (s : ℝ) :
    HasBilinearTranspose (lambdaOperator (N := N) s) (lambdaOperator s) :=
  fourierMultiplier_transpose _ (Hormander.A.besselSymbol_hasTemperateGrowth s)
    (fun ξ => by simp [norm_neg])

theorem lambdaOperator_hasContinuousTranspose {N : ℕ} (s : ℝ) :
    HasContinuousTranspose (lambdaOperator (N := N) s) :=
  ⟨_, lambdaOperator_transpose s, lambdaOperator_continuous s, lambdaOperator_continuous s⟩

/-- The mollifier on `𝓢` as an operator. -/
def mollifierOperator (N : ℕ) (δ : ℝ) (hδ : 0 < δ) : Operator N :=
  (Hormander.A.SδSchwartz N δ hδ).toLinearMap

theorem fourier_mollifierOperator {N : ℕ} (δ : ℝ) (hδ : 0 < δ) (ψ : TestFunction N) :
    𝓕 (mollifierOperator N δ hδ ψ) =
      SchwartzMap.smulLeftCLM ℂ (fun ξ => 𝓕 (Hormander.A.Jδ N δ hδ) ξ) (𝓕 ψ) := by
  ext ξ
  unfold mollifierOperator
  simp only [ContinuousLinearMap.coe_coe]
  rw [Hormander.A.SδSchwartz_eq_convolution, SchwartzMap.fourier_convolution]
  rw [SchwartzMap.pairing_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply (𝓕 (Hormander.A.Jδ N δ hδ)).hasTemperateGrowth]
  simp [smul_eq_mul, mul_comm]

theorem mollifierOperator_eq_fourierMultiplier {N : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    mollifierOperator N δ hδ =
      (SchwartzMap.fourierMultiplierCLM ℂ (fun ξ : Carrier N => 𝓕 (Hormander.A.Jδ N δ hδ) ξ)).toLinearMap := by
  apply LinearMap.ext
  intro ψ
  apply Hormander.A.fourier_schwartz_bijective.1
  simp only [SchwartzMap.fourierTransformCLM_apply]
  rw [fourier_mollifierOperator]
  simp only [ContinuousLinearMap.coe_coe, SchwartzMap.fourierMultiplierCLM_apply]
  exact (FourierTransform.fourier_fourierInv_eq _).symm

/-- The mollifier `S_δ` is continuous on `𝓢`. -/
theorem mollifierOperator_continuous {N : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    Continuous (fun u : TestFunction N => mollifierOperator N δ hδ u) :=
  (Hormander.A.SδSchwartz N δ hδ).continuous

/-- The mollifier `S_δ` is self-transpose (even kernel). -/
theorem mollifierOperator_transpose {N : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    HasBilinearTranspose (mollifierOperator N δ hδ) (mollifierOperator N δ hδ) := by
  rw [mollifierOperator_eq_fourierMultiplier]
  exact fourierMultiplier_transpose _ (𝓕 (Hormander.A.Jδ N δ hδ)).hasTemperateGrowth
    (fun ξ => Hormander.A.fourier_even_of_even _ (Hormander.A.Jδ_even δ hδ) ξ)

theorem mollifierOperator_hasContinuousTranspose {N : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    HasContinuousTranspose (mollifierOperator N δ hδ) :=
  ⟨_, mollifierOperator_transpose δ hδ, mollifierOperator_continuous δ hδ,
    mollifierOperator_continuous δ hδ⟩

theorem coordinateDerivative_hasContinuousTranspose {N : ℕ} (i : Fin N) :
    HasContinuousTranspose (coordinateDerivative i) :=
  ⟨_, coordinateDerivative_transpose i, coordinateDerivative_continuous i,
    (coordinateDerivative_continuous i).neg⟩

/-- Leibniz rule for a Schwartz multiplier and a coordinate derivative. -/
theorem coordinateDerivative_multiplier {N : ℕ} (i : Fin N) (g : SchwartzMap (Carrier N) ℂ) :
    (coordinateDerivative i).comp (multiplierOperator g) =
      (multiplierOperator g).comp (coordinateDerivative i) +
        multiplierOperator (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) g) := by
  apply LinearMap.ext
  intro u
  ext x
  rw [LinearMap.comp_apply, LinearMap.add_apply, add_apply, coordinateDerivative_apply,
    LinearMap.comp_apply, multiplierOperator_apply_continuity, multiplierOperator_apply_continuity, coordinateDerivative_apply]
  have hg := g.hasFDerivAt x
  have hu := u.hasFDerivAt x
  have hprod : fderiv ℝ (⇑(multiplierOperator g u)) x =
      g x • fderiv ℝ u x + u x • fderiv ℝ g x := by
    have : (⇑(multiplierOperator g u)) = fun y => g y * u y := by
      funext y; exact multiplierOperator_apply_continuity g u y
    rw [this]
    exact (hg.mul hu).fderiv
  rw [hprod]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have : (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) g) x =
      fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)) := rfl
  rw [this]
  ring

theorem complexifyRealSchwartz_apply_ofRealCLM {N : ℕ} (f : SchwartzMap (Carrier N) ℝ) (y : Carrier N) :
    complexifyRealSchwartz f y = Complex.ofRealCLM (f y) := by
  simp [complexifyRealSchwartz]

theorem complexify_lineDeriv {N : ℕ} (v : Carrier N) (g : SchwartzMap (Carrier N) ℝ) :
    complexifyRealSchwartz (LineDeriv.lineDerivOp v g) =
      LineDeriv.lineDerivOp v (complexifyRealSchwartz g) := by
  ext x
  have hc : ∀ y, complexifyRealSchwartz g y = Complex.ofRealCLM (g y) :=
    complexifyRealSchwartz_apply_ofRealCLM g
  have h1 : (⇑(complexifyRealSchwartz g) : Carrier N → ℂ) = fun y => Complex.ofRealCLM (g y) := by
    funext y; exact hc y
  have h2 : fderiv ℝ (⇑(complexifyRealSchwartz g)) x = Complex.ofRealCLM.comp (fderiv ℝ g x) := by
    rw [h1]
    exact (Complex.ofRealCLM.hasFDerivAt.comp x (g.hasFDerivAt x)).fderiv
  have e1 : (LineDeriv.lineDerivOp v (complexifyRealSchwartz g)) x =
      fderiv ℝ (⇑(complexifyRealSchwartz g)) x v := rfl
  have e2 : (LineDeriv.lineDerivOp v g) x = fderiv ℝ g x v := rfl
  rw [e1, h2, complexifyRealSchwartz_apply_ofRealCLM, e2]
  rfl

/-- The divergence of a real Schwartz vector field. -/
def vectorFieldDivergence {N : ℕ} (V : RealSchwartzVectorField N) : SchwartzMap (Carrier N) ℝ :=
  ∑ i : Fin N, LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (V i)

theorem realMultiplierOperator_sum {N : ℕ} (g : Fin N → SchwartzMap (Carrier N) ℝ) :
    realMultiplierOperator (∑ i, g i) = ∑ i, realMultiplierOperator (g i) := by
  apply LinearMap.ext
  intro u
  ext x
  simp [realMultiplierOperator, multiplierOperator_apply_continuity, complexifyRealSchwartz,
    Finset.sum_mul, map_sum]

theorem HasBilinearTranspose.sum {N : ℕ} {ι : Type*} (I : Finset ι) (T Tt : ι → Operator N)
    (h : ∀ i ∈ I, HasBilinearTranspose (T i) (Tt i)) :
    HasBilinearTranspose (∑ i ∈ I, T i) (∑ i ∈ I, Tt i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using HasBilinearTranspose.zero (N := N)
  | insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i I)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- `Xᵗ = −X − div X` for a real Schwartz vector field `X`. -/
theorem vectorFieldOperator_transpose {N : ℕ} (V : RealSchwartzVectorField N) :
    HasBilinearTranspose (vectorFieldOperator V)
      (-(vectorFieldOperator V) - realMultiplierOperator (vectorFieldDivergence V)) := by
  have h1 : HasBilinearTranspose (vectorFieldOperator V)
      (∑ i : Fin N, (-(coordinateDerivative i)).comp (realMultiplierOperator (V i))) := by
    unfold vectorFieldOperator
    exact HasBilinearTranspose.sum _ _ _ (fun i _ =>
      bilinearTranspose_comp (multiplierOperator_transpose _) (coordinateDerivative_transpose i))
  have h2 : (∑ i : Fin N, (-(coordinateDerivative i)).comp (realMultiplierOperator (V i))) =
      -(vectorFieldOperator V) - realMultiplierOperator (vectorFieldDivergence V) := by
    unfold vectorFieldOperator vectorFieldDivergence
    rw [realMultiplierOperator_sum]
    have hterm : ∀ i : Fin N, (-(coordinateDerivative i)).comp (realMultiplierOperator (V i)) =
        -((realMultiplierOperator (V i)).comp (coordinateDerivative i)) -
          realMultiplierOperator (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (V i)) := by
      intro i
      have hL := coordinateDerivative_multiplier i (complexifyRealSchwartz (V i))
      rw [realMultiplierOperator, ← complexify_lineDeriv] at *
      simp only [LinearMap.neg_comp, realMultiplierOperator] 
      rw [hL]
      abel
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [← h2]
  exact h1

theorem vectorFieldOperator_hasContinuousTranspose {N : ℕ} (V : RealSchwartzVectorField N) :
    HasContinuousTranspose (vectorFieldOperator V) := by
  unfold vectorFieldOperator
  exact HasContinuousTranspose.sum _ _ (fun i _ =>
    (realMultiplierOperator_hasContinuousTranspose (V i)).comp
      (coordinateDerivative_hasContinuousTranspose i))

/-- The transpose of an operator with a continuous transpose is continuous, whichever
transpose witness is used (transposes are unique). -/
theorem HasContinuousTranspose.transpose_continuous {N : ℕ} {T Tt : Operator N}
    (h : HasContinuousTranspose T) (hT : HasBilinearTranspose T Tt) :
    Continuous (fun u : TestFunction N => Tt u) := by
  obtain ⟨Tt', hT', _, hc'⟩ := h
  have : Tt' = Tt := HasBilinearTranspose.unique hT' hT
  subst this
  exact hc'

/-- The continuity of the explicit transpose `Xᵗ = −X − div X`. -/
theorem vectorFieldOperator_transpose_continuous {N : ℕ} (V : RealSchwartzVectorField N) :
    Continuous (fun u : TestFunction N =>
      (-(vectorFieldOperator V) - realMultiplierOperator (vectorFieldDivergence V)) u) :=
  (vectorFieldOperator_hasContinuousTranspose V).transpose_continuous
    (vectorFieldOperator_transpose V)

end Hormander.B
