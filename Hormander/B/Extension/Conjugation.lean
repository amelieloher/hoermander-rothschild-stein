-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Order
public import Hormander.A.Scale.Duality
public import Mathlib.Analysis.Calculus.FDeriv.Star

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate FourierTransform

namespace Hormander.B

/-- Complex conjugation `K f = f̄` on Schwartz test functions. -/
def conjTest {N : ℕ} (u : TestFunction N) : TestFunction N := Hormander.A.starSchwartz u

@[simp] theorem conjTest_apply {N : ℕ} (u : TestFunction N) (x : Carrier N) :
    conjTest u x = conj (u x) := Hormander.A.starSchwartz_apply u x

@[simp] theorem conjTest_conjTest {N : ℕ} (u : TestFunction N) : conjTest (conjTest u) = u := by
  ext x; simp

theorem conjTest_add {N : ℕ} (u v : TestFunction N) :
    conjTest (u + v) = conjTest u + conjTest v := by
  ext x; simp

theorem conjTest_smul {N : ℕ} (c : ℂ) (u : TestFunction N) :
    conjTest (c • u) = conj c • conjTest u := by
  ext x; simp

theorem conjTest_sub {N : ℕ} (u v : TestFunction N) :
    conjTest (u - v) = conjTest u - conjTest v := by
  ext x; simp

/-- `K` is an isometry of every Sobolev norm on `𝓢`. -/
theorem sobolevNorm_conjTest {N : ℕ} (s : ℝ) (u : TestFunction N) :
    sobolevNorm s (conjTest u) = sobolevNorm s u := by
  rw [sobolevNorm_eq_schwartzToSobolev_norm, sobolevNorm_eq_schwartzToSobolev_norm]
  exact Hormander.A.norm_schwartzToSobolev_star s u

/-- Conjugate an operator: `T ↦ K T K`. -/
def conjOperator {N : ℕ} (T : Operator N) : Operator N where
  toFun u := conjTest (T (conjTest u))
  map_add' u v := by rw [conjTest_add, map_add, conjTest_add]
  map_smul' c u := by
    rw [conjTest_smul, map_smul, conjTest_smul]
    simp

@[simp] theorem conjOperator_apply {N : ℕ} (T : Operator N) (u : TestFunction N) :
    conjOperator T u = conjTest (T (conjTest u)) := rfl

theorem conjOperator_comp {N : ℕ} (A B : Operator N) :
    conjOperator (A.comp B) = (conjOperator A).comp (conjOperator B) := by
  ext u x; simp

theorem conjOperator_add {N : ℕ} (A B : Operator N) :
    conjOperator (A + B) = conjOperator A + conjOperator B := by
  ext u x; simp [conjTest_add]

theorem conjOperator_sub {N : ℕ} (A B : Operator N) :
    conjOperator (A - B) = conjOperator A - conjOperator B := by
  ext u x; simp [conjTest_sub]

theorem conjOperator_sum {N : ℕ} {ι : Type*} (I : Finset ι) (T : ι → Operator N) :
    conjOperator (∑ i ∈ I, T i) = ∑ i ∈ I, conjOperator (T i) := by
  classical
  induction I using Finset.induction_on with
  | empty => ext u x; simp
  | insert i I hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, conjOperator_add, ih]

/-- Conjugation preserves the order class, with the same constants. -/
theorem HasOrder.conj {N : ℕ} {m : ℝ} {T : Operator N} (h : HasOrder m T) :
    HasOrder m (conjOperator T) := by
  intro s
  obtain ⟨C, hC⟩ := h s
  refine ⟨C, fun u => ?_⟩
  rw [conjOperator_apply, sobolevNorm_conjTest]
  have := hC (conjTest u)
  rwa [sobolevNorm_conjTest] at this

theorem bilinearPairing_conjTest {N : ℕ} (u v : TestFunction N) :
    bilinearPairing (conjTest u) (conjTest v) = conj (bilinearPairing u v) := by
  unfold bilinearPairing
  rw [← integral_conj]
  simp

/-- `(K T K)^t = K T^t K`. -/
theorem HasBilinearTranspose.conj {N : ℕ} {T Tt : Operator N} (h : HasBilinearTranspose T Tt) :
    HasBilinearTranspose (conjOperator T) (conjOperator Tt) := by
  intro u v
  have h1 := h (conjTest u) (conjTest v)
  simp only [conjOperator_apply]
  have h2 := congrArg conj h1
  rw [← bilinearPairing_conjTest, ← bilinearPairing_conjTest, conjTest_conjTest] at h2
  rw [conjTest_conjTest] at h2
  exact h2

/-- Real Schwartz multipliers commute with complex conjugation. -/
theorem conjOperator_realMultiplier {N : ℕ} (g : SchwartzMap (Carrier N) ℝ) :
    conjOperator (realMultiplierOperator g) = realMultiplierOperator g := by
  ext u x
  have hg := (complexifyRealSchwartz g).hasTemperateGrowth
  simp only [conjOperator_apply, realMultiplierOperator, multiplierOperator,
    ContinuousLinearMap.coe_coe, conjTest_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg]
  simp [complexifyRealSchwartz]

/-- Coordinate derivatives commute with complex conjugation. -/
theorem conjOperator_coordinateDerivative {N : ℕ} (i : Fin N) :
    conjOperator (coordinateDerivative i) = coordinateDerivative i := by
  ext u x
  simp only [conjOperator_apply, coordinateDerivative, ContinuousLinearMap.coe_coe,
    conjTest_apply]
  change conj (fderiv ℝ (conjTest u) x (EuclideanSpace.single i 1)) =
    fderiv ℝ u x (EuclideanSpace.single i 1)
  have h : (⇑(conjTest u) : Carrier N → ℂ) = fun y => star (u y) := by
    funext y; simp
  rw [h, fderiv_star]
  simp

/-- Real Schwartz vector fields commute with complex conjugation. -/
theorem conjOperator_vectorField {N : ℕ} (V : RealSchwartzVectorField N) :
    conjOperator (vectorFieldOperator V) = vectorFieldOperator V := by
  unfold vectorFieldOperator
  rw [conjOperator_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [conjOperator_comp, conjOperator_realMultiplier, conjOperator_coordinateDerivative]

/-- Every generator of the commutator classes commutes with complex conjugation. -/
theorem conjOperator_generator {N : ℕ} (Y : OperatorGenerator N) :
    conjOperator Y.toOperator = Y.toOperator := by
  cases Y with
  | vectorField V => exact conjOperator_vectorField V
  | multiplier g => exact conjOperator_realMultiplier g

theorem conjOperator_operatorComm {N : ℕ} (A B : Operator N) :
    conjOperator (operatorComm A B) = operatorComm (conjOperator A) (conjOperator B) := by
  unfold operatorComm
  rw [conjOperator_sub, conjOperator_comp, conjOperator_comp]

/-- Conjugation commutes with iterated commutators against real generators. -/
theorem iteratedCommutator_conjOperator {N : ℕ} (ys : List (OperatorGenerator N)) (T : Operator N) :
    iteratedCommutator ys (conjOperator T) = conjOperator (iteratedCommutator ys T) := by
  induction ys with
  | nil => rfl
  | cons Y ys ih =>
    simp only [iteratedCommutator]
    rw [conjOperator_operatorComm, conjOperator_generator, ih]

/-- `K T K ∈ 𝓞^m` whenever `T ∈ 𝓞^m`, with `(KTK)^t = K T^t K`. -/
theorem OperatorClass.conj {N : ℕ} {m : ℝ} {T : Operator N} (h : OperatorClass m T) :
    OperatorClass m (conjOperator T) := by
  obtain ⟨Tt, hTt, hord⟩ := h
  refine ⟨conjOperator Tt, hTt.conj, fun ys => ?_⟩
  rw [iteratedCommutator_conjOperator]
  exact (hord ys).conj

theorem bilinearPairing_comm {N : ℕ} (u v : TestFunction N) :
    bilinearPairing u v = bilinearPairing v u := by
  unfold bilinearPairing
  simp_rw [mul_comm (u _)]

theorem integrable_mul_test {N : ℕ} (u v : TestFunction N) :
    Integrable (fun x => u x * v x) volume :=
  MemLp.integrable_mul (p := 2) (q := 2) (u.memLp 2 volume) (v.memLp 2 volume)

theorem bilinearPairing_sub_right {N : ℕ} (u v w : TestFunction N) :
    bilinearPairing u (v - w) = bilinearPairing u v - bilinearPairing u w := by
  unfold bilinearPairing
  rw [← integral_sub (integrable_mul_test u v) (integrable_mul_test u w)]
  congr 1
  funext x
  simp [mul_sub]

/-- The bilinear pairing on `𝓢` is nondegenerate. -/
theorem eq_zero_of_bilinearPairing_eq_zero {N : ℕ} {w : TestFunction N}
    (h : ∀ v, bilinearPairing w v = 0) : w = 0 := by
  have h1 := h (conjTest w)
  unfold bilinearPairing at h1
  have hint : Integrable (fun x => ‖w x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm w.continuous.aestronglyMeasurable).mp (w.memLp 2 volume)
  have h2 : ∫ x, ‖w x‖ ^ 2 = 0 := by
    have : ∫ x, w x * conjTest w x = ((∫ x, ‖w x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext x
      simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this] at h1
    exact_mod_cast h1
  have h3 := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint).mp h2
  ext x
  have : (fun x => ‖w x‖ ^ 2) = 0 :=
    (Continuous.ae_eq_iff_eq volume (by fun_prop) continuous_const).mp h3
  have := congrFun this x
  simpa using this

/-- Bilinear transposes are unique. -/
theorem HasBilinearTranspose.unique {N : ℕ} {T A B : Operator N}
    (hA : HasBilinearTranspose T A) (hB : HasBilinearTranspose T B) : A = B := by
  apply LinearMap.ext
  intro v
  have : A v - B v = 0 := by
    apply eq_zero_of_bilinearPairing_eq_zero
    intro u
    rw [bilinearPairing_comm, bilinearPairing_sub_right, ← hA u v, ← hB u v, sub_self]
  exact sub_eq_zero.mp this

/-- The Hermitian `L²` pairing `(u, v) = ∫ u v̄`, linear in its first entry. -/
def hermitianPairing {N : ℕ} (u v : TestFunction N) : ℂ := ∫ x, u x * conj (v x)

theorem hermitianPairing_eq {N : ℕ} (u v : TestFunction N) :
    hermitianPairing u v = bilinearPairing u (conjTest v) := by
  unfold hermitianPairing bilinearPairing
  simp

/-- `Ts` is the Hermitian `L²` adjoint of `T` on `𝓢`: `(Tu, v) = (u, Ts v)`. -/
def HasHermitianAdjoint {N : ℕ} (T Ts : Operator N) : Prop :=
  ∀ u v : TestFunction N, hermitianPairing (T u) v = hermitianPairing u (Ts v)

/-- Existence of the Hermitian adjoint from the bilinear transpose. -/
theorem HasBilinearTranspose.hasHermitianAdjoint {N : ℕ} {T Tt : Operator N}
    (hT : HasBilinearTranspose T Tt) : HasHermitianAdjoint T (conjOperator Tt) := by
  intro u v
  rw [hermitianPairing_eq, hermitianPairing_eq, hT, conjOperator_apply, conjTest_conjTest]

end Hormander.B
