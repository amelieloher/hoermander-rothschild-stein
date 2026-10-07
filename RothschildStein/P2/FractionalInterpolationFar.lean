-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FractionalInterpolationIBP

/-!
# Hölder interpolation: the far part

For a `C³` kernel `H(ξ, η)` of `JetSup` bound `B` supported (in `η`) in a compact subset `K` of the
open set `O`, one integration by parts in `η` (`integral_diffOp2_mul_eq`) gives, for every `f` that is
`C²` on `O`,
`∫ H(ξ, η) (L f)(η) dη = ∫_K f(η) K(ξ, η) dη`, `K = L*_η H` (`adjKernel`),
with `|K| ≤ C B` and `|K(ξ, η) - K(ξ', η)| ≤ C B ‖ξ - ξ'‖` (`far_estimate`). Hence the far term is
bounded by `C B sup_K |f|` in sup norm and is Lipschitz in `ξ` with constant `C B sup_K |f|`
(BB pp. 594-595, Lem 11.51: "integration by parts in the far part").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RothschildStein.P2

variable {N : ℕ}

/-- The expression `adjKernel` as a linear function of the jets `(x₀, x₁, x₂)` of `H`
at a point with second coordinate `η`. -/
def adjLin (A : Fin N → Fin N → (Fin N → ℝ) → ℝ) (B : Fin N → (Fin N → ℝ) → ℝ)
    (η : Fin N → ℝ) (x0 : ℝ) (x1 : Fin N → ℝ) (x2 : Fin N → Fin N → ℝ) : ℝ :=
  ∑ a, ∑ b, (pdv b (pdv a (A a b)) η * x0 + pdv a (A a b) η * x1 b + pdv b (A a b) η * x1 a +
      A a b η * x2 a b) - ∑ a, (pdv a (B a) η * x0 + B a η * x1 a)

theorem adjKernel_eq_adjLin (A : Fin N → Fin N → (Fin N → ℝ) → ℝ) (B : Fin N → (Fin N → ℝ) → ℝ)
    (H : E2 N → ℝ) (p : E2 N) :
    adjKernel A B H p = adjLin A B p.2 (H p) (fun a => etaPartial a H p)
      (fun a b => etaPartial₂ a b H p) := rfl

theorem adjLin_sub (A : Fin N → Fin N → (Fin N → ℝ) → ℝ) (B : Fin N → (Fin N → ℝ) → ℝ)
    (η : Fin N → ℝ) (x0 y0 : ℝ) (x1 y1 : Fin N → ℝ) (x2 y2 : Fin N → Fin N → ℝ) :
    adjLin A B η x0 x1 x2 - adjLin A B η y0 y1 y2 =
      adjLin A B η (x0 - y0) (fun a => x1 a - y1 a) (fun a b => x2 a b - y2 a b) := by
  simp only [adjLin, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- The coefficient bound constant of the operator on a compact set. -/
def CoeffBound (A : Fin N → Fin N → (Fin N → ℝ) → ℝ) (B : Fin N → (Fin N → ℝ) → ℝ)
    (K : Set (Fin N → ℝ)) (Cc : ℝ) : Prop :=
  0 ≤ Cc ∧ ∀ η ∈ K, ∀ a b, |A a b η| ≤ Cc ∧ |pdv a (A a b) η| ≤ Cc ∧
    |pdv b (pdv a (A a b)) η| ≤ Cc ∧ |pdv b (A a b) η| ≤ Cc ∧ |B a η| ≤ Cc ∧
    |pdv a (B a) η| ≤ Cc

theorem abs_adjLin_le {A : Fin N → Fin N → (Fin N → ℝ) → ℝ} {B : Fin N → (Fin N → ℝ) → ℝ}
    {K : Set (Fin N → ℝ)} {Cc : ℝ} (hC : CoeffBound A B K Cc) {η : Fin N → ℝ} (hη : η ∈ K)
    {x0 : ℝ} {x1 : Fin N → ℝ} {x2 : Fin N → Fin N → ℝ} {L : ℝ} (h0 : |x0| ≤ L)
    (h1 : ∀ a, |x1 a| ≤ L) (h2 : ∀ a b, |x2 a b| ≤ L) :
    |adjLin A B η x0 x1 x2| ≤ (4 * (N : ℝ) ^ 2 + 2 * N) * Cc * L := by
  have hL : 0 ≤ L := (abs_nonneg _).trans h0
  have hCc := hC.1
  have t1 : ∀ a b, |pdv b (pdv a (A a b)) η * x0 + pdv a (A a b) η * x1 b +
      pdv b (A a b) η * x1 a + A a b η * x2 a b| ≤ 4 * (Cc * L) := by
    intro a b
    obtain ⟨cA, cA1, cA2, cA1', cB, cB1⟩ := hC.2 η hη a b
    have e1 : |pdv b (pdv a (A a b)) η * x0| ≤ Cc * L := by
      rw [abs_mul]; exact mul_le_mul cA2 h0 (abs_nonneg _) hCc
    have e2 : |pdv a (A a b) η * x1 b| ≤ Cc * L := by
      rw [abs_mul]; exact mul_le_mul cA1 (h1 b) (abs_nonneg _) hCc
    have e3 : |pdv b (A a b) η * x1 a| ≤ Cc * L := by
      rw [abs_mul]; exact mul_le_mul cA1' (h1 a) (abs_nonneg _) hCc
    have e4 : |A a b η * x2 a b| ≤ Cc * L := by
      rw [abs_mul]; exact mul_le_mul cA (h2 a b) (abs_nonneg _) hCc
    calc _ ≤ |pdv b (pdv a (A a b)) η * x0| + |pdv a (A a b) η * x1 b| +
          |pdv b (A a b) η * x1 a| + |A a b η * x2 a b| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ 4 * (Cc * L) := by linarith
  have t2 : ∀ a, |pdv a (B a) η * x0 + B a η * x1 a| ≤ 2 * (Cc * L) := by
    intro a
    obtain ⟨cA, cA1, cA2, cA1', cB, cB1⟩ := hC.2 η hη a a
    have e1 : |pdv a (B a) η * x0| ≤ Cc * L := by
      rw [abs_mul]; exact mul_le_mul cB1 h0 (abs_nonneg _) hCc
    have e2 : |B a η * x1 a| ≤ Cc * L := by
      rw [abs_mul]; exact mul_le_mul cB (h1 a) (abs_nonneg _) hCc
    exact (abs_add_le _ _).trans (by linarith)
  unfold adjLin
  calc _ ≤ |∑ a, ∑ b, (pdv b (pdv a (A a b)) η * x0 + pdv a (A a b) η * x1 b +
        pdv b (A a b) η * x1 a + A a b η * x2 a b)| +
        |∑ a, (pdv a (B a) η * x0 + B a η * x1 a)| := abs_sub _ _
    _ ≤ (∑ a, ∑ b, 4 * (Cc * L)) + ∑ a : Fin N, 2 * (Cc * L) := by
        refine add_le_add ?_ ?_
        · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => t1 a b)
        · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => t2 a)
    _ = (4 * (N : ℝ) ^ 2 + 2 * N) * Cc * L := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

theorem exists_coeffBound {O K : Set (Fin N → ℝ)} (hO : IsOpen O) (hKc : IsCompact K)
    (hKO : K ⊆ O) {A : Fin N → Fin N → (Fin N → ℝ) → ℝ} {B : Fin N → (Fin N → ℝ) → ℝ}
    (hA : ∀ a b, ContDiffOn ℝ 2 (A a b) O) (hB : ∀ a, ContDiffOn ℝ 1 (B a) O) :
    ∃ Cc, CoeffBound A B K Cc := by
  have c0 : ∀ a b, ContinuousOn (A a b) O := fun a b => (hA a b).continuousOn
  have c1 : ∀ a b, ContinuousOn (pdv a (A a b)) O := fun a b =>
    (contDiffOn_pdv (n := 1) hO (hA a b) a).continuousOn
  have c2 : ∀ a b, ContinuousOn (pdv b (pdv a (A a b))) O := fun a b =>
    (contDiffOn_pdv (n := 0) hO (contDiffOn_pdv (n := 1) hO (hA a b) a) b).continuousOn
  have c3 : ∀ a b, ContinuousOn (pdv b (A a b)) O := fun a b =>
    (contDiffOn_pdv (n := 1) hO (hA a b) b).continuousOn
  have d0 : ∀ a, ContinuousOn (B a) O := fun a => (hB a).continuousOn
  have d1 : ∀ a, ContinuousOn (pdv a (B a)) O := fun a =>
    (contDiffOn_pdv (n := 0) hO (hB a) a).continuousOn
  set tAB : Fin N → Fin N → (Fin N → ℝ) → ℝ := fun a b η =>
    |A a b η| + |pdv a (A a b) η| + |pdv b (pdv a (A a b)) η| + |pdv b (A a b) η| with htAB
  set tB : Fin N → (Fin N → ℝ) → ℝ := fun a η => |B a η| + |pdv a (B a) η| with htB
  set F : (Fin N → ℝ) → ℝ := fun η => ∑ a, ∑ b, tAB a b η + ∑ a, tB a η with hF
  have hFc : ContinuousOn F K := by
    refine (continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ => ?_).add
      (continuousOn_finsetSum _ fun a _ => ?_)
    · exact ((((c0 a b).mono hKO).abs.add ((c1 a b).mono hKO).abs).add
        ((c2 a b).mono hKO).abs).add ((c3 a b).mono hKO).abs
    · exact ((d0 a).mono hKO).abs.add ((d1 a).mono hKO).abs
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hFc
  refine ⟨max C 0, le_max_right _ _, fun η hη a b => ?_⟩
  have hFη : F η ≤ max C 0 := (le_abs_self _).trans ((hC η hη).trans (le_max_left _ _))
  have nnAB : ∀ a b, 0 ≤ tAB a b η := fun a b => by
    simp only [htAB]; positivity
  have nnB : ∀ a, 0 ≤ tB a η := fun a => by simp only [htB]; positivity
  have hsAB : tAB a b η ≤ F η := by
    have h1 : tAB a b η ≤ ∑ b', tAB a b' η :=
      Finset.single_le_sum (f := fun b' => tAB a b' η) (fun b' _ => nnAB a b') (Finset.mem_univ b)
    have h2 : ∑ b', tAB a b' η ≤ ∑ a', ∑ b', tAB a' b' η :=
      Finset.single_le_sum (f := fun a' => ∑ b', tAB a' b' η)
        (fun a' _ => Finset.sum_nonneg fun b' _ => nnAB a' b') (Finset.mem_univ a)
    have h3 : 0 ≤ ∑ a', tB a' η := Finset.sum_nonneg fun a' _ => nnB a'
    simp only [hF]; linarith
  have hsB : tB a η ≤ F η := by
    have h1 : tB a η ≤ ∑ a', tB a' η :=
      Finset.single_le_sum (f := fun a' => tB a' η) (fun a' _ => nnB a') (Finset.mem_univ a)
    have h3 : 0 ≤ ∑ a', ∑ b', tAB a' b' η :=
      Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ => nnAB a' b'
    simp only [hF]; linarith
  have e1 : tAB a b η ≤ max C 0 := hsAB.trans hFη
  have e2 : tB a η ≤ max C 0 := hsB.trans hFη
  simp only [htAB] at e1
  simp only [htB] at e2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> [skip; skip; skip; skip; skip; skip] <;>
    first
    | linarith [abs_nonneg (A a b η), abs_nonneg (pdv a (A a b) η),
        abs_nonneg (pdv b (pdv a (A a b)) η), abs_nonneg (pdv b (A a b) η),
        abs_nonneg (B a η), abs_nonneg (pdv a (B a) η)]

theorem adjOp2_eq_zero_of_notMem {A : Fin N → Fin N → (Fin N → ℝ) → ℝ}
    {B : Fin N → (Fin N → ℝ) → ℝ} {φ : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hx : x ∉ tsupport φ) : adjOp2 A B φ x = 0 := by
  unfold adjOp2
  have z1 : ∀ a b, pdv b (pdv a (fun y => A a b y * φ y)) x = 0 := by
    intro a b
    have hx1 : x ∉ tsupport (pdv a (fun y => A a b y * φ y)) := fun h =>
      hx (tsupport_mul_subset' (tsupport_pdv_subset a h))
    exact pdv_eq_zero_of_notMem hx1 b
  have z2 : ∀ a, pdv a (fun y => B a y * φ y) x = 0 := fun a =>
    pdv_eq_zero_of_notMem (fun h => hx (tsupport_mul_subset' h)) a
  simp [z1, z2]

theorem continuousOn_adjKernel_slice {O K : Set (Fin N → ℝ)} (hO : IsOpen O) (hKO : K ⊆ O)
    {A : Fin N → Fin N → (Fin N → ℝ) → ℝ} {B : Fin N → (Fin N → ℝ) → ℝ}
    (hA : ∀ a b, ContDiffOn ℝ 2 (A a b) O) (hB : ∀ a, ContDiffOn ℝ 1 (B a) O)
    {H : E2 N → ℝ} (hH : ContDiff ℝ 3 H) (ξ : Fin N → ℝ) :
    ContinuousOn (fun η => adjKernel A B H (ξ, η)) K := by
  have c0 : ∀ a b, ContinuousOn (A a b) K := fun a b => (hA a b).continuousOn.mono hKO
  have c1 : ∀ a b, ContinuousOn (pdv a (A a b)) K := fun a b =>
    (contDiffOn_pdv (n := 1) hO (hA a b) a).continuousOn.mono hKO
  have c2 : ∀ a b, ContinuousOn (pdv b (pdv a (A a b))) K := fun a b =>
    (contDiffOn_pdv (n := 0) hO (contDiffOn_pdv (n := 1) hO (hA a b) a) b).continuousOn.mono hKO
  have c3 : ∀ a b, ContinuousOn (pdv b (A a b)) K := fun a b =>
    (contDiffOn_pdv (n := 1) hO (hA a b) b).continuousOn.mono hKO
  have d0 : ∀ a, ContinuousOn (B a) K := fun a => (hB a).continuousOn.mono hKO
  have d1 : ∀ a, ContinuousOn (pdv a (B a)) K := fun a =>
    (contDiffOn_pdv (n := 0) hO (hB a) a).continuousOn.mono hKO
  have j0 : Continuous (fun η : Fin N → ℝ => H (ξ, η)) :=
    hH.continuous.comp (continuous_const.prodMk continuous_id)
  have j1 : ∀ a, Continuous (fun η : Fin N → ℝ => etaPartial a H (ξ, η)) := fun a =>
    (contDiff_dirDeriv (n := 0) [dirEta (unitVec a)] H
      (by simpa using hH.of_le (by norm_num))).continuous.comp
      (continuous_const.prodMk continuous_id)
  have j2 : ∀ a b, Continuous (fun η : Fin N → ℝ => etaPartial₂ a b H (ξ, η)) := fun a b =>
    (contDiff_dirDeriv (n := 0) [dirEta (unitVec b), dirEta (unitVec a)] H
      (by simpa using hH.of_le (by norm_num))).continuous.comp
      (continuous_const.prodMk continuous_id)
  unfold adjKernel
  refine (continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ => ?_).sub
    (continuousOn_finsetSum _ fun a _ => ?_)
  · exact (((c2 a b).mul j0.continuousOn).add ((c1 a b).mul (j1 b).continuousOn)).add
      ((c3 a b).mul (j1 a).continuousOn) |>.add ((c0 a b).mul (j2 a b).continuousOn)
  · exact ((d1 a).mul j0.continuousOn).add ((d0 a).mul (j1 a).continuousOn)

/-- **The far estimate.** For a `C³` kernel `H` of jet bound `Bj`, supported (in `η`) in the
compact set `K ⊆ O`, and `f` of class `C²` on `O` with `|f| ≤ M` on `K`:
`|∫ H(ξ, η) (L f)(η) dη| ≤ C Bj M` and the same integral is `C Bj M`-Lipschitz in `ξ`
(Euclidean norm), one integration by parts in `η` (BB pp. 594-595, Lem 11.51). -/
theorem far_estimate {O K : Set (Fin N → ℝ)} (hO : IsOpen O) (hKc : IsCompact K) (hKO : K ⊆ O)
    {A : Fin N → Fin N → (Fin N → ℝ) → ℝ} {B : Fin N → (Fin N → ℝ) → ℝ}
    (hA : ∀ a b, ContDiffOn ℝ 2 (A a b) O) (hB : ∀ a, ContDiffOn ℝ 1 (B a) O) {Cc : ℝ}
    (hC : CoeffBound A B K Cc) {H : E2 N → ℝ} {Bj : ℝ} (hH : JetSup H Bj)
    (hHK : ∀ ξ η, η ∉ K → H (ξ, η) = 0) {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f O)
    {M : ℝ} (hM : ∀ η ∈ K, |f η| ≤ M) (ξ ξ' : Fin N → ℝ) :
    |∫ η, H (ξ, η) * diffOp2 A B f η| ≤
        (volume K).toReal * ((4 * (N : ℝ) ^ 2 + 2 * N) * Cc) * Bj * M ∧
      |(∫ η, H (ξ, η) * diffOp2 A B f η) - ∫ η, H (ξ', η) * diffOp2 A B f η| ≤
        (volume K).toReal * ((4 * (N : ℝ) ^ 2 + 2 * N) * Cc) * (N * Bj) * M * ‖ξ - ξ'‖ := by
  have hKm : MeasurableSet K := hKc.measurableSet
  have hvol : volume K < ⊤ := hKc.measure_lt_top
  have hrep : ∀ ξ : Fin N → ℝ, ∫ η, H (ξ, η) * diffOp2 A B f η =
      ∫ η in K, f η * adjKernel A B H (ξ, η) := by
    intro ξ
    set φ : (Fin N → ℝ) → ℝ := fun η => H (ξ, η) with hφdef
    have hφ : ContDiff ℝ 2 φ := (hH.contDiff.of_le (by norm_num)).comp
      (contDiff_const.prodMk contDiff_id)
    have hφc : HasCompactSupport φ := HasCompactSupport.intro hKc (fun x hx => hHK ξ x hx)
    have hφK : tsupport φ ⊆ K := by
      refine closure_minimal (fun x hx => ?_) hKc.isClosed
      by_contra hxK
      exact hx (hHK ξ x hxK)
    have h1 := integral_diffOp2_mul_eq hO hA hB hf hφ hφc (hφK.trans hKO)
    have e1 : ∫ η, H (ξ, η) * diffOp2 A B f η = ∫ η, diffOp2 A B f η * φ η :=
      integral_congr_ae (Eventually.of_forall fun η => mul_comm _ _)
    rw [e1, h1]
    have h0 : ∀ x ∉ K, f x * adjOp2 A B φ x = 0 := fun x hx => by
      rw [adjOp2_eq_zero_of_notMem (fun h => hx (hφK h)), mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0]
    refine setIntegral_congr_fun hKm (fun x hx => ?_)
    rw [adjOp2_slice hO hA hB hH.contDiff (hKO hx)]
  have hcont : ∀ ξ : Fin N → ℝ, ContinuousOn (fun η => f η * adjKernel A B H (ξ, η)) K := fun ξ =>
    (hf.continuousOn.mono hKO).mul (continuousOn_adjKernel_slice hO hKO hA hB hH.contDiff ξ)
  have hBj : 0 ≤ Bj := hH.nonneg
  have hCc := hC.1
  set Kc : ℝ := (4 * (N : ℝ) ^ 2 + 2 * N) * Cc with hKcdef
  have hKc0 : 0 ≤ Kc := by positivity
  -- pointwise size bound
  have size : ∀ ξ η, η ∈ K → |f η * adjKernel A B H (ξ, η)| ≤ M * (Kc * Bj) := by
    intro ξ η hη
    obtain ⟨j0, j1, j2, -, -, -⟩ := hH.jets (ξ, η)
    have := abs_adjLin_le hC hη j0 j1 j2
    rw [adjKernel_eq_adjLin, abs_mul]
    exact mul_le_mul (hM η hη) (by simpa [hKcdef, mul_assoc] using this) (abs_nonneg _)
      ((abs_nonneg _).trans (hM η hη))
  have vol0 : 0 ≤ (volume K).toReal := ENNReal.toReal_nonneg
  refine ⟨?_, ?_⟩
  · rw [hrep ξ]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := K)
      (f := fun η => f η * adjKernel A B H (ξ, η)) hvol (C := M * (Kc * Bj))
      (fun η hη => by simpa [Real.norm_eq_abs] using size ξ η hη)
    simp only [Real.norm_eq_abs, Measure.real] at this
    calc _ ≤ M * (Kc * Bj) * (volume K).toReal := this
      _ = (volume K).toReal * Kc * Bj * M := by ring
  · rw [hrep ξ, hrep ξ', ← integral_sub ((hcont ξ).integrableOn_compact hKc)
      ((hcont ξ').integrableOn_compact hKc)]
    set L : ℝ := N * Bj * ‖ξ - ξ'‖ with hL
    have hdiff : ∀ η ∈ K, ‖f η * adjKernel A B H (ξ, η) - f η * adjKernel A B H (ξ', η)‖ ≤
        M * (Kc * L) := by
      intro η hη
      have hc1 : ContDiff ℝ 1 H := hH.contDiff.of_le (by norm_num)
      have l0 := lipX_of_coord_bound hc1 (fun p m => (hH.jets p).2.2.2.1 m) ξ ξ' η
      have l1 : ∀ a, |etaPartial a H (ξ, η) - etaPartial a H (ξ', η)| ≤ L := fun a =>
        lipX_of_coord_bound (contDiff_dirDeriv (n := 1) [dirEta (unitVec a)] H
          (by simpa using hH.contDiff.of_le (by norm_num))) (fun p m => (hH.jets p).2.2.2.2.1 m a)
          ξ ξ' η
      have l2 : ∀ a b, |etaPartial₂ a b H (ξ, η) - etaPartial₂ a b H (ξ', η)| ≤ L := fun a b =>
        lipX_of_coord_bound (contDiff_dirDeriv (n := 1) [dirEta (unitVec b), dirEta (unitVec a)]
          H (by simpa using hH.contDiff)) (fun p m => (hH.jets p).2.2.2.2.2 m a b) ξ ξ' η
      have hb := abs_adjLin_le hC hη (x0 := H (ξ, η) - H (ξ', η))
        (x1 := fun a => etaPartial a H (ξ, η) - etaPartial a H (ξ', η))
        (x2 := fun a b => etaPartial₂ a b H (ξ, η) - etaPartial₂ a b H (ξ', η)) l0 l1 l2
      rw [← adjLin_sub] at hb
      have hb2 : |adjKernel A B H (ξ, η) - adjKernel A B H (ξ', η)| ≤ Kc * L := by
        rw [adjKernel_eq_adjLin, adjKernel_eq_adjLin]
        refine hb.trans (le_of_eq ?_)
        rw [hKcdef, hL]
      rw [← mul_sub, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hM η hη) hb2 (abs_nonneg _) ((abs_nonneg _).trans (hM η hη))
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := K)
      (f := fun η => f η * adjKernel A B H (ξ, η) - f η * adjKernel A B H (ξ', η)) hvol
      (C := M * (Kc * L)) hdiff
    simp only [Real.norm_eq_abs, Measure.real] at this
    calc _ ≤ M * (Kc * L) * (volume K).toReal := this
      _ = (volume K).toReal * Kc * (N * Bj) * M * ‖ξ - ξ'‖ := by rw [hL]; ring

end RothschildStein.P2
