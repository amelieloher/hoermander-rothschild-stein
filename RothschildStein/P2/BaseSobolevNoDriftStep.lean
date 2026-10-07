-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseSobolevNoDriftDensity
public import RothschildStein.P2.SobolevInterpolationNoDriftStep
public import RothschildStein.P2.TransferCoverCore
public import RothschildStein.H3.WeakJetNormFacts

/-!
# No drift: the cutoff step

Part of the base Sobolev estimate (BB pp. 586-587, (11.69)-(11.70)), without drift. Let `u ∈ W^{2,p}_{X̃}(Ω')` and let
`φ ∈ C_c^∞(Ω')` be a cutoff between two open sets `Us ≤ Ut ≤ Ω'` (`φ = 1` on `Us`,
`tsupport φ ⊆ Ut`, `|X̃_l φ| ≤ b₁`, `|X̃_l² φ| ≤ b₂`). By BB Cor 2.10 the product `u φ` lies in
`W^{2,p}_{X̃,0}(Ω')`, so the compact second-derivative estimate `weakWordENorm_second_of_zero_noDrift`
applies to it. The weak Leibniz rules `X̃_l(uφ) = φ X̃_l u + u X̃_l φ`,
`X̃_l²(uφ) = φ X̃_l² u + 2 X̃_l φ X̃_l u + u X̃_l² φ`, give
`L̃(uφ) = φ L̃u + 2 ∑ₗ X̃_lφ X̃_l u + u L̃φ`, and since `uφ = u` on `Us` (weak words are local)
`second_step_noDrift` is, for every word `I` of weight two,

`‖X̃_I u‖_{L^p(Us)} ≤ Λ (‖L̃u‖_{L^p(Ut)} + 2 b₁ ∑ₗ ‖X̃_l u‖_{L^p(Ut)} + ((q+1) b₂ + 1) ‖u‖_{L^p(Ut)})`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein RothschildStein.P1

variable {n q : ℕ} {w : Fin q → ℕ+} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}

/-- A weak operator value of the operator `L̃ = ∑ₗ X̃ₗ²` without drift consists of weak
derivatives `g₂ₗ` of the words `[l, l]` with `f = ∑ₗ g₂ₗ` a.e. -/
theorem exists_weakWords_of_hasWeakOperatorValue_noDrift {V : Opens (Fin n → ℝ)}
    {u f : (Fin n → ℝ) → ℝ} (h : HasWeakOperatorValue X V (noDriftOpWords q) u f) :
    ∃ g2 : Fin q → (Fin n → ℝ) → ℝ,
      (∀ l : Fin q, hasWeakWordDeriv X V [l, l] u (g2 l)) ∧
      f =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] fun x => ∑ l, g2 l x := by
  obtain ⟨g, hg, hf⟩ := h
  exact ⟨g, fun l => by simpa [noDriftOpWords] using hg l, hf⟩

/-- **The cutoff step, no drift** (see the module docstring). -/
theorem second_step_noDrift
    (hw : ∀ j, (w j : ℕ) = 1) {V : Opens (Fin n → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {a : TestFunction V ℝ (⊤ : ℕ∞)} {p Λ : ℝ} (hp : 1 < p) (hCS : CompactSecondOnNoDrift w X V a p Λ)
    {Ω' Us Ut : Opens (Fin n → ℝ)} (hΩ'V : Ω' ≤ V)
    (hΩ'a : ∀ x ∈ (Ω' : Set (Fin n → ℝ)), a x = 1) (hUsUt : Us ≤ Ut) (hUtΩ : Ut ≤ Ω')
    {u f : (Fin n → ℝ) → ℝ} (hu : memSobolevX w X Ω' 2 (ENNReal.ofReal p) u)
    {g2 : Fin q → (Fin n → ℝ) → ℝ}
    (hg2 : ∀ l : Fin q, hasWeakWordDeriv X Ω' [l, l] u (g2 l))
    (hf : f =ᵐ[volume.restrict (Ω' : Set (Fin n → ℝ))] fun x => ∑ l, g2 l x)
    (φ : TestFunction Ω' ℝ (⊤ : ℕ∞)) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hφs : ∀ x ∈ (Us : Set (Fin n → ℝ)), φ x = 1)
    (hφt : tsupport (φ : (Fin n → ℝ) → ℝ) ⊆ (Ut : Set (Fin n → ℝ))) {b1 b2 : ℝ}
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hφ1' : ∀ (l : Fin q) (x : Fin n → ℝ),
      |fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ) x| ≤ b1)
    (hφ2' : ∀ (l : Fin q) (x : Fin n → ℝ),
      |fieldDerivative (X l) (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)) x| ≤ b2)
    {I : List (Fin q)} (hI : I ∈ wordsOfWeight w 2) :
    weakWordENorm X Us I (ENNReal.ofReal p) u ≤
      ENNReal.ofReal Λ *
        (eLpNorm f (ENNReal.ofReal p) (volume.restrict (Ut : Set (Fin n → ℝ))) +
          ENNReal.ofReal (2 * b1) * ∑ l : Fin q,
            weakWordENorm X Ut [l] (ENNReal.ofReal p) u +
          (ENNReal.ofReal (((q : ℝ) + 1) * b2) + 1) *
            weakWordENorm X Ut [] (ENNReal.ofReal p) u) := by
  classical
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : (1 : ℝ≥0∞) ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have : Fact (1 ≤ P) := ⟨hP1⟩
  have hPtop : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hXΩ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω' : Set (Fin n → ℝ)) := fun i =>
    (hXV i).mono hΩ'V
  have hφsm : ContDiffOn ℝ (⊤ : ℕ∞) (φ : (Fin n → ℝ) → ℝ) (Ω' : Set (Fin n → ℝ)) :=
    φ.contDiff.contDiffOn
  have hUsΩ : (Us : Set (Fin n → ℝ)) ⊆ Ω' := fun x hx => hUtΩ (hUsUt hx)
  have hUt' : (Ut : Set (Fin n → ℝ)) ⊆ Ω' := hUtΩ
  have hΩm : MeasurableSet (Ω' : Set (Fin n → ℝ)) := Ω'.isOpen.measurableSet
  have hIw : I ∈ wordFamily w 2 := mem_wordFamily_two_of_mem_wordsOfWeight_two_noDrift hI
  have hmem1 : ∀ l : Fin q, [l] ∈ wordFamily w 2 := single_mem_wordFamily_two_noDrift hw
  have hmemN : ([] : List (Fin q)) ∈ wordFamily w 2 := S.nil_mem_wordFamily w 2
  choose g1 hg1 using fun l : Fin q => hu.2 [l] (hmem1 l)
  obtain ⟨gN, hgN, -⟩ := hu.2 [] hmemN
  have hLN : hasWeakWordDeriv X Ω' [] u u := S.hasWeakWordDeriv_nil X Ω' hgN.1
  -- the product `u φ` is in `W^{2,p}_{X̃,0}`
  have hf0 : memSobolevXZero w X Ω' 2 P (fun x => u x * φ x) :=
    S.memSobolevXZero_mul_test w X Ω' hXΩ 2 hPtop hu φ
  -- the weak derivatives of the product
  have hL2 : ∀ l : Fin q, hasWeakWordDeriv X Ω' [l, l] (fun x => u x * φ x)
      (fun x => g2 l x * φ x + 2 * g1 l x * fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ) x +
        u x * fieldDerivative (X l) (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)) x) :=
    fun l => S.hasWeakWordDeriv_mul_square X Ω' hXΩ l u (g1 l) (g2 l) φ hφsm (hg1 l).1
      (hg2 l)
  have hCW := weakWordENorm_second_of_zero_noDrift hw hXV hp hCS hΩ'V hΩ'a hf0 hL2
    (Lf := fun x => ∑ l : Fin q, (g2 l x * φ x + 2 * g1 l x *
          fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ) x +
        u x * fieldDerivative (X l) (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)) x))
    Filter.EventuallyEq.rfl hI
  -- the lower bound of the left side (locality of weak words)
  obtain ⟨gI', hgI', -⟩ := hf0.1.2 I hIw
  have hae : u =ᵐ[volume.restrict (Us : Set (Fin n → ℝ))] fun x => u x * φ x :=
    (ae_restrict_iff' Us.isOpen.measurableSet).2 (ae_of_all _ fun x hx => by
      show u x = u x * φ x
      rw [hφs x hx, mul_one])
  have hlow : weakWordENorm X Us I P u ≤ weakWordENorm X Ω' I P (fun x => u x * φ x) := by
    rw [S.weakWordENorm_congr_ae X Us I P hae]
    exact RothschildStein.H3.weakWordENorm_mono_domain X Ω' Us hUsΩ I P _ gI' hgI'
  -- measurability and support facts
  have hmeasφ : AEStronglyMeasurable (φ : (Fin n → ℝ) → ℝ)
      (volume.restrict (Ω' : Set (Fin n → ℝ))) := φ.continuous.aestronglyMeasurable
  have hmeasu : AEStronglyMeasurable u (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    hu.1.aestronglyMeasurable
  have hmeasg1 : ∀ l : Fin q, AEStronglyMeasurable (g1 l)
      (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l => (hg1 l).2.aestronglyMeasurable
  have hmeasOp : AEStronglyMeasurable (fun x => ∑ l, g2 l x)
      (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun l _ => (hg2 l).2.1.aestronglyMeasurable
  have hmeasd1 : ∀ l : Fin q, AEStronglyMeasurable
      (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ))
      (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l =>
    (S.contDiffOn_fieldDerivative Ω' (X l) _ (hXΩ _) hφsm).continuousOn.aestronglyMeasurable
      hΩm
  have hD2 : ∀ l : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (X l) (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)))
      (Ω' : Set (Fin n → ℝ)) := fun l =>
    S.contDiffOn_fieldDerivative Ω' (X l) _ (hXΩ _)
      (S.contDiffOn_fieldDerivative Ω' (X l) _ (hXΩ _) hφsm)
  have hmeasL : AEStronglyMeasurable (sumSquares X (φ : (Fin n → ℝ) → ℝ))
      (volume.restrict (Ω' : Set (Fin n → ℝ))) := by
    have h : sumSquares X (φ : (Fin n → ℝ) → ℝ) = fun x =>
        ∑ l : Fin q, fieldDerivative (X l) (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)) x := rfl
    rw [h]
    exact (continuousOn_finsetSum _ fun l _ => (hD2 l).continuousOn).aestronglyMeasurable hΩm
  have hzeroφ : ∀ x ∉ (Ut : Set (Fin n → ℝ)), (φ : (Fin n → ℝ) → ℝ) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφt h))
  have hzero1 : ∀ l : Fin q, ∀ x ∉ (Ut : Set (Fin n → ℝ)),
      fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ) x = 0 := fun l x hx =>
    wordDerivative_eq_zero_of_notMem_noDrift (X := X) hφt [l] hx
  have hzeroL : ∀ x ∉ (Ut : Set (Fin n → ℝ)),
      sumSquares X (φ : (Fin n → ℝ) → ℝ) x = 0 := fun x hx =>
    sumSquares_eq_zero_of_notMem_noDrift X _ (fun h => hx (hφt h))
  have hφb : ∀ x, |(φ : (Fin n → ℝ) → ℝ) x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hφ0 x)]
    exact hφ1 x
  have hLb : ∀ x, |sumSquares X (φ : (Fin n → ℝ) → ℝ) x| ≤ ((q : ℝ) + 1) * b2 := by
    intro x
    have h : sumSquares X (φ : (Fin n → ℝ) → ℝ) x =
        ∑ l : Fin q, fieldDerivative (X l)
          (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)) x := rfl
    rw [h]
    calc _ ≤ ∑ l : Fin q, |fieldDerivative (X l)
            (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin q, b2 := Finset.sum_le_sum fun l _ => hφ2' l x
      _ = (q : ℝ) * b2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ((q : ℝ) + 1) * b2 := by nlinarith
  -- the norm of `L̃ (u φ)`
  have hLeq : ∀ x, (∑ l : Fin q, (g2 l x * φ x + 2 * g1 l x *
          fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ) x +
        u x * fieldDerivative (X l) (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)) x)) =
      (∑ l, g2 l x) * φ x +
        ∑ l : Fin q, g1 l x * (2 * fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ) x) +
        u x * sumSquares X (φ : (Fin n → ℝ) → ℝ) x := by
    intro x
    have h2 : ∀ l : Fin q, 2 * g1 l x * fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ) x =
        g1 l x * (2 * fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ) x) := fun l => by ring
    have hS : sumSquares X (φ : (Fin n → ℝ) → ℝ) x =
        ∑ l : Fin q, fieldDerivative (X l)
            (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)) x := rfl
    simp only [h2, hS, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  have hLnorm : eLpNorm (fun x => ∑ l : Fin q, (g2 l x * φ x + 2 * g1 l x *
          fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ) x +
        u x * fieldDerivative (X l) (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)) x)) P
        (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      eLpNorm f P (volume.restrict (Ut : Set (Fin n → ℝ))) +
        ENNReal.ofReal (2 * b1) * ∑ l : Fin q,
          eLpNorm (g1 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) +
        ENNReal.ofReal (((q : ℝ) + 1) * b2) *
          eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))) := by
    have e : (fun x => ∑ l : Fin q, (g2 l x * φ x + 2 * g1 l x *
            fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ) x +
          u x * fieldDerivative (X l) (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)) x)) =
        (fun x => (∑ l, g2 l x) * φ x) +
          (∑ l : Fin q, fun x => g1 l x * (2 * fieldDerivative (X l)
            (φ : (Fin n → ℝ) → ℝ) x)) +
          (fun x => u x * sumSquares X (φ : (Fin n → ℝ) → ℝ) x) := by
      funext x
      rw [hLeq x]
      simp [Finset.sum_apply]
    rw [e]
    have eA := eLpNorm_mul_le_of_support hUt' hmeasOp hmeasφ hzeroφ zero_le_one hφb P
    have eB : ∀ l : Fin q, eLpNorm (fun x => g1 l x * (2 * fieldDerivative (X l)
        (φ : (Fin n → ℝ) → ℝ) x)) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
        ENNReal.ofReal (2 * b1) * eLpNorm (g1 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) :=
      fun l => eLpNorm_mul_le_of_support (ψ := fun x => 2 * fieldDerivative (X l)
        (φ : (Fin n → ℝ) → ℝ) x) (b := 2 * b1) hUt' (hmeasg1 l) ((hmeasd1 l).const_mul 2)
        (fun x hx => by simp [hzero1 l x hx]) (by positivity)
        (fun x => by
          rw [abs_mul, abs_two]
          exact mul_le_mul_of_nonneg_left (hφ1' l x) zero_le_two) P
    have eC := eLpNorm_mul_le_of_support hUt' hmeasu hmeasL hzeroL
      (mul_nonneg (by positivity) hb2) hLb P
    have eBsum : eLpNorm (∑ l : Fin q, fun x => g1 l x * (2 * fieldDerivative (X l)
        (φ : (Fin n → ℝ) → ℝ) x)) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
        ENNReal.ofReal (2 * b1) * ∑ l : Fin q,
          eLpNorm (g1 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) := by
      rw [Finset.mul_sum]
      exact (eLpNorm_sum_le hP1).trans (Finset.sum_le_sum fun l _ => eB l)
    have hfOp : eLpNorm (fun x => ∑ l, g2 l x) P
        (volume.restrict (Ut : Set (Fin n → ℝ))) =
        eLpNorm f P (volume.restrict (Ut : Set (Fin n → ℝ))) :=
      (eLpNorm_congr_ae (hf.filter_mono (ae_mono (Measure.restrict_mono hUt' le_rfl)))).symm
    rw [ENNReal.ofReal_one, one_mul, hfOp] at eA
    calc _ ≤ eLpNorm ((fun x => (∑ l, g2 l x) * φ x) +
          (∑ l : Fin q, fun x => g1 l x * (2 * fieldDerivative (X l)
            (φ : (Fin n → ℝ) → ℝ) x))) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
          eLpNorm (fun x => u x * sumSquares X (φ : (Fin n → ℝ) → ℝ) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) := eLpNorm_add_le hP1
      _ ≤ (eLpNorm (fun x => (∑ l, g2 l x) * φ x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) +
          eLpNorm (∑ l : Fin q, fun x => g1 l x * (2 * fieldDerivative (X l)
            (φ : (Fin n → ℝ) → ℝ) x)) P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
          eLpNorm (fun x => u x * sumSquares X (φ : (Fin n → ℝ) → ℝ) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) := add_le_add (eLpNorm_add_le hP1) le_rfl
      _ ≤ _ := add_le_add (add_le_add eA eBsum) eC
  have hfN : eLpNorm (fun x => u x * φ x) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))) := by
    have := eLpNorm_mul_le_of_support hUt' hmeasu hmeasφ hzeroφ zero_le_one hφb P
    rwa [ENNReal.ofReal_one, one_mul] at this
  have hfNw : weakWordENorm X Ω' [] P (fun x => u x * φ x) ≤
      eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))) := by
    rw [S.weakWordENorm_eq X Ω' [] P _ _ (S.hasWeakWordDeriv_nil X Ω'
      (hf0.1.2 [] hmemN |>.choose_spec.1.1))]
    exact hfN
  -- norms of `u` over `Ut`
  have eU1 : ∀ l : Fin q, weakWordENorm X Ut [l] P u =
      eLpNorm (g1 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) := fun l =>
    S.weakWordENorm_eq X Ut _ P u _ (S.hasWeakWordDeriv_restrict X Ω' Ut hUt' (hg1 l).1)
  have eUN : weakWordENorm X Ut [] P u =
      eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))) :=
    S.weakWordENorm_eq X Ut _ P u _ (S.hasWeakWordDeriv_restrict X Ω' Ut hUt' hLN)
  simp only [eU1, eUN]
  calc weakWordENorm X Us I P u ≤ weakWordENorm X Ω' I P (fun x => u x * φ x) := hlow
    _ ≤ ENNReal.ofReal Λ * (_ + weakWordENorm X Ω' [] P (fun x => u x * φ x)) := hCW
    _ ≤ ENNReal.ofReal Λ * ((eLpNorm f P (volume.restrict (Ut : Set (Fin n → ℝ))) +
          ENNReal.ofReal (2 * b1) * ∑ l : Fin q,
            eLpNorm (g1 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) +
          ENNReal.ofReal (((q : ℝ) + 1) * b2) *
            eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ)))) +
          eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ)))) :=
        mul_le_mul' le_rfl (add_le_add hLnorm hfNw)
    _ = _ := by ring

end RothschildStein.P2
