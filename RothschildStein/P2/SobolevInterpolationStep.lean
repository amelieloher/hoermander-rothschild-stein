-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationDensity
public import RothschildStein.P2.SobolevInterpolationWords

/-!
# Sobolev interpolation, seminorm absorption: the cutoff step

Let `u ∈ W^{2,p}_{X̃}(Ω')` and let `φ ∈ C_c^∞(Ω')` be a cutoff between two open sets `Us ≤ Ut ≤ Ω'`
(`φ = 1` on `Us`, `tsupport φ ⊆ Ut`, `0 ≤ φ ≤ 1`, with `|X̃_l φ| ≤ b₁`, `|X̃_l² φ|, |X̃₀ φ| ≤ b₂`).
By BB Cor 2.10 the product `u φ` lies in `W^{2,p}_{X̃,0}(Ω')`, so the compact interpolation inequality
`weakWordENorm_interpolation_of_zero` applies to it. The weak Leibniz rules compute
`X̃_l(uφ) = φ X̃_l u + u X̃_l φ`, `X̃_l²(uφ) = φ X̃_l² u + 2 X̃_l φ X̃_l u + u X̃_l² φ`,
`X̃₀(uφ) = φ X̃₀ u + u X̃₀ φ`, and one obtains (`seminorm_step`)

`∑_l ‖X̃_l u‖_{L^p(Us)} ≤ ε (∑_l ‖X̃_l² u‖_{L^p(Ut)} + ‖X̃₀ u‖_{L^p(Ut)} + 2 b₁ ∑_l ‖X̃_l u‖_{L^p(Ut)}
   + (q+1) b₂ ‖u‖_{L^p(Ut)}) + C ε^{-1} ‖u‖_{L^p(Ut)}`

(BB p. 583: `L̃(φu) = φ L̃u + 2 ∑ X̃_iφ X̃_iu + u L̃φ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein

variable {n q : ℕ} {w : Fin (q + 1) → ℕ+} {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)}

section Helpers

/-- **A bounded multiplier supported in `Ut ⊆ Ω'`**:
`‖g ψ‖_{L^p(Ω')} ≤ b ‖g‖_{L^p(Ut)}` when `ψ` vanishes off `Ut` and `|ψ| ≤ b`. -/
theorem eLpNorm_mul_le_of_support {Ω' Ut : Set (Fin n → ℝ)} (hUt : Ut ⊆ Ω')
    {g ψ : (Fin n → ℝ) → ℝ} (hg : AEStronglyMeasurable g (volume.restrict Ω'))
    (hψ : AEStronglyMeasurable ψ (volume.restrict Ω')) (hψ0 : ∀ x ∉ Ut, ψ x = 0) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ x, |ψ x| ≤ b) (P : ℝ≥0∞) :
    eLpNorm (fun x => g x * ψ x) P (volume.restrict Ω') ≤
      ENNReal.ofReal b * eLpNorm g P (volume.restrict Ut) := by
  have hgψ : AEStronglyMeasurable (fun x => g x * ψ x) (volume.restrict Ω') := hg.mul hψ
  have hsupp : Function.support (fun x => g x * ψ x) ⊆ Ut := by
    intro x hx
    by_contra hxU
    exact hx (by simp [hψ0 x hxU])
  have hgψU : AEStronglyMeasurable (fun x => g x * ψ x) (volume.restrict Ut) := by
    have := hgψ.restrict (s := Ut)
    rwa [Measure.restrict_restrict_of_subset hUt] at this
  rw [← eLpNorm_restrict_eq_of_support_subset hgψ hsupp, Measure.restrict_restrict_of_subset hUt]
  calc eLpNorm (fun x => g x * ψ x) P (volume.restrict Ut)
      ≤ eLpNorm (b • g) P (volume.restrict Ut) := by
        refine eLpNorm_mono_ae hgψU (ae_of_all _ fun x => ?_)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul, abs_mul, abs_mul,
          abs_of_nonneg hb0]
        nlinarith [hb x, abs_nonneg (g x), abs_nonneg (ψ x)]
    _ = ENNReal.ofReal b * eLpNorm g P (volume.restrict Ut) := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hb0]

/-- A function vanishes off any set containing the support of `φ`, together with all its
classical word derivatives. -/
theorem wordDerivative_eq_zero_of_notMem {Ut : Set (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ}
    (hφt : tsupport φ ⊆ Ut) (I : List (Fin (q + 1))) {x : Fin n → ℝ} (hx : x ∉ Ut) :
    wordDerivative X I φ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (hφt (S.tsupport_wordDerivative_subset X I φ h)))

/-- A function that is `1` on an open set has vanishing word derivatives there (`[l]` case). -/
theorem fieldDerivative_eq_zero_of_eq_one {Us : Opens (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ}
    (hφs : ∀ x ∈ (Us : Set (Fin n → ℝ)), φ x = 1) (V : (Fin n → ℝ) → (Fin n → ℝ))
    {x : Fin n → ℝ} (hx : x ∈ (Us : Set (Fin n → ℝ))) : fieldDerivative V φ x = 0 := by
  have h : φ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.eventuallyEq_of_mem (Us.isOpen.mem_nhds hx) (fun y hy => hφs y hy)
  rw [RothschildStein.P1.fieldDerivative_congr_eventually h]
  simp [fieldDerivative]

end Helpers

/-- **The cutoff step** (see the module docstring). -/
theorem seminorm_step
    (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hw0 : (w 0 : ℕ) = 2) {V : Opens (Fin n → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {a : TestFunction V ℝ (⊤ : ℕ∞)} {p εs Cp : ℝ} (hp : 1 < p)
    (hCI : CompactInterpolationOn X V a p εs Cp) {Ω' Us Ut : Opens (Fin n → ℝ)} (hΩ'V : Ω' ≤ V)
    (hΩ'a : ∀ x ∈ (Ω' : Set (Fin n → ℝ)), a x = 1) (hUsUt : Us ≤ Ut) (hUtΩ : Ut ≤ Ω')
    {u : (Fin n → ℝ) → ℝ} (hu : memSobolevX w X Ω' 2 (ENNReal.ofReal p) u)
    (φ : TestFunction Ω' ℝ (⊤ : ℕ∞)) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hφs : ∀ x ∈ (Us : Set (Fin n → ℝ)), φ x = 1)
    (hφt : tsupport (φ : (Fin n → ℝ) → ℝ) ⊆ (Ut : Set (Fin n → ℝ))) {b1 b2 : ℝ}
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hφ1' : ∀ (l : Fin q) (x : Fin n → ℝ),
      |fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ) x| ≤ b1)
    (hφ2' : ∀ (l : Fin q) (x : Fin n → ℝ),
      |fieldDerivative (X l.succ) (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)) x| ≤ b2)
    (hφd : ∀ x : Fin n → ℝ, |fieldDerivative (X 0) (φ : (Fin n → ℝ) → ℝ) x| ≤ b2)
    {ε : ℝ} (hε : 0 < ε) (hεs : ε < εs) :
    ∑ l : Fin q, weakWordENorm X Us [l.succ] (ENNReal.ofReal p) u ≤
      ENNReal.ofReal ε * ((∑ l : Fin q, weakWordENorm X Ut [l.succ, l.succ] (ENNReal.ofReal p) u +
          weakWordENorm X Ut [0] (ENNReal.ofReal p) u) +
        ENNReal.ofReal (2 * b1) * ∑ l : Fin q, weakWordENorm X Ut [l.succ] (ENNReal.ofReal p) u +
        ((q : ℝ≥0∞) + 1) * ENNReal.ofReal b2 * weakWordENorm X Ut [] (ENNReal.ofReal p) u) +
      ENNReal.ofReal (Cp / ε) * weakWordENorm X Ut [] (ENNReal.ofReal p) u := by
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
  have hUtm : MeasurableSet (Ut : Set (Fin n → ℝ)) := Ut.isOpen.measurableSet
  have hΩm : MeasurableSet (Ω' : Set (Fin n → ℝ)) := Ω'.isOpen.measurableSet
  -- the weak derivatives of `u`
  have hmem1 : ∀ l : Fin q, [l.succ] ∈ wordFamily w 2 := fun l => by
    rw [S.mem_wordFamily_iff]
    simp [wordWeight, hw l]
  have hmem2 : ∀ l : Fin q, [l.succ, l.succ] ∈ wordFamily w 2 := fun l => by
    rw [S.mem_wordFamily_iff]
    simp [wordWeight, hw l]
  have hmem0 : [(0 : Fin (q + 1))] ∈ wordFamily w 2 := by
    rw [S.mem_wordFamily_iff]
    simp [wordWeight, hw0]
  have hmemN : ([] : List (Fin (q + 1))) ∈ wordFamily w 2 := S.nil_mem_wordFamily w 2
  choose g1 hg1 using fun l : Fin q => hu.2 [l.succ] (hmem1 l)
  choose g2 hg2 using fun l : Fin q => hu.2 [l.succ, l.succ] (hmem2 l)
  obtain ⟨g0, hg0, hg0p⟩ := hu.2 [0] hmem0
  obtain ⟨gN, hgN, -⟩ := hu.2 [] hmemN
  have hLN : hasWeakWordDeriv X Ω' [] u u := S.hasWeakWordDeriv_nil X Ω' hgN.1
  -- the product `u φ` is in `W^{2,p}_{X̃,0}`
  have hf0 : memSobolevXZero w X Ω' 2 P (fun x => u x * φ x) :=
    S.memSobolevXZero_mul_test w X Ω' hXΩ 2 hPtop hu φ
  have hCW := weakWordENorm_interpolation_of_zero hw hw0 hXV hp hCI hΩ'V hΩ'a hf0 hε hεs
  -- the weak derivatives of the product
  have hL1 : ∀ l : Fin q, hasWeakWordDeriv X Ω' [l.succ] (fun x => u x * φ x)
      (fun x => g1 l x * φ x + u x * fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ) x) :=
    fun l => S.hasWeakWordDeriv_mul_one X Ω' hXΩ l.succ u (g1 l) φ hφsm (hg1 l).1
  have hL2 : ∀ l : Fin q, hasWeakWordDeriv X Ω' [l.succ, l.succ] (fun x => u x * φ x)
      (fun x => g2 l x * φ x + 2 * g1 l x * fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ) x +
        u x * fieldDerivative (X l.succ) (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)) x) :=
    fun l => S.hasWeakWordDeriv_mul_square X Ω' hXΩ l.succ u (g1 l) (g2 l) φ hφsm (hg1 l).1
      (hg2 l).1
  have hL0 : hasWeakWordDeriv X Ω' [0] (fun x => u x * φ x)
      (fun x => g0 x * φ x + u x * fieldDerivative (X 0) (φ : (Fin n → ℝ) → ℝ) x) :=
    S.hasWeakWordDeriv_mul_one X Ω' hXΩ 0 u g0 φ hφsm hg0
  have hLNf : hasWeakWordDeriv X Ω' [] (fun x => u x * φ x) (fun x => u x * φ x) :=
    S.hasWeakWordDeriv_nil X Ω' (hf0.1.2 [] hmemN |>.choose_spec.1.1)
  -- norms of the products over `Ω'`
  have eF1 : ∀ l : Fin q, weakWordENorm X Ω' [l.succ] P (fun x => u x * φ x) =
      eLpNorm (fun x => g1 l x * φ x + u x * fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ) x)
        P (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l =>
    S.weakWordENorm_eq X Ω' _ P _ _ (hL1 l)
  have eF2 : ∀ l : Fin q, weakWordENorm X Ω' [l.succ, l.succ] P (fun x => u x * φ x) =
      eLpNorm (fun x => g2 l x * φ x + 2 * g1 l x *
          fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ) x +
        u x * fieldDerivative (X l.succ) (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)) x)
        P (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l =>
    S.weakWordENorm_eq X Ω' _ P _ _ (hL2 l)
  have eF0 : weakWordENorm X Ω' [0] P (fun x => u x * φ x) =
      eLpNorm (fun x => g0 x * φ x + u x * fieldDerivative (X 0) (φ : (Fin n → ℝ) → ℝ) x)
        P (volume.restrict (Ω' : Set (Fin n → ℝ))) := S.weakWordENorm_eq X Ω' _ P _ _ hL0
  have eFN : weakWordENorm X Ω' [] P (fun x => u x * φ x) =
      eLpNorm (fun x => u x * φ x) P (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    S.weakWordENorm_eq X Ω' _ P _ _ hLNf
  -- norms of `u` over `Us` and `Ut`
  have eUs : ∀ l : Fin q, weakWordENorm X Us [l.succ] P u =
      eLpNorm (g1 l) P (volume.restrict (Us : Set (Fin n → ℝ))) := fun l =>
    S.weakWordENorm_eq X Us _ P u _ (S.hasWeakWordDeriv_restrict X Ω' Us hUsΩ (hg1 l).1)
  have eU1 : ∀ l : Fin q, weakWordENorm X Ut [l.succ] P u =
      eLpNorm (g1 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) := fun l =>
    S.weakWordENorm_eq X Ut _ P u _ (S.hasWeakWordDeriv_restrict X Ω' Ut hUt' (hg1 l).1)
  have eU2 : ∀ l : Fin q, weakWordENorm X Ut [l.succ, l.succ] P u =
      eLpNorm (g2 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) := fun l =>
    S.weakWordENorm_eq X Ut _ P u _ (S.hasWeakWordDeriv_restrict X Ω' Ut hUt' (hg2 l).1)
  have eU0 : weakWordENorm X Ut [0] P u = eLpNorm g0 P (volume.restrict (Ut : Set (Fin n → ℝ))) :=
    S.weakWordENorm_eq X Ut _ P u _ (S.hasWeakWordDeriv_restrict X Ω' Ut hUt' hg0)
  have eUN : weakWordENorm X Ut [] P u = eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))) :=
    S.weakWordENorm_eq X Ut _ P u _ (S.hasWeakWordDeriv_restrict X Ω' Ut hUt' hLN)
  -- measurability of the pieces
  have hmeasψ1 : ∀ l : Fin q, AEStronglyMeasurable
      (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)) (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    fun l => (S.contDiffOn_fieldDerivative Ω' (X l.succ) _ (hXΩ _) hφsm).continuousOn.aestronglyMeasurable
      hΩm
  have hmeasψ2 : ∀ l : Fin q, AEStronglyMeasurable
      (fieldDerivative (X l.succ) (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)))
      (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l =>
    (S.contDiffOn_fieldDerivative Ω' (X l.succ) _ (hXΩ _)
      (S.contDiffOn_fieldDerivative Ω' (X l.succ) _ (hXΩ _) hφsm)).continuousOn.aestronglyMeasurable
      hΩm
  have hmeasψ0 : AEStronglyMeasurable (fieldDerivative (X 0) (φ : (Fin n → ℝ) → ℝ))
      (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    (S.contDiffOn_fieldDerivative Ω' (X 0) _ (hXΩ _) hφsm).continuousOn.aestronglyMeasurable hΩm
  have hmeasφ : AEStronglyMeasurable (φ : (Fin n → ℝ) → ℝ)
      (volume.restrict (Ω' : Set (Fin n → ℝ))) := φ.continuous.aestronglyMeasurable
  have hzero1 : ∀ l : Fin q, ∀ x ∉ (Ut : Set (Fin n → ℝ)),
      fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ) x = 0 := fun l x hx =>
    wordDerivative_eq_zero_of_notMem (X := X) hφt [l.succ] hx
  have hzero2 : ∀ l : Fin q, ∀ x ∉ (Ut : Set (Fin n → ℝ)),
      fieldDerivative (X l.succ) (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)) x = 0 :=
    fun l x hx => wordDerivative_eq_zero_of_notMem (X := X) hφt [l.succ, l.succ] hx
  have hzero0 : ∀ x ∉ (Ut : Set (Fin n → ℝ)),
      fieldDerivative (X 0) (φ : (Fin n → ℝ) → ℝ) x = 0 := fun x hx =>
    wordDerivative_eq_zero_of_notMem (X := X) hφt [0] hx
  have hzeroφ : ∀ x ∉ (Ut : Set (Fin n → ℝ)), (φ : (Fin n → ℝ) → ℝ) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφt h))
  have hφb : ∀ x, |(φ : (Fin n → ℝ) → ℝ) x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hφ0 x)]
    exact hφ1 x
  -- the lower bound of the left side
  have hlow : ∀ l : Fin q, weakWordENorm X Us [l.succ] P u ≤
      weakWordENorm X Ω' [l.succ] P (fun x => u x * φ x) := by
    intro l
    rw [eUs l, eF1 l]
    have hae : g1 l =ᵐ[volume.restrict (Us : Set (Fin n → ℝ))]
        fun x => g1 l x * φ x + u x * fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ) x := by
      refine (ae_restrict_iff' Us.isOpen.measurableSet).2 (ae_of_all _ fun x hx => ?_)
      show g1 l x = g1 l x * φ x + u x * fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ) x
      rw [hφs x hx, fieldDerivative_eq_zero_of_eq_one hφs (X l.succ) hx]
      simp
    calc eLpNorm (g1 l) P (volume.restrict (Us : Set (Fin n → ℝ)))
        = eLpNorm (fun x => g1 l x * φ x + u x *
            fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ) x) P
            (volume.restrict (Us : Set (Fin n → ℝ))) := eLpNorm_congr_ae hae
      _ ≤ _ := eLpNorm_mono_measure _ (Measure.restrict_mono hUsΩ le_rfl)
  -- the upper bounds of the right side
  have hmeasg1 : ∀ l : Fin q, AEStronglyMeasurable (g1 l) (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    fun l => (hg1 l).2.aestronglyMeasurable
  have hmeasg2 : ∀ l : Fin q, AEStronglyMeasurable (g2 l) (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    fun l => (hg2 l).2.aestronglyMeasurable
  have hmeasg0 : AEStronglyMeasurable g0 (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    hg0p.aestronglyMeasurable
  have hmeasu : AEStronglyMeasurable u (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    hu.1.aestronglyMeasurable
  have hU2 : ∀ l : Fin q, weakWordENorm X Ω' [l.succ, l.succ] P (fun x => u x * φ x) ≤
      eLpNorm (g2 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) +
        ENNReal.ofReal (2 * b1) * eLpNorm (g1 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) +
        ENNReal.ofReal b2 * eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))) := by
    intro l
    rw [eF2 l]
    have h : (fun x => g2 l x * φ x + 2 * g1 l x *
          fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ) x +
        u x * fieldDerivative (X l.succ) (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)) x) =
        (fun x => g2 l x * φ x) + (fun x => g1 l x * (2 * fieldDerivative (X l.succ)
          (φ : (Fin n → ℝ) → ℝ) x)) + (fun x => u x * fieldDerivative (X l.succ)
            (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)) x) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [h]
    have e1 := eLpNorm_mul_le_of_support hUt' (hmeasg2 l) hmeasφ hzeroφ zero_le_one hφb P
    have e2 := eLpNorm_mul_le_of_support (ψ := fun x => 2 * fieldDerivative (X l.succ)
      (φ : (Fin n → ℝ) → ℝ) x) (b := 2 * b1) hUt' (hmeasg1 l) ((hmeasψ1 l).const_mul 2)
      (fun x hx => by simp [hzero1 l x hx]) (by positivity)
      (fun x => by
        rw [abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left (hφ1' l x) zero_le_two) P
    have e3 := eLpNorm_mul_le_of_support hUt' hmeasu (hmeasψ2 l) (hzero2 l) hb2 (hφ2' l) P
    calc eLpNorm ((fun x => g2 l x * φ x) + (fun x => g1 l x * (2 * fieldDerivative (X l.succ)
          (φ : (Fin n → ℝ) → ℝ) x)) + (fun x => u x * fieldDerivative (X l.succ)
            (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)) x)) P
          (volume.restrict (Ω' : Set (Fin n → ℝ)))
        ≤ eLpNorm ((fun x => g2 l x * φ x) + (fun x => g1 l x * (2 * fieldDerivative (X l.succ)
          (φ : (Fin n → ℝ) → ℝ) x))) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
          eLpNorm (fun x => u x * fieldDerivative (X l.succ)
            (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) := eLpNorm_add_le hP1
      _ ≤ (eLpNorm (fun x => g2 l x * φ x) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
          eLpNorm (fun x => g1 l x * (2 * fieldDerivative (X l.succ)
            (φ : (Fin n → ℝ) → ℝ) x)) P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
          eLpNorm (fun x => u x * fieldDerivative (X l.succ)
            (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) := add_le_add (eLpNorm_add_le hP1) le_rfl
      _ ≤ (ENNReal.ofReal 1 * eLpNorm (g2 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) +
          ENNReal.ofReal (2 * b1) * eLpNorm (g1 l) P (volume.restrict (Ut : Set (Fin n → ℝ)))) +
          ENNReal.ofReal b2 * eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))) :=
        add_le_add (add_le_add e1 e2) e3
      _ = _ := by rw [ENNReal.ofReal_one, one_mul]
  have hU0 : weakWordENorm X Ω' [0] P (fun x => u x * φ x) ≤
      eLpNorm g0 P (volume.restrict (Ut : Set (Fin n → ℝ))) +
        ENNReal.ofReal b2 * eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))) := by
    rw [eF0]
    have e1 := eLpNorm_mul_le_of_support hUt' hmeasg0 hmeasφ hzeroφ zero_le_one hφb P
    have e3 := eLpNorm_mul_le_of_support hUt' hmeasu hmeasψ0 hzero0 hb2 hφd P
    calc eLpNorm (fun x => g0 x * φ x + u x * fieldDerivative (X 0) (φ : (Fin n → ℝ) → ℝ) x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ)))
        ≤ eLpNorm (fun x => g0 x * φ x) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
          eLpNorm (fun x => u x * fieldDerivative (X 0) (φ : (Fin n → ℝ) → ℝ) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) := eLpNorm_add_le hP1
      _ ≤ ENNReal.ofReal 1 * eLpNorm g0 P (volume.restrict (Ut : Set (Fin n → ℝ))) +
          ENNReal.ofReal b2 * eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))) :=
        add_le_add e1 e3
      _ = _ := by rw [ENNReal.ofReal_one, one_mul]
  have hUN : weakWordENorm X Ω' [] P (fun x => u x * φ x) ≤
      eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))) := by
    rw [eFN]
    have e1 := eLpNorm_mul_le_of_support hUt' hmeasu hmeasφ hzeroφ zero_le_one hφb P
    rwa [ENNReal.ofReal_one, one_mul] at e1
  simp only [eUs, eU1, eU2, eU0, eUN]
  calc ∑ l : Fin q, eLpNorm (g1 l) P (volume.restrict (Us : Set (Fin n → ℝ)))
      ≤ ∑ l : Fin q, weakWordENorm X Ω' [l.succ] P (fun x => u x * φ x) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [← eUs l]
        exact hlow l
    _ ≤ ENNReal.ofReal ε * (∑ l : Fin q, weakWordENorm X Ω' [l.succ, l.succ] P
          (fun x => u x * φ x) + weakWordENorm X Ω' [0] P (fun x => u x * φ x)) +
        ENNReal.ofReal (Cp / ε) * weakWordENorm X Ω' [] P (fun x => u x * φ x) := hCW
    _ ≤ ENNReal.ofReal ε * (∑ l : Fin q, (eLpNorm (g2 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) +
          ENNReal.ofReal (2 * b1) * eLpNorm (g1 l) P (volume.restrict (Ut : Set (Fin n → ℝ))) +
          ENNReal.ofReal b2 * eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ)))) +
        (eLpNorm g0 P (volume.restrict (Ut : Set (Fin n → ℝ))) +
          ENNReal.ofReal b2 * eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm u P (volume.restrict (Ut : Set (Fin n → ℝ))) :=
        add_le_add (mul_le_mul' le_rfl (add_le_add (Finset.sum_le_sum fun l _ => hU2 l) hU0))
          (mul_le_mul' le_rfl hUN)
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring

end RothschildStein.P2
