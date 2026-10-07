-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderInterpolationLimit
public import RothschildStein.P2.FractionalInterpolation
public import RothschildStein.P1.WeakExtensionHolder
public import RothschildStein.S.CompactUniformWordApproximation
public import RothschildStein.S.MollifierAllDimensions

/-!
# The first Hölder interpolation inequality for compact intrinsic `C^{2,α}`

The first Hölder interpolation inequality `‖T L̃ v‖_{C^α} ≤ ε ‖L̃ v‖_∞ + C ε^{-γ} ‖v‖_∞`
(`FractionalInterpolation`) is
proved there for `v ∈ C²(O)` (Euclidean). Here it is extended to compactly supported intrinsic
`C^{2,α}_{X̃}` functions `v` of the patch `V` with a Hölder weak jet `D`, `L̃ v := D [0] + ∑ᵢ D [i, i]`
(the convention of the weak extension theorem): by BB Thm 2.20 the Euclidean mollifications `φ_ε` of `v` are smooth and
`X̃_I φ_ε → D I` uniformly on `V` for every word of weight at most two, in particular
`L̃ φ_ε → L̃ v`; the limit passage is `HolderInterpolationLimit`. The constants lose a factor `2^{γ+1}`
(`ε` is replaced by `ε/2` in the inequality for `φ_ε`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- `driftWeight` has all weights at most two. -/
theorem driftWeight_le_two' (i : Fin (q + 1)) : ((driftWeight i : ℕ+) : ℕ) ≤ 2 := by
  unfold driftWeight
  split_ifs <;> simp

/-- **Smooth approximants of a compact intrinsic jet** (BB Thm 2.20): for `v` continuous on the
open patch `V`, vanishing on `V ∖ K` for a compact `K ⊆ V`, with continuous weak jet `D` of all
words of weight at most two, the Euclidean mollifications `φ_ε` of the zero extension are smooth
and `X̃_I φ_ε → D I` uniformly on `V` for the nonempty words, `φ_ε → v` uniformly. -/
theorem exists_jet_approximants (C : LiftedChart driftWeight st Ω hΩ X x₀ m)
    {V : Opens (Fin (n + m) → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ)))
    {v : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKV : K ⊆ (V : Set (Fin (n + m) → ℝ)))
    (hz : ∀ x ∈ (V : Set (Fin (n + m) → ℝ)) \ K, v x = 0)
    (hvc : ContinuousOn v (V : Set (Fin (n + m) → ℝ)))
    (hw : ∀ I ∈ wordFamily driftWeight 2, hasWeakWordDeriv C.Xl V I v (D I))
    (hct : ∀ I ∈ wordFamily driftWeight 2, ContinuousOn (D I) (V : Set (Fin (n + m) → ℝ))) :
    ∃ φ : ℝ → (Fin (n + m) → ℝ) → ℝ, (∀ ε : ℝ, 0 < ε → ContDiff ℝ (⊤ : ℕ∞) (φ ε)) ∧
      TendstoUniformlyOn φ v (𝓝[>] (0 : ℝ)) (V : Set (Fin (n + m) → ℝ)) ∧
      ∀ I ∈ wordFamily driftWeight 2, I ≠ [] →
        TendstoUniformlyOn (fun ε => wordDerivative C.Xl I (φ ε)) (D I) (𝓝[>] (0 : ℝ))
          (V : Set (Fin (n + m) → ℝ)) := by
  classical
  set jet : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ := fun I => if I = [] then v else D I
    with hjet
  have hzero : jet [] = v := by simp [hjet]
  have hw' : ∀ I ∈ wordFamily driftWeight 2, hasWeakWordDeriv C.Xl V I v (jet I) := by
    intro I hI
    by_cases h : I = []
    · subst h
      rw [hzero]
      exact S.hasWeakWordDeriv_nil C.Xl V (hvc.locallyIntegrableOn V.isOpen.measurableSet)
    · simpa [hjet, h] using hw I hI
  have hct' : ∀ I ∈ wordFamily driftWeight 2, ContinuousOn (jet I) (V : Set (Fin (n + m) → ℝ)) := by
    intro I hI
    by_cases h : I = []
    · subst h
      rw [hzero]
      exact hvc
    · simpa [hjet, h] using hct I hI
  have hT := S.compact_uniform_weak_word_mollification driftWeight C.Xl V hXV 2 v jet hzero hw' hct'
    hK hKV hz
  obtain ⟨hcont, hcs, -⟩ := S.continuous_compact_zeroExtension_of_local_support V hvc hK hKV hz
  refine ⟨fun ε => S.euclideanRegularize (n + m) ((V : Set (Fin (n + m) → ℝ)).indicator v) ε,
    fun ε hε => S.contDiff_euclideanRegularize_all_dimensions
      (hcont.locallyIntegrable) hε, ?_, ?_⟩
  · have := hT [] (S.nil_mem_wordFamily _ _)
    rw [hzero] at this
    exact this
  · intro I hI hne
    have := hT I hI
    simpa [hjet, hne] using this

/-- The operator `L̃ = X̃₀ + ∑ᵢ X̃ᵢ²` of the drift chart is a coordinate operator. -/
theorem isCoordinateOp_drift (C : LiftedChart driftWeight st Ω hΩ X x₀ m) :
    IsCoordinateOp C (sumSquaresWithDrift C.Xl) := by
  obtain ⟨A, B, hA, hB, h⟩ := sumSquaresWithDrift_eq_diffOp2 (isOpen_liftedDomain C) C.Xl
    (fun i => C.lift_smooth i)
  exact ⟨A, B, hA, hB, h⟩

/-- A smooth function is `C²` on every set. -/
theorem contDiffOn_two_of_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {s : Set E} (h : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiffOn ℝ 2 f s :=
  (h.of_le (by first
    | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    | norm_num)).contDiffOn

/-- `L̃ φ` is continuous on the chart domain for `φ ∈ C²(O)`. -/
theorem continuousOn_sumSquaresWithDrift_of_contDiffOn (C : LiftedChart driftWeight st Ω hΩ X x₀ m)
    {φ : (Fin (n + m) → ℝ) → ℝ} (hφ : ContDiffOn ℝ 2 φ C.O) :
    ContinuousOn (sumSquaresWithDrift C.Xl φ) C.O := by
  obtain ⟨A, B, hA, hB, h⟩ := isCoordinateOp_drift C
  exact (continuousOn_diffOp2 (isOpen_liftedDomain C) hA hB hφ).congr
    (fun x hx => h φ hφ x hx)

/-- Uniform convergence of the weighted derivatives of a jet gives uniform convergence of
`L̃ φ_ε` to the weak `L̃ v = D [0] + ∑ᵢ D [i, i]`. -/
theorem tendstoUniformlyOn_sumSquaresWithDrift (C : LiftedChart driftWeight st Ω hΩ X x₀ m)
    {V : Set (Fin (n + m) → ℝ)} {φ : ℝ → (Fin (n + m) → ℝ) → ℝ}
    {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (h0 : TendstoUniformlyOn (fun ε => wordDerivative C.Xl [0] (φ ε)) (D [0]) (𝓝[>] (0 : ℝ)) V)
    (h1 : ∀ i : Fin q, TendstoUniformlyOn (fun ε => wordDerivative C.Xl [i.succ, i.succ] (φ ε))
      (D [i.succ, i.succ]) (𝓝[>] (0 : ℝ)) V) :
    TendstoUniformlyOn (fun ε => sumSquaresWithDrift C.Xl (φ ε)) (weakSumSquaresWithDrift D)
      (𝓝[>] (0 : ℝ)) V := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hη3 : 0 < η / 3 := by positivity
  filter_upwards [eventually_abs_sub_le_of_tendstoUniformlyOn h0 hη3,
    eventually_abs_sum_sub_le (A := fun i ε x => wordDerivative C.Xl [i.succ, i.succ] (φ ε) x)
      (a := fun i x => D [i.succ, i.succ] x) h1 hη3] with ε hε0 hε1 x hx
  rw [Real.dist_eq]
  have e : weakSumSquaresWithDrift D x - sumSquaresWithDrift C.Xl (φ ε) x =
      -(wordDerivative C.Xl [0] (φ ε) x - D [0] x) +
        -(∑ i : Fin q, wordDerivative C.Xl [i.succ, i.succ] (φ ε) x -
          ∑ i : Fin q, D [i.succ, i.succ] x) := by
    simp only [weakSumSquaresWithDrift, sumSquaresWithDrift, wordDerivative]
    ring
  rw [e]
  have a1 := hε0 x hx
  have a2 := hε1 x hx
  calc |-(wordDerivative C.Xl [0] (φ ε) x - D [0] x) +
        -(∑ i : Fin q, wordDerivative C.Xl [i.succ, i.succ] (φ ε) x -
          ∑ i : Fin q, D [i.succ, i.succ] x)|
      ≤ |-(wordDerivative C.Xl [0] (φ ε) x - D [0] x)| +
        |-(∑ i : Fin q, wordDerivative C.Xl [i.succ, i.succ] (φ ε) x -
          ∑ i : Fin q, D [i.succ, i.succ] x)| := abs_add_le _ _
    _ ≤ η / 3 + η / 3 := by
        rw [abs_neg, abs_neg]
        exact add_le_add a1 a2
    _ < η := by linarith

variable {F : KernelFrame (n + m)}

/-- **The first interpolation inequality for compactly supported
intrinsic `C^{2,α}` functions** (BB Prop 11.50, Lem 11.51, pp. 593–596): for `0 < α < 1` and a
positive-type operator `T` (type `λ ≥ 1`) of a lifted frame there are `γ > 1` and `Cc` such that for
`0 < ε < 1`, every `v` in the compact intrinsic class `memHolderXCompact driftWeight C.Xl C.dl V 2 α`
of the patch `V = F.V` with Hölder weak jet `D` (`L̃ v = D [0] + ∑ᵢ D [i, i]`),
`‖T L̃ v‖_{C^α(V)} ≤ ε ‖L̃ v‖_{∞,V} + Cc ε^{-γ} ‖v‖_{∞,V}`. Unconditional (the lifted frame hypothesis
only). -/
theorem exists_fractional_interpolation_holder_drift
    (C : LiftedChart driftWeight st Ω hΩ X x₀ m) (hF : C.IsLiftedFrame F) {lam : ℕ} (hlam : 1 ≤ lam)
    (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ γ Cc : ℝ, 1 < γ ∧ 0 < Cc ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ (v : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ),
        memHolderXCompact driftWeight C.Xl C.dl F.V 2 α v →
        LiftedChart.IsHolderWeakJet driftWeight C.Xl C.dl F.V 2 α v D →
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
            (fun x => T.apply (weakSumSquaresWithDrift D) x) ≤
          ENNReal.ofReal ε * (⨆ x : (F.V : Set (Fin (n + m) → ℝ)),
              ENNReal.ofReal |weakSumSquaresWithDrift D x|) +
            ENNReal.ofReal (Cc * ε ^ (-γ)) *
              ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |v x| := by
  obtain ⟨γ₀, Cc₀, hγ₀, hCc₀, hineq⟩ := exists_fractional_interpolation_drift C hF hlam T hα0 hα1
  refine ⟨γ₀, 2 * (2 : ℝ) ^ γ₀ * Cc₀, hγ₀, by positivity, ?_⟩
  intro ε hε0 hε1 v D hv hD
  set V : Set (Fin (n + m) → ℝ) := (F.V : Set (Fin (n + m) → ℝ)) with hVdef
  have hVO : V ⊆ C.O := hF.subset_U.trans C.U_subset_O
  have hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) V := fun i => hF.contDiffOn_Xl i
  have hvc : ContinuousOn v V :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hF.subset_U hα0 hv.1.1
  have hK : IsCompact (closure (V ∩ Function.support v)) := hv.2.1
  have hKV : closure (V ∩ Function.support v) ⊆ V := hv.2.2
  have hz : ∀ x ∈ V \ closure (V ∩ Function.support v), v x = 0 := fun x hx => by
    by_contra h
    exact hx.2 (subset_closure ⟨hx.1, h⟩)
  have hwj : ∀ I ∈ wordFamily driftWeight 2, hasWeakWordDeriv C.Xl F.V I v (D I) :=
    fun I hI => (hD I hI).1
  have hctj : ∀ I ∈ wordFamily driftWeight 2, ContinuousOn (D I) V := fun I hI =>
    LiftedChart.continuousOn_of_holderENorm_lt_top hF.subset_U hα0 (lt_top_iff_ne_top.2 (hD I hI).2)
  obtain ⟨h0mem, himem⟩ := drift_words_mem_wordFamily (w := driftWeight) (q := q)
    (by simp [driftWeight]) (fun j => by simp [driftWeight, Fin.succ_ne_zero])
  obtain ⟨φ, hφs, hφv, hφD⟩ := exists_jet_approximants C hXV hK hKV hz hvc hwj hctj
  have hL := tendstoUniformlyOn_sumSquaresWithDrift C (hφD [0] h0mem (by simp))
    (fun i => hφD [i.succ, i.succ] (himem i) (by simp))
  have hLc : ∀ᶠ ε₁ in 𝓝[>] (0 : ℝ), ContinuousOn (sumSquaresWithDrift C.Xl (φ ε₁)) V := by
    filter_upwards [self_mem_nhdsWithin] with ε₁ hε₁
    exact (continuousOn_sumSquaresWithDrift_of_contDiffOn C
      (contDiffOn_two_of_top (hφs ε₁ hε₁))).mono hVO
  have hLD := hD.weakSumSquaresWithDrift_ne_top (by simp [driftWeight])
    (fun j => by simp [driftWeight, Fin.succ_ne_zero]) hα0
  have hg : ContinuousOn (weakSumSquaresWithDrift D) V :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hF.subset_U hα0 (lt_top_iff_ne_top.2 hLD)
  have hφ : ∀ᶠ ε₁ in 𝓝[>] (0 : ℝ),
      holderENorm C.dl α V (fun x => T.apply (sumSquaresWithDrift C.Xl (φ ε₁)) x) ≤
        ENNReal.ofReal (ε / 2) *
            (⨆ x : V, ENNReal.ofReal |sumSquaresWithDrift C.Xl (φ ε₁) x|) +
          ENNReal.ofReal (Cc₀ * (ε / 2) ^ (-γ₀)) * ⨆ x : V, ENNReal.ofReal |φ ε₁ x| := by
    filter_upwards [self_mem_nhdsWithin] with ε₁ hε₁
    exact hineq (ε / 2) (by positivity) (by linarith) (φ ε₁)
      (contDiffOn_two_of_top (hφs ε₁ hε₁))
  have hres := holderENorm_apply_le_of_approx hF (fun i => driftWeight_le_two' i) hlam T hα0
    (L := sumSquaresWithDrift C.Xl) (ε' := ε / 2) (c' := Cc₀ * (ε / 2) ^ (-γ₀)) (by positivity)
    (by have := Real.rpow_pos_of_pos (by positivity : 0 < ε / 2) (-γ₀); positivity)
    φ (weakSumSquaresWithDrift D) v hφ hLc hg hL hφv
  have hpow : (ε / 2) ^ (-γ₀) = ε ^ (-γ₀) * (2 : ℝ) ^ γ₀ := by
    rw [Real.div_rpow hε0.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  have e1 : 2 * (ε / 2) = ε := by ring
  have e2 : 2 * (Cc₀ * (ε / 2) ^ (-γ₀)) = 2 * (2 : ℝ) ^ γ₀ * Cc₀ * ε ^ (-γ₀) := by
    rw [hpow]; ring
  rw [e1, e2] at hres
  exact hres

end RothschildStein.P2
