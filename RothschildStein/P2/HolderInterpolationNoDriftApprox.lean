-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderInterpolationApprox
public import RothschildStein.P1.WeakExtensionNoDriftHolder

/-!
# No drift: the first Hölder interpolation inequality for compact intrinsic `C^{2,α}`

The no-drift counterpart of `HolderInterpolationApprox`. The first Hölder interpolation inequality
`‖T L̃ v‖_{C^α} ≤ ε ‖L̃ v‖_∞ + C ε^{-γ} ‖v‖_∞` for `v ∈ C²(O)` and `L̃ = ∑ᵢ X̃ᵢ²`
(`exists_fractional_interpolation_noDrift`) extends to compactly supported intrinsic `C^{2,α}_{X̃}` functions `v`
of the patch `V` with Hölder weak jet `D`, `L̃ v := ∑ᵢ D [i, i]` (`weakSumSquares D []`): by BB Thm 2.20 the
Euclidean mollifications `φ_ε` of `v` are smooth and `X̃_I φ_ε → D I` uniformly on `V` for every word of weight
at most two, and the limit passage is `holderENorm_apply_le_of_approx` (alphabet-generic). The constants lose a
factor `2^{γ+1}`. The statement needs only the lifted frame.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

section Generic

variable {n k : ℕ} {w : Fin k → ℕ+} {Xt : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}

/-- **Smooth approximants of a compact intrinsic jet, alphabet-generic** (BB Thm 2.20): for `v`
continuous on the open patch `V`, vanishing on `V ∖ K` for a compact `K ⊆ V`, with continuous weak jet `D`
of all words of weight at most two, the Euclidean mollifications `φ_ε` of the zero extension are smooth and
`X̃_I φ_ε → D I` uniformly on `V` for the nonempty words, `φ_ε → v` uniformly. -/
theorem exists_jet_approximants_noDrift {V : Opens (Fin n → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin n → ℝ)))
    {v : (Fin n → ℝ) → ℝ} {D : List (Fin k) → (Fin n → ℝ) → ℝ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKV : K ⊆ (V : Set (Fin n → ℝ)))
    (hz : ∀ x ∈ (V : Set (Fin n → ℝ)) \ K, v x = 0)
    (hvc : ContinuousOn v (V : Set (Fin n → ℝ)))
    (hw : ∀ I ∈ wordFamily w 2, hasWeakWordDeriv Xt V I v (D I))
    (hct : ∀ I ∈ wordFamily w 2, ContinuousOn (D I) (V : Set (Fin n → ℝ))) :
    ∃ φ : ℝ → (Fin n → ℝ) → ℝ, (∀ ε : ℝ, 0 < ε → ContDiff ℝ (⊤ : ℕ∞) (φ ε)) ∧
      TendstoUniformlyOn φ v (𝓝[>] (0 : ℝ)) (V : Set (Fin n → ℝ)) ∧
      ∀ I ∈ wordFamily w 2, I ≠ [] →
        TendstoUniformlyOn (fun ε => wordDerivative Xt I (φ ε)) (D I) (𝓝[>] (0 : ℝ))
          (V : Set (Fin n → ℝ)) := by
  classical
  set jet : List (Fin k) → (Fin n → ℝ) → ℝ := fun I => if I = [] then v else D I
    with hjet
  have hzero : jet [] = v := by simp [hjet]
  have hw' : ∀ I ∈ wordFamily w 2, hasWeakWordDeriv Xt V I v (jet I) := by
    intro I hI
    by_cases h : I = []
    · subst h
      rw [hzero]
      exact S.hasWeakWordDeriv_nil Xt V (hvc.locallyIntegrableOn V.isOpen.measurableSet)
    · simpa [hjet, h] using hw I hI
  have hct' : ∀ I ∈ wordFamily w 2, ContinuousOn (jet I) (V : Set (Fin n → ℝ)) := by
    intro I hI
    by_cases h : I = []
    · subst h
      rw [hzero]
      exact hvc
    · simpa [hjet, h] using hct I hI
  have hT := S.compact_uniform_weak_word_mollification w Xt V hXV 2 v jet hzero hw' hct'
    hK hKV hz
  obtain ⟨hcont, hcs, -⟩ := S.continuous_compact_zeroExtension_of_local_support V hvc hK hKV hz
  refine ⟨fun ε => S.euclideanRegularize n ((V : Set (Fin n → ℝ)).indicator v) ε,
    fun ε hε => S.contDiff_euclideanRegularize_all_dimensions
      (hcont.locallyIntegrable) hε, ?_, ?_⟩
  · have := hT [] (S.nil_mem_wordFamily _ _)
    rw [hzero] at this
    exact this
  · intro I hI hne
    have := hT I hI
    simpa [hjet, hne] using this

/-- No drift: uniform convergence of the weighted derivatives `X̃ᵢ² φ_ε → D [i, i]` gives uniform
convergence of `L̃ φ_ε = ∑ᵢ X̃ᵢ² φ_ε` to the weak `L̃ v = ∑ᵢ D [i, i]` (`weakSumSquares D []`). -/
theorem tendstoUniformlyOn_sumSquares_nil {V : Set (Fin n → ℝ)} {φ : ℝ → (Fin n → ℝ) → ℝ}
    {D : List (Fin k) → (Fin n → ℝ) → ℝ}
    (h1 : ∀ i : Fin k, TendstoUniformlyOn (fun ε => wordDerivative Xt [i, i] (φ ε))
      (D [i, i]) (𝓝[>] (0 : ℝ)) V) :
    TendstoUniformlyOn (fun ε => sumSquares Xt (φ ε)) (weakSumSquares D [])
      (𝓝[>] (0 : ℝ)) V := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [eventually_abs_sum_sub_le (A := fun i ε x => wordDerivative Xt [i, i] (φ ε) x)
    (a := fun i x => D [i, i] x) h1 (half_pos hη)] with ε hε x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (hε x hx) (half_lt_self hη)

end Generic

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The no-drift weight vector has `(noDriftWeight i : ℕ) = 1`. -/
theorem noDriftWeight_natCast_eq_one (i : Fin q) : ((noDriftWeight i : ℕ+) : ℕ) = 1 := by
  simp [noDriftWeight]

/-- The operator `L̃ = ∑ᵢ X̃ᵢ²` of the no-drift chart is a coordinate operator. -/
theorem isCoordinateOp_noDrift (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m) :
    IsCoordinateOp C (sumSquares C.Xl) := by
  obtain ⟨A, B, hA, hB, h⟩ := sumSquares_eq_diffOp2 (isOpen_liftedDomain C) C.Xl
    (fun i => C.lift_smooth i)
  exact ⟨A, B, hA, hB, h⟩

/-- `L̃ φ` is continuous on the chart domain for `φ ∈ C²(O)`, no drift. -/
theorem continuousOn_sumSquares_of_contDiffOn (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m)
    {φ : (Fin (n + m) → ℝ) → ℝ} (hφ : ContDiffOn ℝ 2 φ C.O) :
    ContinuousOn (sumSquares C.Xl φ) C.O := by
  obtain ⟨A, B, hA, hB, h⟩ := isCoordinateOp_noDrift C
  exact (continuousOn_diffOp2 (isOpen_liftedDomain C) hA hB hφ).congr
    (fun x hx => h φ hφ x hx)

variable {F : KernelFrame (n + m)}

/-- **The first interpolation inequality for compactly supported
intrinsic `C^{2,α}` functions, no drift** (BB Prop 11.50, Lem 11.51, pp. 593–596): for `0 < α < 1` and a
positive-type operator `T` (type `λ ≥ 1`) of a lifted frame there are `γ > 1` and `Cc` such that for
`0 < ε < 1`, every `v` in the compact intrinsic class `memHolderXCompact noDriftWeight C.Xl C.dl V 2 α` of the
patch `V = F.V` with Hölder weak jet `D` (`L̃ v = ∑ᵢ D [i, i]`),
`‖T L̃ v‖_{C^α(V)} ≤ ε ‖L̃ v‖_{∞,V} + Cc ε^{-γ} ‖v‖_{∞,V}`. Unconditional (the lifted frame hypothesis
only). -/
theorem exists_fractional_interpolation_holder_noDrift
    (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m) (hF : C.IsLiftedFrame F) {lam : ℕ}
    (hlam : 1 ≤ lam) (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ γ Cc : ℝ, 1 < γ ∧ 0 < Cc ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ (v : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ),
        memHolderXCompact noDriftWeight C.Xl C.dl F.V 2 α v →
        LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V 2 α v D →
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
            (fun x => T.apply (weakSumSquares D []) x) ≤
          ENNReal.ofReal ε * (⨆ x : (F.V : Set (Fin (n + m) → ℝ)),
              ENNReal.ofReal |weakSumSquares D [] x|) +
            ENNReal.ofReal (Cc * ε ^ (-γ)) *
              ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |v x| := by
  obtain ⟨γ₀, Cc₀, hγ₀, hCc₀, hineq⟩ :=
    exists_fractional_interpolation_noDrift C hF hlam T hα0 hα1
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
  have hwj : ∀ I ∈ wordFamily noDriftWeight 2, hasWeakWordDeriv C.Xl F.V I v (D I) :=
    fun I hI => (hD I hI).1
  have hctj : ∀ I ∈ wordFamily noDriftWeight 2, ContinuousOn (D I) V := fun I hI =>
    LiftedChart.continuousOn_of_holderENorm_lt_top hF.subset_U hα0 (lt_top_iff_ne_top.2 (hD I hI).2)
  have himem : ∀ i : Fin q, ([i, i] : List (Fin q)) ∈ wordFamily noDriftWeight 2 := fun i =>
    (S.mem_wordFamily_iff _ 2 _).2 (by simp [wordWeight, noDriftWeight])
  obtain ⟨φ, hφs, hφv, hφD⟩ := exists_jet_approximants_noDrift (w := noDriftWeight) hXV hK hKV hz
    hvc hwj hctj
  have hL := tendstoUniformlyOn_sumSquares_nil (Xt := C.Xl)
    (fun i => hφD [i, i] (himem i) (by simp))
  have hLc : ∀ᶠ ε₁ in 𝓝[>] (0 : ℝ), ContinuousOn (sumSquares C.Xl (φ ε₁)) V := by
    filter_upwards [self_mem_nhdsWithin] with ε₁ hε₁
    exact (continuousOn_sumSquares_of_contDiffOn C
      (contDiffOn_two_of_top (hφs ε₁ hε₁))).mono hVO
  have hLD := hD.weakSumSquares_nil_ne_top noDriftWeight_natCast_eq_one hα0
  have hg : ContinuousOn (weakSumSquares D []) V :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hF.subset_U hα0 (lt_top_iff_ne_top.2 hLD)
  have hφ : ∀ᶠ ε₁ in 𝓝[>] (0 : ℝ),
      holderENorm C.dl α V (fun x => T.apply (sumSquares C.Xl (φ ε₁)) x) ≤
        ENNReal.ofReal (ε / 2) *
            (⨆ x : V, ENNReal.ofReal |sumSquares C.Xl (φ ε₁) x|) +
          ENNReal.ofReal (Cc₀ * (ε / 2) ^ (-γ₀)) * ⨆ x : V, ENNReal.ofReal |φ ε₁ x| := by
    filter_upwards [self_mem_nhdsWithin] with ε₁ hε₁
    exact hineq (ε / 2) (by positivity) (by linarith) (φ ε₁)
      (contDiffOn_two_of_top (hφs ε₁ hε₁))
  have hres := holderENorm_apply_le_of_approx hF
    (fun i => by simp [noDriftWeight]) hlam T hα0
    (L := sumSquares C.Xl) (ε' := ε / 2) (c' := Cc₀ * (ε / 2) ^ (-γ₀)) (by positivity)
    (by have := Real.rpow_pos_of_pos (by positivity : 0 < ε / 2) (-γ₀); positivity)
    φ (weakSumSquares D []) v hφ hLc hg hL hφv
  have hpow : (ε / 2) ^ (-γ₀) = ε ^ (-γ₀) * (2 : ℝ) ^ γ₀ := by
    rw [Real.div_rpow hε0.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  have e1 : 2 * (ε / 2) = ε := by ring
  have e2 : 2 * (Cc₀ * (ε / 2) ^ (-γ₀)) = 2 * (2 : ℝ) ^ γ₀ * Cc₀ * ε ^ (-γ₀) := by
    rw [hpow]; ring
  rw [e1, e2] at hres
  exact hres

end RothschildStein.P2
