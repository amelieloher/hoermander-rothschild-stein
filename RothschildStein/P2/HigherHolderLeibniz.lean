-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherHolderCompact
public import RothschildStein.P2.ProductAbsorptionExit
public import RothschildStein.S.WordLeibniz
public import RothschildStein.S.HolderLeibnizBounds
public import RothschildStein.S.ZeroExtension
public import RothschildStein.S.MultiplicationBounds

/-!
# Leibniz jets of cutoff products, zero-extended to the patch

Part of the higher Hölder estimate (BB p. 604, (11.95): cutoff multiplication has finite loss in `r⁻¹`;
weak product rule, Leibniz rule in `C^{k,α}_{X̃}`, zero extension by a first-exit argument). For a smooth cutoff `ζ` with `tsupport ζ ⊆ K₀ ⊂ B` (`K₀` compact, `B ⊆ V` open) and a
weak jet `D` of a function `D []` on `B`, the Leibniz jet `leibJet X B ζ D` (the sums of products over the
complementary subwords, `S.leibnizWordValue`, extended by zero off `B`) is the weak jet on `V` of the product
`B.indicator (D [] ζ)`, and its Hölder norms on `V` equal those on `B`, with the explicit bound
`‖(D ζ)_K‖ ≤ 2^{|K|} (max_J ‖X_J ζ‖) ‖D‖_N`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2.HigherHolder

open RothschildStein.P1

section Leibniz

variable {n' q : ℕ} {X : Fin q → (Fin n' → ℝ) → (Fin n' → ℝ)}

/-- The Leibniz jet of the product `D [] * ζ`, extended by zero off `B`. -/
def leibJet (X : Fin q → (Fin n' → ℝ) → (Fin n' → ℝ)) (B : Set (Fin n' → ℝ))
    (ζ : (Fin n' → ℝ) → ℝ) (D : List (Fin q) → (Fin n' → ℝ) → ℝ) :
    List (Fin q) → (Fin n' → ℝ) → ℝ :=
  fun K => B.indicator (S.leibnizWordValue X K D ζ)

theorem leibnizWordValue_nil (ζ : (Fin n' → ℝ) → ℝ) (D : List (Fin q) → (Fin n' → ℝ) → ℝ) :
    S.leibnizWordValue X [] D ζ = fun x => D [] x * ζ x := by
  funext x
  simp [S.leibnizWordValue, S.leibnizSplits, wordDerivative]

theorem leibJet_nil (B : Set (Fin n' → ℝ)) (ζ : (Fin n' → ℝ) → ℝ)
    (D : List (Fin q) → (Fin n' → ℝ) → ℝ) :
    leibJet X B ζ D [] = B.indicator (fun x => D [] x * ζ x) := by
  unfold leibJet
  rw [leibnizWordValue_nil]

/-- **The weak jet of a zero-extended cutoff product.** If `D` is a weak jet of `D []` on the open `B`,
`ζ` is smooth with `ζ = 0` off the compact `K₀ ⊆ B ⊆ V`, then `leibJet X B ζ D` is a weak jet on `V` of
`B.indicator (D [] ζ)` (weak Leibniz rule on `B`, extension by zero). -/
theorem hasWeakWordDeriv_leibJet {V B : Opens (Fin n' → ℝ)} (hBV : (B : Set (Fin n' → ℝ)) ⊆ V)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n' → ℝ))) {ζ : (Fin n' → ℝ) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) {K₀ : Set (Fin n' → ℝ)} (hK₀ : IsCompact K₀)
    (hK₀B : K₀ ⊆ (B : Set (Fin n' → ℝ))) (hζ0 : ∀ z, z ∉ K₀ → ζ z = 0)
    {D : List (Fin q) → (Fin n' → ℝ) → ℝ} (K : List (Fin q))
    (hD : ∀ J, J.Sublist K → hasWeakWordDeriv X B J (D []) (D J)) :
    hasWeakWordDeriv X V K ((B : Set (Fin n' → ℝ)).indicator (fun x => D [] x * ζ x))
      (leibJet X B ζ D K) := by
  have hXB : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (B : Set (Fin n' → ℝ)) := fun i => (hX i).mono hBV
  have h := S.hasWeakWordDeriv_mul_word X B hXB K (D []) ζ hζ.contDiffOn D rfl (fun J hJ => hD J hJ)
  refine S.hasWeakWordDeriv_zeroExtension X V B hBV ⟨K₀, hK₀⟩ hK₀B K _ _ h ?_
  exact Filter.Eventually.of_forall fun x _ hx => by simp [hζ0 x hx]

variable {Ω₀ : Set (Fin n' → ℝ)} {w : Fin q → ℕ+}

/-- The Hölder norm over `V` of the zero-extended Leibniz jet equals that of the Leibniz sum over
`B` (zero extension by a first-exit argument, for an open set; no margin constant). -/
theorem holderENorm_leibJet_eq (hw2 : ∀ i, (w i : ℕ) ≤ 2) {α : ℝ} (hα : 0 < α)
    {V B : Set (Fin n' → ℝ)} (hBV : B ⊆ V) (hB : IsOpen B) {ζ : (Fin n' → ℝ) → ℝ}
    {K₀ : Set (Fin n' → ℝ)} (hK₀ : IsCompact K₀) (hK₀B : K₀ ⊆ B) (htζ : tsupport ζ ⊆ K₀)
    (D : List (Fin q) → (Fin n' → ℝ) → ℝ) (K : List (Fin q)) :
    holderENorm (controlDistance Ω₀ w X) α V (leibJet X B ζ D K) =
      holderENorm (controlDistance Ω₀ w X) α B (S.leibnizWordValue X K D ζ) := by
  have hz : ∀ z ∈ V \ K₀, leibJet X B ζ D K z = 0 := by
    intro z hz
    unfold leibJet
    by_cases hzB : z ∈ B
    · rw [Set.indicator_of_mem hzB]
      unfold S.leibnizWordValue
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hy
      have : wordDerivative X p.2 ζ z = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        exact fun h => hz.2 (htζ ((S.tsupport_wordDerivative_subset X p.2 ζ) h))
      simp [this]
    · rw [Set.indicator_of_notMem hzB]
  rw [holderENorm_eq_of_compact_support_open (Ω := Ω₀) (w := w) (X := X) hw2 hα _ hK₀ hB hK₀B hBV hz]
  exact S.holderENorm_congr _ α B _ fun x hx => Set.indicator_of_mem hx _

/-- The bound of the Leibniz sum on `B`: if every `‖D K‖_{C^α(B)}` and every `‖X_J ζ‖_{C^α(B)}`
(`|J| ≤ N`) is controlled, then for `K` of weight at most `N`
`‖(D ζ)_K‖ ≤ 2^N · c · ∑_{|J| ≤ N} ‖D J‖`. -/
theorem holderENorm_leibnizWordValue_le_jet {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ}
    (hα : 0 < α) {B : Set (Fin n' → ℝ)} (hs : ∀ x ∈ B, ∀ y ∈ B, d x y = 0 → x = y)
    (hw : ∀ j, (w j : ℕ) = 1) {N : ℕ} {ζ : (Fin n' → ℝ) → ℝ} {c : ℝ}
    {D : List (Fin q) → (Fin n' → ℝ) → ℝ}
    (hD : ∀ J ∈ wordFamily w N, holderENorm d α B (D J) ≠ ⊤)
    (hζ : ∀ J ∈ wordFamily w N, holderENorm d α B (wordDerivative X J ζ) ≤ ENNReal.ofReal c)
    {K : List (Fin q)} (hK : K ∈ wordFamily w N) :
    holderENorm d α B (S.leibnizWordValue X K D ζ) ≤
      (2 : ℝ≥0∞) ^ N * ENNReal.ofReal c * ∑ J ∈ wordFamily w N, holderENorm d α B (D J) := by
  have hsub : ∀ p ∈ S.leibnizSplits K, p.1 ∈ wordFamily w N ∧ p.2 ∈ wordFamily w N := by
    intro p hp
    obtain ⟨h1, h2⟩ := S.leibnizSplits_sublist K p hp
    exact ⟨S.sublist_mem_wordFamily w N h1 hK, S.sublist_mem_wordFamily w N h2 hK⟩
  refine (S.holderENorm_leibnizWordValue_le d B hα hs X K D ζ
    (fun p hp => lt_top_iff_ne_top.2 (hD _ (hsub p hp).1))
    (fun p hp => lt_of_le_of_lt (hζ _ (hsub p hp).2) ENNReal.ofReal_lt_top)).trans ?_
  have hlen : K.length ≤ N := by
    have := (S.mem_wordFamily_iff w N K).1 hK
    rwa [wordWeight_eq_length hw] at this
  refine (S.list_sum_le_length_mul (S.leibnizSplits K) _
    (ENNReal.ofReal c * ∑ J ∈ wordFamily w N, holderENorm d α B (D J)) fun p hp => ?_).trans ?_
  · rw [mul_comm]
    exact mul_le_mul' (hζ _ (hsub p hp).2)
      (Finset.single_le_sum (f := fun J => holderENorm d α B (D J)) (fun _ _ => zero_le)
        (hsub p hp).1)
  · rw [S.leibnizSplits_length, mul_assoc]
    refine mul_le_mul' ?_ le_rfl
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hlen

/-- **The jet norm of a zero-extended cutoff product.** Under the hypotheses of
`holderENorm_leibJet_eq` and `holderENorm_leibnizWordValue_le_jet`,
`‖leibJet‖_{N, C^α(V)} ≤ |wordFamily N| · 2^N · c · ‖D‖_{N, C^α(B)}`. -/
theorem holderJetNorm_leibJet_le (hw2 : ∀ i, (w i : ℕ) ≤ 2) (hw : ∀ j, (w j : ℕ) = 1) {α : ℝ}
    (hα : 0 < α) {V B : Set (Fin n' → ℝ)} (hBV : B ⊆ V) (hB : IsOpen B) {ζ : (Fin n' → ℝ) → ℝ}
    {K₀ : Set (Fin n' → ℝ)} (hK₀ : IsCompact K₀) (hK₀B : K₀ ⊆ B) (htζ : tsupport ζ ⊆ K₀)
    (hs : ∀ x ∈ B, ∀ y ∈ B, controlDistance Ω₀ w X x y = 0 → x = y) {N : ℕ} {c : ℝ}
    {D : List (Fin q) → (Fin n' → ℝ) → ℝ}
    (hD : ∀ J ∈ wordFamily w N, holderENorm (controlDistance Ω₀ w X) α B (D J) ≠ ⊤)
    (hζ : ∀ J ∈ wordFamily w N,
      holderENorm (controlDistance Ω₀ w X) α B (wordDerivative X J ζ) ≤ ENNReal.ofReal c) :
    holderJetNorm w (controlDistance Ω₀ w X) V α N (leibJet X B ζ D) ≤
      ((wordFamily w N).card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ N * ENNReal.ofReal c) *
        holderJetNorm w (controlDistance Ω₀ w X) B α N D := by
  unfold holderJetNorm
  calc ∑ K ∈ wordFamily w N, holderENorm (controlDistance Ω₀ w X) α V (leibJet X B ζ D K)
      = ∑ K ∈ wordFamily w N, holderENorm (controlDistance Ω₀ w X) α B
          (S.leibnizWordValue X K D ζ) :=
        Finset.sum_congr rfl fun K _ => holderENorm_leibJet_eq hw2 hα hBV hB hK₀ hK₀B htζ D K
    _ ≤ ∑ K ∈ wordFamily w N, (2 : ℝ≥0∞) ^ N * ENNReal.ofReal c *
          ∑ J ∈ wordFamily w N, holderENorm (controlDistance Ω₀ w X) α B (D J) :=
        Finset.sum_le_sum fun K hK =>
          holderENorm_leibnizWordValue_le_jet hα hs hw hD hζ hK
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

end Leibniz

end RothschildStein.P2.HigherHolder
