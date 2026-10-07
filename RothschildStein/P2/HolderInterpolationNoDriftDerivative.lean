-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderInterpolationNoDriftApprox
public import RothschildStein.P2.HolderInterpolationCombine
public import RothschildStein.P1.WeakExtensionNoDriftMain
public import RothschildStein.S.HolderBounds

/-!
# No drift: interpolation for the first derivatives

The no-drift counterpart of `HolderInterpolationDerivative` (the derivative interpolation inequality, BB Prop 11.50,
(11.81)-(11.83), pp. 593-596; alphabet `Fin q`, all weights one, `L̃ = ∑ᵢ X̃ᵢ²`). Let `a ∈ C_c^∞(V)` be the fixed
cutoff of the derivative representations and `v` a compactly supported intrinsic `C^{2,α}_{X̃}` function of the
patch with `a v = v`. Then, with the parametrix identity `v = a v = P_L L̃ v + F_L v` (extended to compact
`C^{2,α}` by the weak extension theorem, no Hölder-norm density) and the first-order identity `X̃_l v = F_l L̃ v + S_l v` of
the derivative representations:

* `‖X̃_l v‖_{C^α} ≤ ‖F_l L̃ v‖_{C^α} + C_{S_l} ‖v‖_{C^α}` (Hölder continuity of the type-0 operator `S_l`);
* `‖v‖_{C^α} ≤ ‖P_L L̃ v‖_{C^α} + ‖F_L v‖_{C^α}`;
* the first interpolation inequality (`exists_fractional_interpolation_holder_noDrift`) bounds `‖F_l L̃ v‖_{C^α}`
  and `‖P_L L̃ v‖_{C^α}` by `ε' ‖L̃ v‖_∞ + C ε'^{-γ} ‖v‖_∞`, and the `L^∞ → C^α` bound of the continuity theorem for the
  type-one operator `F_L` gives `‖F_L v‖_{C^α} ≤ C ‖v‖_∞`.

Choosing `ε'` a small multiple of `ε` (`InterpBound` calculus) gives
`∑_l ‖X̃_l v‖_{C^α} ≤ ε ‖L̃ v‖_∞ + C(𝒜, α) ε^{-γ} ‖v‖_∞`. The result assumes exactly the hypotheses of
`weakExtension_parametrix_full_noDrift_of` and `weakExtension_firstOrder_full_noDrift_of` (`LeftDifferentiation`, the
`SignedParametrixNoDrift`s, the density data `c`). The `(HD)` package of the lifted control distance is
`LiftedChart.distanceGeometry`, which needs no further hypothesis.
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
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart noDriftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The identities of the derivative representations extended to compactly supported intrinsic
`C^{2,α}` functions, no drift** (by the weak extension theorem: `W^{2,p}` approximation by tests and continuity of both sides,
no Hölder-norm density). Under the hypotheses of the derivative representations on a standard frame there are
operators `P_L` (type 2), `F_L` (type 1), `F_l` (type 1), `S_l` (type-0 endpoint) such that for every
compactly supported intrinsic `C^{2,α}_{X̃}` function `v` of the patch with Hölder weak jet `D` and `a v = v`,
pointwise on `V`: `v = P_L L̃ v + F_L v` and `X̃_l v = F_l L̃ v + S_l v` (`X̃_l v = D [l]`,
`L̃ v = ∑ᵢ D [i, i]`). -/
theorem exists_compactIdentities_noDrift_of_representation (hF : C.IsStandardFrame F H K hQ)
    (hLeftDiff : LeftDifferentiation F noDriftWeight C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (P₂ : TypeOperator F 2) (F₂ : TypeOperator F 1) (Fl : Fin q → TypeOperator F 1)
      (Sl : Fin q → TypeOperator F 0), (∀ l, IsEndpoint F C.Xl (Sl l)) ∧
      ∀ (v : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ),
        memHolderXCompact noDriftWeight C.Xl C.dl F.V 2 α v →
        LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V 2 α v D → (∀ x, a x * v x = v x) →
        EqOn v (fun ξ => P₂.apply (weakSumSquares D []) ξ + F₂.apply v ξ)
          (F.V : Set (Fin (n + m) → ℝ)) ∧
        ∀ l : Fin q,
          EqOn (fun ξ => (Fl l).apply (weakSumSquares D []) ξ + (Sl l).apply v ξ)
            (D [l]) (F.V : Set (Fin (n + m) → ℝ)) := by
  classical
  have hw : ∀ j : Fin q, ((noDriftWeight j : ℕ+) : ℕ) = 1 := noDriftWeight_natCast_eq_one
  obtain ⟨b, hab⟩ := exists_cutoff_mul_eq F.V a
  obtain ⟨P₁, P₂, F₁, F₂, -, -, -, -, -, -, -, -, -, -, -, -, hLeft⟩ :=
    LiftedChart.weakExtension_parametrix_full_noDrift_of hF hw hc hc0 a b hab (hParametrix b)
  obtain ⟨Fl, Sl, hend, -, -, -, hFirst⟩ :=
    LiftedChart.weakExtension_firstOrder_full_noDrift_of hF hw hLeftDiff hc hc0 a hParametrix
  refine ⟨P₂, F₂, Fl, Sl, hend, fun v D hv hD hav => ⟨?_, ?_⟩⟩
  · intro ξ hξ
    have := hLeft α hα0 hα1 v hv D hD ξ hξ
    rwa [hav ξ] at this
  · intro l
    have hav' : (fun x => a x * v x) = v := funext hav
    obtain ⟨hweak, hcont, -⟩ := hFirst α hα0 hα1 v hv D hD l
    rw [hav'] at hweak
    have hmem := LiftedChart.horizontal_mem_wordFamily_noDrift (w := noDriftWeight) hw l
    have hu := S.hasWeakWordDeriv_unique C.Xl F.V hweak (hD [l] hmem).1
    exact Measure.eqOn_open_of_ae_eq hu F.V.isOpen hcont
      (LiftedChart.continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0
        (lt_top_iff_ne_top.2 (hD [l] hmem).2))

/-- **The derivative interpolation inequality, no drift** (BB
(11.81)-(11.83)): under the hypotheses of the derivative representations on a standard frame (`LeftDifferentiation`,
`SignedParametrixNoDrift`, density `c`) and `0 < α < 1` there are `γ > 1` and `Cc` such that for `0 < ε < 1` and
every compactly supported intrinsic `C^{2,α}_{X̃}` function `v` of the patch `V` with Hölder weak jet `D` and
`a v = v`, `∑_{l} ‖X̃_l v‖_{C^α(V)} ≤ ε ‖L̃ v‖_{∞,V} + Cc ε^{-γ} ‖v‖_{∞,V}`, where `X̃_l v = D [l]` and
`L̃ v = ∑ᵢ D [i, i]`. -/
theorem exists_derivativeInterpolation_noDrift_of_representation (hF : C.IsStandardFrame F H K hQ)
    (hLeftDiff : LeftDifferentiation F noDriftWeight C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ γ Cc : ℝ, 1 < γ ∧ 0 < Cc ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ (v : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ),
        memHolderXCompact noDriftWeight C.Xl C.dl F.V 2 α v →
        LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V 2 α v D → (∀ x, a x * v x = v x) →
        ∑ l : Fin q, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D [l]) ≤
          ENNReal.ofReal ε * (⨆ x : (F.V : Set (Fin (n + m) → ℝ)),
              ENNReal.ofReal |weakSumSquares D [] x|) +
            ENNReal.ofReal (Cc * ε ^ (-γ)) *
              ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |v x| := by
  classical
  obtain ⟨P₂, F₂, Fl, Sl, -, hid⟩ := exists_compactIdentities_noDrift_of_representation hF hLeftDiff hc
    hc0 a hParametrix hα0 hα1
  -- the constants of the finitely many operators
  choose γl Cl hγl hCl hAl using fun l : Fin q =>
    exists_fractional_interpolation_holder_noDrift C hF.lifted (lam := 1) le_rfl (Fl l) hα0 hα1
  obtain ⟨γ₂, C₂, hγ₂, hC₂, hA₂⟩ :=
    exists_fractional_interpolation_holder_noDrift C hF.lifted (lam := 2) (by norm_num) P₂ hα0 hα1
  choose CSl hCSl hHV hCSb using fun l : Fin q =>
    TypeOperator.exists_holderENorm_bound_standard hF (Sl l) hα0 hα1
  obtain ⟨CH₂, hCH₂, hF₂b⟩ := TypeOperator.exists_holderENorm_bound hF.lifted (le_refl 1) F₂ hα0 hα1
  set γs : ℝ := 1 + ∑ l, γl l + γ₂ with hγs
  have hγl0 : ∀ l, 0 ≤ γl l := fun l => (by linarith [hγl l] : (0 : ℝ) ≤ γl l)
  have hsumγ : 0 ≤ ∑ l, γl l := Finset.sum_nonneg fun l _ => hγl0 l
  have hγs1 : 1 < γs := by rw [hγs]; linarith
  have hγle : ∀ l, γl l ≤ γs := fun l => by
    have : γl l ≤ ∑ l', γl l' :=
      Finset.single_le_sum (f := γl) (fun l' _ => hγl0 l') (Finset.mem_univ l)
    rw [hγs]; linarith
  have hγ₂le : γ₂ ≤ γs := by rw [hγs]; linarith
  -- scales
  set N : ℝ := (q : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  set t₁ : ℝ := 1 / (2 * N) with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have ht₁1 : t₁ ≤ 1 := by
    rw [ht₁, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [hN]; linarith
  set CSs : ℝ := ∑ l, CSl l with hCSs
  have hCSs0 : 0 ≤ CSs := Finset.sum_nonneg fun l _ => (hCSl l).le
  set t₂ : ℝ := 1 / (2 * (CSs + 1)) with ht₂
  have ht₂0 : 0 < t₂ := by positivity
  have ht₂1 : t₂ ≤ 1 := by
    rw [ht₂, div_le_one (by positivity)]
    linarith
  have e1 : (q : ℝ) * t₁ ≤ 1 / 2 := by
    rw [ht₁, mul_one_div, div_le_iff₀ (by positivity), hN]
    linarith
  have e2 : CSs * t₂ ≤ 1 / 2 := by
    rw [ht₂, mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  set Cc₀ : ℝ := (∑ l, Cl l * t₁ ^ (-γl l)) + CSs * (C₂ * t₂ ^ (-γ₂) + CH₂) with hCc₀
  have hCc₀0 : 0 ≤ Cc₀ :=
    add_nonneg (Finset.sum_nonneg fun l _ => mul_nonneg (hCl l).le (Real.rpow_nonneg ht₁0.le _))
      (mul_nonneg hCSs0 (add_nonneg (mul_nonneg hC₂.le (Real.rpow_nonneg ht₂0.le _)) hCH₂.le))
  refine ⟨γs, Cc₀ + 1, hγs1, by linarith, ?_⟩
  intro ε hε0 hε1 v D hv hD hav
  set Sg : ℝ≥0∞ := ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |weakSumSquares D [] x|
    with hSg
  set Sv : ℝ≥0∞ := ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |v x| with hSv
  have hvc : ContinuousOn v (F.V : Set (Fin (n + m) → ℝ)) :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0 hv.1.1
  have hvm : AEStronglyMeasurable v (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
    hvc.aestronglyMeasurable F.V.isOpen.measurableSet
  obtain ⟨hleft, hDl⟩ := hid v D hv hD hav
  have hvnorm : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) v ≤
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (P₂.apply (weakSumSquares D [])) +
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (F₂.apply v) := by
    calc holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) v =
          holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
          (fun ξ => P₂.apply (weakSumSquares D []) ξ + F₂.apply v ξ) :=
          S.holderENorm_congr C.dl α (F.V : Set (Fin (n + m) → ℝ)) v hleft
      _ ≤ _ := holderENorm_add_le hα0.le _ _
  have hl : ∀ l : Fin q, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D [l]) ≤
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) ((Fl l).apply (weakSumSquares D [])) +
        ENNReal.ofReal (CSl l) * (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
            (P₂.apply (weakSumSquares D [])) +
          holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (F₂.apply v)) := by
    intro l
    calc holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D [l]) =
          holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
          (fun ξ => (Fl l).apply (weakSumSquares D []) ξ + (Sl l).apply v ξ) :=
          (S.holderENorm_congr C.dl α (F.V : Set (Fin (n + m) → ℝ)) _ (hDl l)).symm
      _ ≤ holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) ((Fl l).apply (weakSumSquares D [])) +
          holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) ((Sl l).apply v) :=
          holderENorm_add_le hα0.le _ _
      _ ≤ holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) ((Fl l).apply (weakSumSquares D [])) +
          ENNReal.ofReal (CSl l) * holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) v :=
          add_le_add le_rfl (hCSb l v)
      _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl hvnorm)
  -- the interpolation bounds
  have IB1 : ∀ l : Fin q, InterpBound
      (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) ((Fl l).apply (weakSumSquares D [])))
      Sg Sv t₁ (Cl l * t₁ ^ (-γl l)) γs := fun l =>
    ((InterpBound.of_bound (hCl l).le
      (fun ε hε0 hε1 => hAl l ε hε0 hε1 v D hv hD)).scale ht₁0 ht₁1).mono le_rfl le_rfl (hγle l)
  have IBP : InterpBound (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
      (P₂.apply (weakSumSquares D []))) Sg Sv t₂ (C₂ * t₂ ^ (-γ₂)) γs :=
    ((InterpBound.of_bound hC₂.le
      (fun ε hε0 hε1 => hA₂ ε hε0 hε1 v D hv hD)).scale ht₂0 ht₂1).mono le_rfl le_rfl hγ₂le
  have IBF : InterpBound (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (F₂.apply v)) Sg Sv 0
      CH₂ γs :=
    (InterpBound.of_const hCH₂.le (hF₂b v hvm)).mono le_rfl le_rfl (by linarith)
  have IBv := IBP.add IBF
  have IBl : ∀ l : Fin q, InterpBound
      (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) ((Fl l).apply (weakSumSquares D [])) +
        ENNReal.ofReal (CSl l) * (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
            (P₂.apply (weakSumSquares D [])) +
          holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (F₂.apply v))) Sg Sv
      (t₁ + CSl l * (t₂ + 0))
      (Cl l * t₁ ^ (-γl l) + CSl l * (C₂ * t₂ ^ (-γ₂) + CH₂)) γs := fun l =>
    (IB1 l).add (IBv.const_mul (hCSl l).le)
  have IBsum := InterpBound.sum Finset.univ (fun l (_ : l ∈ Finset.univ) => IBl l)
  have hs : ∑ l : Fin q, (t₁ + CSl l * (t₂ + 0)) ≤ 1 := by
    simp only [add_zero]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.sum_mul]
    linarith
  have hc : ∑ l : Fin q, (Cl l * t₁ ^ (-γl l) + CSl l * (C₂ * t₂ ^ (-γ₂) + CH₂)) ≤ Cc₀ + 1 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    linarith
  have IBfin := (IBsum.of_le (Finset.sum_le_sum fun l _ => hl l)).mono hs hc le_rfl
  have := IBfin.2.2 ε hε0 hε1
  simpa only [one_mul] using this

end RothschildStein.P2
