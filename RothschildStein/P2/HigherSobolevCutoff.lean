-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherSobolevRegular
public import RothschildStein.P2.SobolevInterpolationNoDriftNhds
public import RothschildStein.P2.TransferCoverSobolev
public import RothschildStein.S.ClassicalWords
public import RothschildStein.S.Leibniz

/-!
# Higher Sobolev estimate, step 1: the cutoff recurrence on the `ρ`-balls

Part of the higher Sobolev estimate (BB pp. 589–590, Prop 11.47, (11.73)). Let `U_R = U_R^ρ` be the `ρ`-balls of the chart centre, `a = 1` on
`U_R ⊆ V`, and `η = η_R ∈ C_c^∞(U_R)` with `η = 1` on `U_{R/2}` (the radial cutoff construction). For `u ∈ W^{L,p}(U_R)` with
`L̃ u = f ∈ W^{N,p}(U_R)` (`N + 1 ≤ L`) the function `v = η u` is compactly supported in `U_R`, lies in
`W^{L,p}(V)` and `L̃ v = η f + 2 ∑_i (X̃_i η)(X̃_i u) + (L̃ η) u ∈ W^{N,p}(V)` (the weak square product rule
`S.hasWeakWordDeriv_mul_square`), with norms bounded by `‖f‖_{W^N(U_R)} + ‖u‖_{W^{N+1}(U_R)}`
(`cutoff_package`). Consequently

* (`cutoffEstimate`) `‖u‖_{W^{j+2,p}(U_{R/2})} ≤ C (‖L̃ u‖_{W^{j,p}(U_R)} + ‖u‖_{W^{j+1,p}(U_R)})`
  (the compact recurrence of `compactRecurrence` applied to `v`), and
* (`cutoffRegularity`) `u ∈ W^{j+2,p}(U_R)`, `L̃ u ∈ W^{j+1,p}(U_R)` imply `u ∈ W^{j+3,p}(U_{R/2})`
  (the regularity step `regularityStep` applied to `v`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

section Product

variable {d k : ℕ} {w : Fin k → ℕ+} {Xt : Fin k → (Fin d → ℝ) → (Fin d → ℝ)}

/-- The multiplication by a fixed test function is bounded on `W^{n',P}(U)`. -/
theorem exists_mul_test_const {U : Opens (Fin d → ℝ)}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (U : Set (Fin d → ℝ))) {P : ℝ≥0∞} (hP : 1 ≤ P)
    (n' : ℕ) (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ f : (Fin d → ℝ) → ℝ, memSobolevX w Xt U n' P f →
      sobolevXENorm w Xt U n' P (fun x => f x * φ x) ≤ c * sobolevXENorm w Xt U n' P f := by
  refine ⟨(((2 ^ n' * (wordFamily w n').card : ℕ) : ℝ≥0∞)) *
      RothschildStein.S.cutoffWordENorm w Xt U n' φ,
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (RothschildStein.S.cutoffWordENorm_lt_top w Xt U hXt n' φ).ne, fun f hf => ?_⟩
  exact RothschildStein.S.sobolevXENorm_mul_test_le w Xt U hXt n' P hP f hf φ

end Product

section Cutoff

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)} {q₀ : ℕ}
  {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {a : TestFunction F.V ℝ (⊤ : ℕ∞)}

/-- **The cutoff package.** Let `U ⊆ F.V` be open with `a = 1` on `U` and
`η ∈ C_c^∞(U)`. For `N + 1 ≤ L` there is a finite constant `M` such that for every `u ∈ W^{L,P}(U)` with
`L̃ u = f ∈ W^{N,P}(U)`, the function `v = η u`
is compactly supported in `U`, lies in `W^{L,P}(F.V)` with `‖v‖_{W^{N+1}(V)} ≤ M ‖u‖_{W^{N+1}(U)}`, and
`L̃ v = g` weakly on `F.V` with `g ∈ W^{N,P}(F.V)` and `‖g‖_{W^N(V)} ≤ M (‖f‖_{W^N(U)} + ‖u‖_{W^{N+1}(U)})`. -/
theorem cutoff_package (hH : HigherFrame C H K hQ F a) {P : ℝ≥0∞} (hP1 : 1 < P)
    {U : Opens (Fin (n + m) → ℝ)} (hUV : (U : Set (Fin (n + m) → ℝ)) ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    (hUa : ∀ x ∈ (U : Set (Fin (n + m) → ℝ)), a x = 1) (η : TestFunction U ℝ (⊤ : ℕ∞))
    (N L : ℕ) (hNL : N + 1 ≤ L) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ u f : (Fin (n + m) → ℝ) → ℝ,
      memSobolevX w C.Xl U L P u → HasWeakOperatorValue C.Xl U (noDriftOpWords q) u f →
      memSobolevX w C.Xl U N P f →
      memSobolevX w C.Xl F.V L P (fun x => u x * η x) ∧ HasCompactSupport (fun x => u x * η x) ∧
      tsupport (fun x => u x * η x) ⊆ (F.V : Set (Fin (n + m) → ℝ)) ∧
      (∀ x ∈ tsupport (fun x => u x * η x), a x = 1) ∧
      sobolevXENorm w C.Xl F.V (N + 1) P (fun x => u x * η x) ≤
        M * sobolevXENorm w C.Xl U (N + 1) P u ∧
      ∃ g : (Fin (n + m) → ℝ) → ℝ,
        HasWeakOperatorValue C.Xl F.V (noDriftOpWords q) (fun x => u x * η x) g ∧
        memSobolevX w C.Xl F.V N P g ∧
        sobolevXENorm w C.Xl F.V N P g ≤
          M * (sobolevXENorm w C.Xl U N P f + sobolevXENorm w C.Xl U (N + 1) P u) := by
  have hP : (1 : ℝ≥0∞) ≤ P := hP1.le
  have : Fact (1 ≤ P) := ⟨hP⟩
  have hw := hH.weight
  have hXU : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (U : Set (Fin (n + m) → ℝ)) :=
    fun i => (hH.contDiffOn_Xl i).mono hUV
  have hηc : ContDiffOn ℝ (⊤ : ℕ∞) (η : (Fin (n + m) → ℝ) → ℝ) (U : Set (Fin (n + m) → ℝ)) :=
    η.contDiff.contDiffOn
  obtain ⟨c₁, hc₁, hb₁⟩ := exists_mul_test_const (w := w) hXU hP (N + 1) η
  obtain ⟨c₀, hc₀, hb₀⟩ := exists_mul_test_const (w := w) hXU hP N η
  choose cA hcA hbA using fun i : Fin q => exists_mul_test_const (w := w) hXU hP N
    (RothschildStein.S.wordDerivativeTest U C.Xl hXU [i] η)
  choose cB hcB hbB using fun i : Fin q => exists_mul_test_const (w := w) hXU hP N
    (RothschildStein.S.wordDerivativeTest U C.Xl hXU [i, i] η)
  refine ⟨c₁ + c₀ + ∑ i, (2 * cA i + cB i),
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hc₁, hc₀⟩, ENNReal.sum_ne_top.2 fun i _ =>
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top (hcA i), hcB i⟩⟩,
    fun u f hu hop hf => ?_⟩
  set v : (Fin (n + m) → ℝ) → ℝ := fun x => u x * η x with hv
  have hvU : memSobolevX w C.Xl U L P v :=
    RothschildStein.S.memSobolevX_mul_test w C.Xl U hXU L P hP u hu η
  have hcv : HasCompactSupport v := η.hasCompactSupport.mul_left
  have hsv : tsupport v ⊆ (U : Set (Fin (n + m) → ℝ)) :=
    tsupport_mul_subset_right.trans η.tsupport_subset
  have hvV : memSobolevX w C.Xl F.V L P v := memSobolevX_extend hUV hvU hcv hsv
  have huN1 : memSobolevX w C.Xl U (N + 1) P u :=
    RothschildStein.S.memSobolevX_mono_order w C.Xl U hNL hu
  have huN : memSobolevX w C.Xl U N P u :=
    RothschildStein.S.memSobolevX_mono_order w C.Xl U (Nat.le_succ N) huN1
  have hM1 : c₁ ≤ c₁ + c₀ + ∑ i, (2 * cA i + cB i) := le_self_add.trans le_self_add
  have hM2 : c₀ ≤ c₁ + c₀ + ∑ i, (2 * cA i + cB i) := le_add_self.trans le_self_add
  have hM3 : (∑ i, (2 * cA i + cB i)) ≤ c₁ + c₀ + ∑ i, (2 * cA i + cB i) := le_add_self
  refine ⟨hvV, hcv, hsv.trans hUV, fun x hx => hUa x (hsv hx), ?_, ?_⟩
  · have hvV' : memSobolevX w C.Xl F.V (N + 1) P v :=
      RothschildStein.S.memSobolevX_mono_order w C.Xl F.V hNL hvV
    rw [RothschildStein.S.sobolevXENorm_eq_of_compact_support w C.Xl F.V U hUV (N + 1) hvV' hcv hsv]
    exact (hb₁ u huN1).trans (mul_le_mul' hM1 le_rfl)
  · -- the operator value of the cutoff function
    obtain ⟨D, hD⟩ := IsWeakJet.exists huN1
    obtain ⟨gop, hgop, hfae⟩ := hop
    have h1mem : ∀ i : Fin q, [i] ∈ wordFamily w (N + 1) := fun i => by
      rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]
      simp
    let ηi : Fin q → (Fin (n + m) → ℝ) → ℝ := fun i => fieldDerivative (C.Xl i) η
    let ηii : Fin q → (Fin (n + m) → ℝ) → ℝ :=
      fun i => fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i) η)
    have hq : ∀ i : Fin q, hasWeakWordDeriv C.Xl U [i, i] v
        (fun x => gop i x * η x + 2 * D [i] x * ηi i x + u x * ηii i x) := fun i =>
      RothschildStein.S.hasWeakWordDeriv_mul_square C.Xl U hXU i u (D [i]) (gop i) η hηc
        (hD [i] (h1mem i)).1 (hgop i)
    let gU : (Fin (n + m) → ℝ) → ℝ := fun x =>
      f x * η x + ∑ i, (2 * (D [i] x * ηi i x) + u x * ηii i x)
    have hgUop : HasWeakOperatorValue C.Xl U (noDriftOpWords q) v gU := by
      refine ⟨fun i x => gop i x * η x + 2 * D [i] x * ηi i x + u x * ηii i x, hq, ?_⟩
      filter_upwards [hfae] with x hx
      show f x * η x + ∑ i, (2 * (D [i] x * ηi i x) + u x * ηii i x) =
        ∑ i, (gop i x * η x + 2 * D [i] x * ηi i x + u x * ηii i x)
      calc f x * η x + ∑ i, (2 * (D [i] x * ηi i x) + u x * ηii i x)
          = (∑ i, gop i x) * η x + ∑ i, (2 * (D [i] x * ηi i x) + u x * ηii i x) := by rw [hx]
        _ = ∑ i, (gop i x * η x + (2 * (D [i] x * ηi i x) + u x * ηii i x)) := by
            rw [Finset.sum_mul]
            exact Finset.sum_add_distrib.symm
        _ = _ := Finset.sum_congr rfl fun i _ => by ring
    -- membership and norm of `gU` on `U`
    have hA : memSobolevX w C.Xl U N P (fun x => f x * η x) :=
      RothschildStein.S.memSobolevX_mul_test w C.Xl U hXU N P hP f hf η
    have hDi : ∀ i, memSobolevX w C.Xl U N P (D [i]) := fun i =>
      (memSobolevX_jet_deriv hXU hw hD i).1
    have hB1 : ∀ i, memSobolevX w C.Xl U N P (fun x => D [i] x * ηi i x) := fun i =>
      RothschildStein.S.memSobolevX_mul_test w C.Xl U hXU N P hP (D [i]) (hDi i)
        (RothschildStein.S.wordDerivativeTest U C.Xl hXU [i] η)
    have hB2 : ∀ i, memSobolevX w C.Xl U N P (fun x => u x * ηii i x) := fun i =>
      RothschildStein.S.memSobolevX_mul_test w C.Xl U hXU N P hP u huN
        (RothschildStein.S.wordDerivativeTest U C.Xl hXU [i, i] η)
    have hT : ∀ i, memSobolevX w C.Xl U N P (fun x => 2 * (D [i] x * ηi i x) + u x * ηii i x) :=
      fun i => memSobolevX_add' hXU (memSobolevX_const_mul 2 (hB1 i)) (hB2 i)
    have hsumT : memSobolevX w C.Xl U N P
        (fun x => ∑ i, (2 * (D [i] x * ηi i x) + u x * ηii i x)) :=
      memSobolevX_finset_sum hXU Finset.univ fun i _ => hT i
    have hgU : memSobolevX w C.Xl U N P gU := memSobolevX_add' hXU hA hsumT
    have hnormT : ∀ i, sobolevXENorm w C.Xl U N P
        (fun x => 2 * (D [i] x * ηi i x) + u x * ηii i x) ≤
        (2 * cA i + cB i) * sobolevXENorm w C.Xl U (N + 1) P u := by
      intro i
      refine (sobolevXENorm_add_le' hXU hP (memSobolevX_const_mul 2 (hB1 i)) (hB2 i)).trans ?_
      rw [sobolevXENorm_const_mul 2 (hB1 i)]
      have e2 : ENNReal.ofReal |(2 : ℝ)| = 2 := by simp
      rw [e2]
      have h1 : sobolevXENorm w C.Xl U N P (fun x => D [i] x * ηi i x) ≤
          cA i * sobolevXENorm w C.Xl U (N + 1) P u :=
        (hbA i (D [i]) (hDi i)).trans (mul_le_mul' le_rfl (memSobolevX_jet_deriv hXU hw hD i).2)
      have h2 : sobolevXENorm w C.Xl U N P (fun x => u x * ηii i x) ≤
          cB i * sobolevXENorm w C.Xl U (N + 1) P u :=
        (hbB i u huN).trans (mul_le_mul' le_rfl (sobolevXENorm_mono_order (Nat.le_succ N) u))
      calc 2 * sobolevXENorm w C.Xl U N P (fun x => D [i] x * ηi i x) +
            sobolevXENorm w C.Xl U N P (fun x => u x * ηii i x)
          ≤ 2 * (cA i * sobolevXENorm w C.Xl U (N + 1) P u) +
            cB i * sobolevXENorm w C.Xl U (N + 1) P u := add_le_add (mul_le_mul' le_rfl h1) h2
        _ = (2 * cA i + cB i) * sobolevXENorm w C.Xl U (N + 1) P u := by ring
    have hnormG : sobolevXENorm w C.Xl U N P gU ≤
        (c₁ + c₀ + ∑ i, (2 * cA i + cB i)) *
          (sobolevXENorm w C.Xl U N P f + sobolevXENorm w C.Xl U (N + 1) P u) := by
      calc sobolevXENorm w C.Xl U N P gU
          ≤ sobolevXENorm w C.Xl U N P (fun x => f x * η x) +
            sobolevXENorm w C.Xl U N P
              (fun x => ∑ i, (2 * (D [i] x * ηi i x) + u x * ηii i x)) :=
            sobolevXENorm_add_le' hXU hP hA hsumT
        _ ≤ sobolevXENorm w C.Xl U N P (fun x => f x * η x) +
            ∑ i, sobolevXENorm w C.Xl U N P (fun x => 2 * (D [i] x * ηi i x) + u x * ηii i x) :=
            add_le_add le_rfl (sobolevXENorm_finset_sum_le hXU _ hP fun i _ => hT i)
        _ ≤ c₀ * sobolevXENorm w C.Xl U N P f +
            ∑ i, (2 * cA i + cB i) * sobolevXENorm w C.Xl U (N + 1) P u :=
            add_le_add (hb₀ f hf) (Finset.sum_le_sum fun i _ => hnormT i)
        _ = c₀ * sobolevXENorm w C.Xl U N P f +
            (∑ i, (2 * cA i + cB i)) * sobolevXENorm w C.Xl U (N + 1) P u := by
            rw [Finset.sum_mul]
        _ ≤ (c₁ + c₀ + ∑ i, (2 * cA i + cB i)) * sobolevXENorm w C.Xl U N P f +
            (c₁ + c₀ + ∑ i, (2 * cA i + cB i)) * sobolevXENorm w C.Xl U (N + 1) P u :=
            add_le_add (mul_le_mul' hM2 le_rfl) (mul_le_mul' hM3 le_rfl)
        _ = _ := (mul_add _ _ _).symm
    -- extension by zero to `F.V`
    have hηz : ∀ x, x ∉ tsupport (η : (Fin (n + m) → ℝ) → ℝ) → η x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport hx
    have hηiz : ∀ i, ∀ x, x ∉ tsupport (η : (Fin (n + m) → ℝ) → ℝ) → ηi i x = 0 := fun i x hx =>
      image_eq_zero_of_notMem_tsupport (fun h =>
        hx (RothschildStein.S.tsupport_fieldDerivative_subset (C.Xl i) _ h))
    have hηiiz : ∀ i, ∀ x, x ∉ tsupport (η : (Fin (n + m) → ℝ) → ℝ) → ηii i x = 0 := fun i x hx =>
      image_eq_zero_of_notMem_tsupport (fun h =>
        hx (RothschildStein.S.tsupport_fieldDerivative_subset (C.Xl i) _
          (RothschildStein.S.tsupport_fieldDerivative_subset (C.Xl i) _ h)))
    have hgz : ∀ x, x ∉ tsupport (η : (Fin (n + m) → ℝ) → ℝ) → gU x = 0 := by
      intro x hx
      show f x * η x + ∑ i, (2 * (D [i] x * ηi i x) + u x * ηii i x) = 0
      rw [hηz x hx]
      simp [hηiz _ x hx, hηiiz _ x hx]
    have hvz : ∀ x, x ∉ tsupport (η : (Fin (n + m) → ℝ) → ℝ) → v x = 0 := fun x hx => by
      show u x * η x = 0
      rw [hηz x hx, mul_zero]
    have hgop' := HasWeakOperatorValue.extend hUV η.hasCompactSupport η.tsupport_subset hvz hgUop
    rw [indicator_eq_self_of_zero_off η.tsupport_subset hgz] at hgop'
    have hcg : HasCompactSupport gU := HasCompactSupport.intro η.hasCompactSupport hgz
    have hsg : tsupport gU ⊆ (U : Set (Fin (n + m) → ℝ)) :=
      (closure_minimal (fun x hx => by
        by_contra hxn
        exact hx (hgz x hxn)) (isClosed_tsupport _)).trans η.tsupport_subset
    have hgV : memSobolevX w C.Xl F.V N P gU := memSobolevX_extend hUV hgU hcg hsg
    refine ⟨gU, hgop', hgV, ?_⟩
    rw [RothschildStein.S.sobolevXENorm_eq_of_compact_support w C.Xl F.V U hUV N hgV hcg hsg]
    exact hnormG

/-! ### Good radii -/

/-- The radii `R < R₀` for which the `ρ`-ball `U_R` of the centre lies in the cutoff region `F.V`, the
cutoff `a` is `1` on it, and there is a cutoff `η ∈ C_c^∞(U_R)` with `η = 1` on `U_{R/2}`. -/
def GoodRadius (C : LiftedChart w s Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G) (F : KernelFrame (n + m))
    (a : TestFunction F.V ℝ (⊤ : ℕ∞)) (R₀ : ℝ) : Prop :=
  0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
    (rhoBallOpen C ν R : Set (Fin (n + m) → ℝ)) ⊆ (F.V : Set (Fin (n + m) → ℝ)) ∧
    (∀ x ∈ (rhoBallOpen C ν R : Set (Fin (n + m) → ℝ)), a x = 1) ∧
    ∃ η : TestFunction (rhoBallOpen C ν R) ℝ (⊤ : ℕ∞),
      ∀ x ∈ (rhoBallOpen C ν (R / 2) : Set (Fin (n + m) → ℝ)), η x = 1

theorem exists_goodRadius (hH : HigherFrame C H K hQ F a) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) : ∃ R₀ : ℝ, GoodRadius C ν F a R₀ := by
  obtain ⟨rstar, hr0, hr1, hq, -⟩ := exists_radialCutoff C ν hν
    (Kc := {joinPoint x₀ (0 : Fin m → ℝ)}) isCompact_singleton (by simpa using C.center_mem)
  obtain ⟨r₂, hr₂, hsub⟩ := exists_rhoBall_subset_of_mem_nhds_noDrift C ν C.center_mem hH.near
  refine ⟨min rstar r₂, lt_min hr0 hr₂, fun R hR hRR => ?_⟩
  have hRr : R < rstar := hRR.trans_le (min_le_left _ _)
  have hRr₂ : R ≤ r₂ := hRR.le.trans (min_le_right _ _)
  have hsubR := hsub R hRr₂
  refine ⟨fun x hx => (hsubR hx).1, fun x hx => (hsubR hx).2, ?_⟩
  obtain ⟨hcd, hcs, -, heq, hts, hcl⟩ := hq _ (mem_singleton _) (R / 2) R (half_pos hR)
    (by linarith) hRr
  exact ⟨⟨radialCutoff C ν _ (R / 2) R, hcd, hcs, hts.trans hcl⟩, fun x hx => heq hx⟩

/-! ### The cutoff estimate and the cutoff regularity -/

variable {ν : G2.HomogeneousNorm C.G} {R₀ : ℝ}

/-- **The cutoff recurrence**
`‖u‖_{W^{j+2,p}(U_{R/2})} ≤ C (‖L̃ u‖_{W^{j,p}(U_R)} + ‖u‖_{W^{j+1,p}(U_R)})` (BB p. 589, (11.73)) for
`u ∈ W^{j+2,p}(U_R)`, `R < R₀`. -/
theorem cutoffEstimate (hH : HigherFrame C H K hQ F a) (hg : GoodRadius C ν F a R₀) {P : ℝ≥0∞}
    (hP1 : 1 < P) (hPt : P ≠ ⊤) (j : ℕ) {R : ℝ} (hR : 0 < R) (hRR : R < R₀) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ u f : (Fin (n + m) → ℝ) → ℝ,
      memSobolevX w C.Xl (rhoBallOpen C ν R) (j + 2) P u →
      HasWeakOperatorValue C.Xl (rhoBallOpen C ν R) (noDriftOpWords q) u f →
      memSobolevX w C.Xl (rhoBallOpen C ν R) j P f →
      sobolevXENorm w C.Xl (rhoBallOpen C ν (R / 2)) (j + 2) P u ≤
        ENNReal.ofReal Cst * (sobolevXENorm w C.Xl (rhoBallOpen C ν R) j P f +
          sobolevXENorm w C.Xl (rhoBallOpen C ν R) (j + 1) P u) := by
  obtain ⟨hUV, hUa, η, hη⟩ := hg.2 R hR hRR
  obtain ⟨M, hM, hpk⟩ := cutoff_package hH hP1 hUV hUa η j (j + 2) (by omega)
  obtain ⟨Λ, hΛ, hrec⟩ := compactRecurrence hH hP1 hPt j
  have h2M : 2 * M ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hM
  refine ⟨Λ * ((2 * M).toReal + 1), mul_pos hΛ (by positivity), fun u f hu hop hf => ?_⟩
  obtain ⟨hvV, hcv, hsv, ha1, hv1, g, hgop, -, hgb⟩ := hpk u f hu hop hf
  have hrecv := hrec _ g hvV hcv hsv ha1 hgop
  have hsub2 : (rhoBallOpen C ν (R / 2) : Set (Fin (n + m) → ℝ)) ⊆
      (F.V : Set (Fin (n + m) → ℝ)) := fun x hx =>
    hUV (rhoBall_mono C ν (joinPoint x₀ (0 : Fin m → ℝ)) (show R / 2 ≤ R by linarith) hx)
  have hae : u =ᵐ[volume.restrict (rhoBallOpen C ν (R / 2) : Set (Fin (n + m) → ℝ))]
      fun x => u x * η x := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (rhoBallOpen C ν (R / 2)).isOpen.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => by
      show u x = u x * η x
      rw [hη x hx, mul_one]
  have hnorm : sobolevXENorm w C.Xl (rhoBallOpen C ν (R / 2)) (j + 2) P u ≤
      sobolevXENorm w C.Xl F.V (j + 2) P (fun x => u x * η x) := by
    rw [RothschildStein.S.sobolevXENorm_congr_ae C.Xl _ w (j + 2) P hae]
    exact sobolevXENorm_mono_domain w C.Xl hsub2 hvV
  set a₁ := sobolevXENorm w C.Xl (rhoBallOpen C ν R) j P f with ha₁
  set a₂ := sobolevXENorm w C.Xl (rhoBallOpen C ν R) (j + 1) P u with ha₂
  have hfin : ENNReal.ofReal ((2 * M).toReal + 1) = 2 * M + 1 := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal h2M,
      ENNReal.ofReal_one]
  calc sobolevXENorm w C.Xl (rhoBallOpen C ν (R / 2)) (j + 2) P u
      ≤ sobolevXENorm w C.Xl F.V (j + 2) P (fun x => u x * η x) := hnorm
    _ ≤ ENNReal.ofReal Λ * (sobolevXENorm w C.Xl F.V j P g +
          sobolevXENorm w C.Xl F.V (j + 1) P (fun x => u x * η x)) := hrecv
    _ ≤ ENNReal.ofReal Λ * (M * (a₁ + a₂) + M * a₂) :=
        mul_le_mul' le_rfl (add_le_add hgb hv1)
    _ ≤ ENNReal.ofReal Λ * ((2 * M + 1) * (a₁ + a₂)) := by
        refine mul_le_mul' le_rfl ?_
        calc M * (a₁ + a₂) + M * a₂ ≤ M * (a₁ + a₂) + M * (a₁ + a₂) :=
              add_le_add le_rfl (mul_le_mul' le_rfl le_add_self)
          _ = 2 * M * (a₁ + a₂) := by ring
          _ ≤ (2 * M + 1) * (a₁ + a₂) := mul_le_mul' le_self_add le_rfl
    _ = ENNReal.ofReal (Λ * ((2 * M).toReal + 1)) * (a₁ + a₂) := by
        rw [ENNReal.ofReal_mul hΛ.le, hfin, mul_assoc]

/-- **The cutoff regularity step**: `u ∈ W^{j+2,p}(U_R)` with
`L̃ u = f ∈ W^{j+1,p}(U_R)` lies in `W^{j+3,p}(U_{R/2})` (`R < R₀`; BB pp. 590-591). -/
theorem cutoffRegularity (hH : HigherFrame C H K hQ F a) (hg : GoodRadius C ν F a R₀) {P : ℝ≥0∞}
    (hP1 : 1 < P) (hPt : P ≠ ⊤) (j : ℕ) {R : ℝ} (hR : 0 < R) (hRR : R < R₀)
    {u f : (Fin (n + m) → ℝ) → ℝ} (hu : memSobolevX w C.Xl (rhoBallOpen C ν R) (j + 2) P u)
    (hop : HasWeakOperatorValue C.Xl (rhoBallOpen C ν R) (noDriftOpWords q) u f)
    (hf : memSobolevX w C.Xl (rhoBallOpen C ν R) (j + 1) P f) :
    memSobolevX w C.Xl (rhoBallOpen C ν (R / 2)) (j + 3) P u := by
  obtain ⟨hUV, hUa, η, hη⟩ := hg.2 R hR hRR
  obtain ⟨M, hM, hpk⟩ := cutoff_package hH hP1 hUV hUa η (j + 1) (j + 2) (by omega)
  obtain ⟨hvV, hcv, hsv, ha1, -, g, hgop, hgmem, -⟩ := hpk u f hu hop hf
  have hreg := regularityStep hH hP1 hPt j hvV hcv hsv ha1 hgop hgmem
  have hsub2 : (rhoBallOpen C ν (R / 2) : Set (Fin (n + m) → ℝ)) ⊆
      (F.V : Set (Fin (n + m) → ℝ)) := fun x hx =>
    hUV (rhoBall_mono C ν (joinPoint x₀ (0 : Fin m → ℝ)) (show R / 2 ≤ R by linarith) hx)
  have hae : u =ᵐ[volume.restrict (rhoBallOpen C ν (R / 2) : Set (Fin (n + m) → ℝ))]
      fun x => u x * η x := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (rhoBallOpen C ν (R / 2)).isOpen.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => by
      show u x = u x * η x
      rw [hη x hx, mul_one]
  exact (RothschildStein.S.memSobolevX_congr_ae C.Xl _ w (j + 3) P hae).2
    (RothschildStein.S.memSobolevX_restrict w C.Xl F.V _ hsub2 hreg)

end Cutoff

end RothschildStein.P2
