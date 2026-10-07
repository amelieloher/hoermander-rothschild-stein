-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsPole
public import RothschildStein.P1.ParametrixKernelBoundsDeriv
public import RothschildStein.P1.RightParametrix

/-!
# Chart bounds (kernel part): the kernels of `P_R` and `F_R^chart` satisfy the kernel bounds

For the right parametrix of the lifted drift chart (BB p. 605, Prop. 11.61)

`P_R f(ξ) = ∫_U p(ξ, η) f(η) dη`, `p(ξ, η) = a(ξ) (b(η)/c(η)) Γ(Θ(η, ξ))`
(`rightParametrixKernel`, `rightParametrix_eq_integral`),

`F_R^chart f(ξ) = ∫_U (-e(ξ, η)) f(η) dη`, `e = rightErrorKernel`
(`rightChartErrorKernel`, `rightChartError_eq_integral`),

this file proves, on every compact `L ⊆ U` (the cutoffs `a, b` and the kernel `Γ` fixed):

* `P_R` has kernel bounds of exponent `2` (type `2`: size `C d̃^(2-Q)`);
* `e` and each of its three components `(b/c) a E_η Γ(Θ)`, `(b/c) 2 ∑ᵢ X̃ᵢ a Zᵢ Γ(Θ)`,
  `(b/c) (L̃ a) Γ(Θ)` has kernel bounds of exponent `1` (size `C d̃^(1-Q)`, difference
  `C h d̃^(-Q)`), and so has `F_R^chart`;
* the kernel of `F_R^chart` satisfies the hypotheses `RestrictedKernelBounds` of the restricted-error bounds, so that
  the small-ball bounds of `RestrictedError*` apply to `F_R^chart` directly (see
  `ParametrixKernelBoundsSol` for the composite statements).

The proof assembles the symbol-class families (`ParametrixKernelBoundsPole`): the extended remainder
fields `Rt` of a chart extension (`exists_chartExt`) agree with the true remainders near the
two-point values `(η, Θ(η, ξ))`, `ξ, η ∈ L`, and the smooth factors `a(ξ)`, `b(η)/c(η)`, `X̃ᵢ a`,
`L̃ a` are globally smooth (their supports lie in `U`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RothschildStein.P1

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function smooth on an open set `U` and vanishing off a closed subset `S ⊆ U` is
globally smooth. -/
theorem contDiff_of_contDiffOn_of_eq_zero {f : E → ℝ} {U S : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hS : IsClosed S) (hSU : S ⊆ U) (h0 : ∀ x ∉ S, f x = 0) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ S
  · exact hf.contDiffAt (hU.mem_nhds (hSU hx))
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hS.isOpen_compl.mem_nhds hx] with y hy
    exact h0 y hy

end Smoothness

section Support

variable {N : ℕ}

/-- The field derivative of `f` vanishes off the support of `f`. -/
theorem fieldDerivative_eq_zero_of_notMem_tsupport {V : (Fin N → ℝ) → (Fin N → ℝ)}
    {f : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (hx : x ∉ tsupport f) : fieldDerivative V f x = 0 := by
  have h : f =ᶠ[nhds x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
  rw [fieldDerivative_congr_eventually h]
  simp [fieldDerivative]

/-- The iterated field derivative of `f` vanishes off the support of `f`. -/
theorem fieldDerivative_fieldDerivative_eq_zero_of_notMem_tsupport {V W : (Fin N → ℝ) → (Fin N → ℝ)}
    {f : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (hx : x ∉ tsupport f) :
    fieldDerivative V (fieldDerivative W f) x = 0 := by
  have h : fieldDerivative W f =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact fieldDerivative_eq_zero_of_notMem_tsupport hy
  rw [fieldDerivative_congr_eventually h]
  simp [fieldDerivative]

end Support

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}

/-- `b/c` is globally smooth for a smooth `b` supported in `U` (the density `c` is smooth
and positive on `U`). -/
theorem contDiff_cutoff_div_density {b : (Fin (n + m) → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ C.U) : ContDiff ℝ (⊤ : ℕ∞) (fun η => b η / C.c η) := by
  have h := RothschildStein.G1.cutoff_smul_contDiff C.isOpen_U (fun η => (C.c η)⁻¹)
    (C.density_smooth.inv (fun η hη => (C.density_pos η hη).ne')) b hb hbs
  simpa [div_eq_mul_inv, smul_eq_mul] using h

/-- `X̃ᵢ a` is globally smooth for a smooth `a` supported in `U`. -/
theorem contDiff_fieldDerivative_Xl {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (has : tsupport a ⊆ C.U) (i : Fin (q + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i) a) :=
  contDiff_of_contDiffOn_of_eq_zero C.isOpen_U (contDiffOn_fieldDerivative_Xl ha.contDiffOn i)
    (isClosed_tsupport a) has (fun _ hx => fieldDerivative_eq_zero_of_notMem_tsupport hx)

/-- `L̃ a` is globally smooth for a smooth `a` supported in `U`. -/
theorem contDiff_sumSquaresWithDrift_Xl {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (has : tsupport a ⊆ C.U) :
    ContDiff ℝ (⊤ : ℕ∞) (sumSquaresWithDrift C.Xl a) := by
  refine contDiff_of_contDiffOn_of_eq_zero C.isOpen_U (contDiffOn_sumSquaresWithDrift_Xl
    ha.contDiffOn) (isClosed_tsupport a) has (fun x hx => ?_)
  unfold sumSquaresWithDrift
  rw [fieldDerivative_eq_zero_of_notMem_tsupport hx, zero_add]
  exact Finset.sum_eq_zero (fun i _ => fieldDerivative_fieldDerivative_eq_zero_of_notMem_tsupport hx)

variable (C) (K a b : (Fin (n + m) → ℝ) → ℝ)

/-- The kernel of the right parametrix `P_R`: `p(ξ, η) = a(ξ) (b(η)/c(η)) Γ(Θ(η, ξ))`
(the definition of `P_R`). -/
def rightParametrixKernel (ξ η : Fin (n + m) → ℝ) : ℝ :=
  a ξ * (b η / C.c η) * K (C.Θ η ξ)

/-- The kernel of the chart error `F_R^chart = -E_R`. -/
def rightChartErrorKernel (ξ η : Fin (n + m) → ℝ) : ℝ := -C.rightErrorKernel K a b ξ η

/-- The three components of the error kernel (from the right pole computation):
`e = (b/c) a E_η Γ(Θ) + (b/c) 2 ∑ᵢ X̃ᵢ a Zᵢ Γ(Θ) + (b/c) (L̃ a) Γ(Θ)`. -/
def errorKernelPole (ξ η : Fin (n + m) → ℝ) : ℝ :=
  b η / C.c η * (a ξ * C.rightPoleError η K (C.Θ η ξ))

/-- The first-order component of the error kernel. -/
def errorKernelZ (i : Fin q) (ξ η : Fin (n + m) → ℝ) : ℝ :=
  b η / C.c η * (2 * (fieldDerivative (C.Xl i.succ) a ξ * C.zDeriv η i.succ K (C.Θ η ξ)))

/-- The cutoff component of the error kernel. -/
def errorKernelGamma (ξ η : Fin (n + m) → ℝ) : ℝ :=
  b η / C.c η * (sumSquaresWithDrift C.Xl a ξ * K (C.Θ η ξ))

/-- The cutoff component of the error kernel as a symbol family. -/
def gammaSymbol : KZ (n + m) → ℝ := fun z =>
  (b z.2.1 / C.c z.2.1 * sumSquaresWithDrift C.Xl a z.1) * kerFam K z

variable {C K a b}

/-- `P_R f(ξ) = ∫_U p(ξ, η) f(η) dη`. -/
theorem rightParametrix_eq_integral (f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) :
    C.rightParametrix K a b f ξ = ∫ η in C.U, C.rightParametrixKernel K a b ξ η * f η := by
  unfold rightParametrix
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun η => by
    simp only [rightParametrixKernel]
    ring)

/-- `F_R^chart f(ξ) = ∫_U (-e(ξ, η)) f(η) dη`. -/
theorem rightChartError_eq_integral (f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) :
    C.rightChartError K a b f ξ = ∫ η in C.U, C.rightChartErrorKernel K a b ξ η * f η := by
  unfold rightChartError rightError
  rw [← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun η => by
    simp only [rightChartErrorKernel]
    ring)

/-- The error kernel is the sum of its three components. -/
theorem rightErrorKernel_eq_sum (ξ η : Fin (n + m) → ℝ) :
    C.rightErrorKernel K a b ξ η = C.errorKernelPole K a b ξ η +
      ∑ i : Fin q, C.errorKernelZ K a b i ξ η + C.errorKernelGamma K a b ξ η := by
  unfold rightErrorKernel errBracket errorKernelPole errorKernelZ errorKernelGamma
  rw [mul_add, mul_add, ← Finset.mul_sum, ← Finset.mul_sum]

variable {K' : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ))} {R : ℝ}

/-- The cutoff component has degree `1 - Q` (the pole has degree `2 - Q`). -/
theorem gammaSymbol_class (hK : IsCompact K') (hR : 0 < R)
    (hΓ : ∀ k : ℕ, WtSym C.G K' R k (2 - (C.G.homogeneousDimension : ℤ)) (kerFam K))
    (hbc : ContDiff ℝ (⊤ : ℕ∞) (fun η => b η / C.c η))
    (hla : ContDiff ℝ (⊤ : ℕ∞) (sumSquaresWithDrift C.Xl a)) (k : ℕ) :
    WtSym C.G K' R k (1 - (C.G.homogeneousDimension : ℤ)) (C.gammaSymbol K a b) :=
  WtSym.mono_d hR (by omega) (WtSym.mul (WtSym.param hK
    (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      b p.2 / C.c p.2 * sumSquaresWithDrift C.Xl a p.1)
    ((hbc.comp contDiff_snd).mul (hla.comp contDiff_fst))) (hΓ k))

/-- On the chart the `Γ`-symbol is the cutoff component of the error kernel. -/
theorem gammaSymbol_eq {ξ η : Fin (n + m) → ℝ} :
    C.gammaSymbol K a b (ξ, η, C.Θ η ξ) = C.errorKernelGamma K a b ξ η := by
  show b η / C.c η * sumSquaresWithDrift C.Xl a ξ * K (C.Θ η ξ) = _
  unfold errorKernelGamma
  ring

namespace ChartExt

variable {L : Set (Fin (n + m) → ℝ)} (ex : C.ChartExt L) (K a b)

/-- The pole component of the error kernel as a symbol family:
`((b/c) a) (ξ, η) · (E Γ)(ξ, η, u)`. -/
def poleSymbol : KZ (n + m) → ℝ := fun z => (b z.2.1 / C.c z.2.1 * a z.1) * ex.errFam K z

/-- The first-order component of the error kernel as a symbol family. -/
def zSymbol (i : Fin q) : KZ (n + m) → ℝ := fun z =>
  (2 * (b z.2.1 / C.c z.2.1 * fieldDerivative (C.Xl i.succ) a z.1)) *
    ex.zFam i.succ (kerFam K) z

/-- The error kernel `e = (b/c)(a E_η Γ + 2 ∑ᵢ X̃ᵢ a ZᵢΓ + (L̃ a) Γ)` as a symbol family. -/
def errorSymbol : KZ (n + m) → ℝ := fun z =>
  ex.poleSymbol K a b z + ∑ i : Fin q, ex.zSymbol K a b i z + C.gammaSymbol K a b z

variable {K a b}

/-- The pole component has degree `1 - Q`. -/
theorem poleSymbol_class (hK : IsCompact K') (hR : 0 < R)
    (hΓ : ∀ k : ℕ, WtSym C.G K' R k (2 - (C.G.homogeneousDimension : ℤ)) (kerFam K))
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hbc : ContDiff ℝ (⊤ : ℕ∞) (fun η => b η / C.c η)) (k : ℕ) :
    WtSym C.G K' R k (1 - (C.G.homogeneousDimension : ℤ)) (ex.poleSymbol K a b) :=
  (WtSym.mul (WtSym.param hK (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
    b p.2 / C.c p.2 * a p.1) ((hbc.comp contDiff_snd).mul (ha.comp contDiff_fst)))
    (ex.errFam_class hK hR hΓ k)).degree_congr (zero_add _)

/-- The first-order component has degree `1 - Q`. -/
theorem zSymbol_class (hK : IsCompact K') (hR : 0 < R)
    (hΓ : ∀ k : ℕ, WtSym C.G K' R k (2 - (C.G.homogeneousDimension : ℤ)) (kerFam K))
    (hbc : ContDiff ℝ (⊤ : ℕ∞) (fun η => b η / C.c η)) (i : Fin q)
    (hxa : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i.succ) a)) (k : ℕ) :
    WtSym C.G K' R k (1 - (C.G.homogeneousDimension : ℤ)) (ex.zSymbol K a b i) :=
  (WtSym.mul (WtSym.param hK (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
    2 * (b p.2 / C.c p.2 * fieldDerivative (C.Xl i.succ) a p.1))
    (contDiff_const.mul ((hbc.comp contDiff_snd).mul (hxa.comp contDiff_fst))))
    (ex.zFam_class hK hR hΓ i.succ k)).degree_congr (by simp [Fin.succ_ne_zero]; ring)

/-- **The error kernel has degree `1 - Q`**: `e` is a symbol of degree `1 - Q` (type `1`). -/
theorem errorSymbol_class (hK : IsCompact K') (hR : 0 < R)
    (hΓ : ∀ k : ℕ, WtSym C.G K' R k (2 - (C.G.homogeneousDimension : ℤ)) (kerFam K))
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hbc : ContDiff ℝ (⊤ : ℕ∞) (fun η => b η / C.c η))
    (hxa : ∀ i : Fin q, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i.succ) a))
    (hla : ContDiff ℝ (⊤ : ℕ∞) (sumSquaresWithDrift C.Xl a)) (k : ℕ) :
    WtSym C.G K' R k (1 - (C.G.homogeneousDimension : ℤ)) (ex.errorSymbol K a b) :=
  WtSym.add (WtSym.add (ex.poleSymbol_class hK hR hΓ ha hbc k)
    (WtSym.sum Finset.univ _ (fun i _ => ex.zSymbol_class hK hR hΓ hbc i (hxa i) k)))
    (gammaSymbol_class hK hR hΓ hbc hla k)

/-- On the chart the pole symbol is the pole component of the error kernel. -/
theorem poleSymbol_eq (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ)) {ξ η : Fin (n + m) → ℝ}
    (hu : C.Θ η ξ ≠ 0) (hV : (η, C.Θ η ξ) ∈ ex.V) :
    ex.poleSymbol K a b (ξ, η, C.Θ η ξ) = C.errorKernelPole K a b ξ η := by
  show b η / C.c η * a ξ * ex.errFam K (ξ, η, C.Θ η ξ) = _
  rw [ex.errFam_eq hΓ hu hV]
  unfold errorKernelPole
  ring

/-- On the chart the `Z`-symbol is the first-order component of the error kernel. -/
theorem zSymbol_eq (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ)) (i : Fin q) {ξ η : Fin (n + m) → ℝ}
    (hu : C.Θ η ξ ≠ 0) (hV : (η, C.Θ η ξ) ∈ ex.V) :
    ex.zSymbol K a b i (ξ, η, C.Θ η ξ) = C.errorKernelZ K a b i ξ η := by
  show 2 * (b η / C.c η * fieldDerivative (C.Xl i.succ) a ξ) *
    ex.zFam i.succ (kerFam K) (ξ, η, C.Θ η ξ) = _
  rw [ex.zFam_eq hΓ i.succ hu hV]
  unfold errorKernelZ
  ring

/-- **The error symbol is the error kernel** at `(ξ, η, Θ(η, ξ))` whenever `u = Θ(η, ξ) ≠ 0`
and `(η, u) ∈ V`. -/
theorem errorSymbol_eq (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ)) {ξ η : Fin (n + m) → ℝ}
    (hu : C.Θ η ξ ≠ 0) (hV : (η, C.Θ η ξ) ∈ ex.V) :
    ex.errorSymbol K a b (ξ, η, C.Θ η ξ) = C.rightErrorKernel K a b ξ η := by
  rw [rightErrorKernel_eq_sum]
  show ex.poleSymbol K a b (ξ, η, C.Θ η ξ) + ∑ i : Fin q, ex.zSymbol K a b i (ξ, η, C.Θ η ξ) +
    C.gammaSymbol K a b (ξ, η, C.Θ η ξ) = _
  rw [ex.poleSymbol_eq hΓ hu hV, gammaSymbol_eq]
  congr 2
  exact Finset.sum_congr rfl (fun i _ => ex.zSymbol_eq hΓ i hu hV)

end ChartExt

section Main

variable {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
  (a b : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
  {L : Set (Fin (n + m) → ℝ)}

/-- `b/c` is globally smooth. -/
theorem contDiff_cutoff_b : ContDiff ℝ (⊤ : ℕ∞) (fun η => b η / C.c η) :=
  contDiff_cutoff_div_density b.contDiff b.tsupport_subset

/-- **The kernel of `F_R^chart` satisfies the hypotheses of the restricted-error bounds**
on every compact `K₀ ⊆ U`: `RestrictedKernelBounds K₀ (-e)` (size `A d̃^(1-Q)`, difference
`B d̃(ξ, ξ')/d̃(ξ', η)^Q`, measurable cut kernel). So the small-ball `L^p`, sup and Hölder bounds
of `RestrictedError*` apply to `F_R^chart` directly. -/
theorem exists_restrictedKernelBounds_rightChartErrorKernel {K₀ : Set (Fin (n + m) → ℝ)}
    (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U) :
    ∃ A B : ℝ, C.RestrictedKernelBounds K₀ (C.rightChartErrorKernel K a b) A B := by
  obtain ⟨ex⟩ := C.exists_chartExt hK₀ hK₀U
  have hbc := contDiff_cutoff_b (C := C) b
  have hxa : ∀ i : Fin q, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i.succ) a) := fun i =>
    contDiff_fieldDerivative_Xl a.contDiff a.tsupport_subset i.succ
  have hla := contDiff_sumSquaresWithDrift_Xl (C := C) a.contDiff a.tsupport_subset
  refine exists_restrictedKernelBounds_of_wtSym hK₀ hK₀U
    (A := fun z : KZ (n + m) => (-1) * ex.errorSymbol (K : (Fin (n + m) → ℝ) → ℝ) a b z)
    (fun L' hL' R hR => (WtSym.smul (-1) (ex.errorSymbol_class (hL'.prod hL') hR
      (fun k => wtSym_kerFam_fundamental K _ _) a.contDiff hbc hxa hla 1)).degree_congr
      (by simp)) (fun ξ hξ η hη hne => ?_)
  have he := ex.errorSymbol_eq (a := ⇑a) (b := ⇑b) K.smooth_off_zero (C.theta_ne_zero (hK₀U hη) (hK₀U hξ) hne)
    (ex.mem_V η hη ξ hξ)
  show C.rightChartErrorKernel K a b ξ η =
    -1 * ex.errorSymbol (K : (Fin (n + m) → ℝ) → ℝ) a b (ξ, η, C.Θ η ξ)
  rw [he]
  unfold rightChartErrorKernel
  ring

end Main

end LiftedChart

end RothschildStein.P1
