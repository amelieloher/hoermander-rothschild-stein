-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FractionalInterpolationNear
public import RothschildStein.P2.FractionalInterpolationOperator
public import RothschildStein.P2.FractionalInterpolationEuclid
public import RothschildStein.P1.ContinuityPositiveShell

/-!
# Hölder interpolation: the principal-term inequality

For one principal term `t` of positive type (`deg D ≤ 1`), the operator `f ↦ ∫ k(·, η) f(η) dη`
applied to `f = L̃ v` splits at the scale `h` into the near part (`‖·‖_{C^α} ≤ C h^{1-α} ‖f‖_∞`,
`exists_near_bound`) and the far part (one integration by parts, `‖·‖_{C^α} ≤ C h^{-M} ‖v‖_∞`,
`far_estimate` with the jets `exists_farKernel_jetSup`), BB pp. 594-595, Lem 11.51. The Euclidean
Lipschitz bound of the far kernel is transferred to the lifted control distance by
`exists_norm_le_mul_dl`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- `Lop` is, on the lifted domain `O`, a second-order operator in coordinates with `C²`
and `C¹` coefficients (`diffOp2`); this holds for `L̃ = ∑ X̃ᵢ² + X̃₀` and `L̃ = ∑ X̃ᵢ²`. -/
def IsCoordinateOp (C : LiftedChart w st Ω hΩ X x₀ m)
    (Lop : ((Fin (n + m) → ℝ) → ℝ) → (Fin (n + m) → ℝ) → ℝ) : Prop :=
  ∃ (A : Fin (n + m) → Fin (n + m) → (Fin (n + m) → ℝ) → ℝ)
    (B : Fin (n + m) → (Fin (n + m) → ℝ) → ℝ),
    (∀ a b, ContDiffOn ℝ 2 (A a b) C.O) ∧ (∀ a, ContDiffOn ℝ 1 (B a) C.O) ∧
    ∀ f : (Fin (n + m) → ℝ) → ℝ, ContDiffOn ℝ 2 f C.O → ∀ x ∈ C.O, Lop f x = diffOp2 A B f x

theorem continuousOn_diffOp2 {N : ℕ} {O : Set (Fin N → ℝ)} (hO : IsOpen O)
    {A : Fin N → Fin N → (Fin N → ℝ) → ℝ} {B : Fin N → (Fin N → ℝ) → ℝ}
    (hA : ∀ a b, ContDiffOn ℝ 2 (A a b) O) (hB : ∀ a, ContDiffOn ℝ 1 (B a) O)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f O) : ContinuousOn (diffOp2 A B f) O := by
  unfold diffOp2
  have h1 : ∀ b, ContDiffOn ℝ 1 (pdv b f) O := fun b => contDiffOn_pdv (n := 1) hO hf b
  refine (continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ => ?_).add
    (continuousOn_finsetSum _ fun a _ => ?_)
  · exact (hA a b).continuousOn.mul (contDiffOn_pdv (n := 0) hO (h1 b) a).continuousOn
  · exact (hB a).continuousOn.mul (h1 a).continuousOn

/-- A bound on `V` of a function continuous on `cl V` holds on `cl V`. -/
theorem abs_le_of_mem_closure {E : Type*} [TopologicalSpace E] {V : Set E} {v : E → ℝ}
    (hv : ContinuousOn v (closure V)) {M : ℝ} (hM : ∀ y ∈ V, |v y| ≤ M) :
    ∀ y ∈ closure V, |v y| ≤ M := by
  have hc : IsClosed (closure V ∩ (fun z => |v z|) ⁻¹' Set.Iic M) :=
    (hv.abs).preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic
  have : closure V ⊆ closure V ∩ (fun z => |v z|) ⁻¹' Set.Iic M :=
    closure_minimal (fun z hz => ⟨subset_closure hz, hM z hz⟩) hc
  exact fun y hy => (this hy).2

/-- **The principal-term inequality** (BB pp. 594-595, Lem 11.51, for one principal term of
positive type): there are `Cn, h₀, Cfar, M` such that for `0 < h ≤ h₀`, `v ∈ C²(O)` and
`Mg ≥ sup_V |L̃ v|`, `Mv ≥ sup_V |v|`, the function `x ↦ ∫ k(x, η) (L̃ v)(η) dη` is bounded on `V` by
`Cn h^{1-α} Mg + Cfar h^{-M} Mv` and `C^α`-Hölder for `d̃` with that constant. -/
theorem principal_interpolation (hF : C.IsLiftedFrame F) (hw : ∀ i, (w i : ℕ) ≤ 2)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) (t : PrincipalTerm F) (hdeg : t.degree ≤ 1)
    {Cg : ℝ} (hCg : 0 ≤ Cg) (hvar : LiftedVariation C Cg) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {Lop : ((Fin (n + m) → ℝ) → ℝ) → (Fin (n + m) → ℝ) → ℝ} (hL : IsCoordinateOp C Lop) :
    ∃ (Cn h₀ Cfar : ℝ) (M : ℕ), 0 < Cn ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 ≤ Cfar ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ v : (Fin (n + m) → ℝ) → ℝ, ContDiffOn ℝ 2 v C.O →
        ∀ Mg Mv : ℝ, 0 ≤ Mg → 0 ≤ Mv → (∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |Lop v y| ≤ Mg) →
        (∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |v y| ≤ Mv) →
        (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)),
          |∫ η, t.kernel x η * Lop v η| ≤ Cn * h ^ (1 - α) * Mg + Cfar * (h⁻¹) ^ M * Mv) ∧
        (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)),
          |(∫ η, t.kernel x η * Lop v η) - ∫ η, t.kernel y η * Lop v η| ≤
            (Cn * h ^ (1 - α) * Mg + Cfar * (h⁻¹) ^ M * Mv) * (C.dl x y).toReal ^ α) := by
  obtain ⟨A, B, hA, hB, hLop⟩ := hL
  set S : Set (Fin (n + m) → ℝ) := closure (F.V : Set (Fin (n + m) → ℝ)) with hS
  have hSc : IsCompact S := hF.isCompact_closure
  have hSU : S ⊆ C.U := hF.closure_subset
  have hSO : S ⊆ C.O := hSU.trans C.U_subset_O
  have hVS : (F.V : Set (Fin (n + m) → ℝ)) ⊆ S := subset_closure
  have hVm : MeasurableSet (F.V : Set (Fin (n + m) → ℝ)) := F.V.isOpen.measurableSet
  have hO : IsOpen C.O := isOpen_liftedDomain C
  obtain ⟨Cc, hCc⟩ := exists_coeffBound hO hSc hSO hA hB
  obtain ⟨Cn, h₀, hCn, hh₀, hh₀1, hnear⟩ := exists_near_bound hF ν hν t hdeg hCg hvar hα0 hα1
  obtain ⟨Cj, Mj, hCj, hjet⟩ := exists_farKernel_jetSup hF ν hν t
  obtain ⟨CE, hCE, hE⟩ := exists_norm_le_mul_dl C hw hSc hSU
  obtain ⟨D₀, hD₀, hD⟩ := C.exists_dl_bound hSc hSU
  have hα' : 0 < 1 - α := by linarith
  set Cf : ℝ := (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) * (((n + m : ℕ) : ℝ) + 1) with hCf
  have hCf0 : 0 ≤ Cf := by
    have := hCc.1
    positivity
  set Hc : ℝ := Cf * Cj * (1 + CE * D₀ ^ (1 - α)) with hHc
  have hHc0 : 0 ≤ Hc := by positivity
  refine ⟨Cn, h₀, Hc, Mj, hCn, hh₀, hh₀1, hHc0, ?_⟩
  intro h hh hhh₀ v hv Mg Mv hMg0 hMv0 hMg hMv
  have hh1 : h ≤ 1 := hhh₀.trans hh₀1
  -- the function `g = L̃ v` is continuous on `O`
  have hgc : ContinuousOn (Lop v) C.O :=
    (continuousOn_diffOp2 hO hA hB hv).congr (fun x hx => hLop v hv x hx)
  have hgmeas : AEStronglyMeasurable (Lop v) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
    (hgc.mono (hVS.trans hSO)).aestronglyMeasurable hVm
  have hvS : ∀ y ∈ S, |v y| ≤ Mv :=
    abs_le_of_mem_closure (hv.continuousOn.mono hSO) hMv
  obtain ⟨hnsup, hnhol⟩ := hnear h hh hhh₀ (Lop v) hgmeas Mg hMg0 hMg
  -- the far kernel
  have hJ := hjet h hh hh1
  have hHK : ∀ ξ η : Fin (n + m) → ℝ, η ∉ S → (farKernel ν t h : E2 (n + m) → ℝ) (ξ, η) = 0 :=
    fun ξ η hη => farKernel_eq_zero_of_notMem hF ν t h (fun hp => hη hp.2)
  have hfar := fun ξ ξ' => far_estimate hO hSc hSO hA hB hCc hJ hHK hv hvS ξ ξ'
  have hBj : 0 ≤ Cj * (h⁻¹) ^ Mj := hJ.nonneg
  have hfarint : ∀ x : Fin (n + m) → ℝ, ∫ η, farKernel ν t h (x, η) * Lop v η =
      ∫ η, (farKernel ν t h : E2 (n + m) → ℝ) (x, η) * diffOp2 A B v η := by
    intro x
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    beta_reduce
    by_cases hη : η ∈ S
    · rw [hLop v hv η (hSO hη)]
    · rw [hHK x η hη, zero_mul, zero_mul]
  -- integrability and the splitting `kernel = near + far`
  have hfarc : ∀ x : Fin (n + m) → ℝ,
      Integrable (fun η => farKernel ν t h (x, η) * Lop v η) := by
    intro x
    refine integrable_of_continuousOn_of_zero hSc ?_ (fun η hη => by
      rw [hHK x η hη, zero_mul])
    have : Continuous (fun η : Fin (n + m) → ℝ => (farKernel ν t h : E2 (n + m) → ℝ) (x, η)) :=
      (contDiff_farKernel hF ν hν t hh).continuous.comp (continuous_const.prodMk continuous_id)
    exact this.continuousOn.mul (hgc.mono hSO)
  have hker : ∀ x : Fin (n + m) → ℝ, Integrable (fun η => t.kernel x η * Lop v η) :=
    fun x => (PrincipalTerm.patchKernel hF t hdeg).integrable_row hgmeas hMg0 hMg x
  have hsplit : ∀ x : Fin (n + m) → ℝ, ∫ η, t.kernel x η * Lop v η =
      (∫ η, nearKernel ν t h x η * Lop v η) + ∫ η, farKernel ν t h (x, η) * Lop v η := by
    intro x
    have hnear' : Integrable (fun η => nearKernel ν t h x η * Lop v η) := by
      refine ((hker x).sub (hfarc x)).congr (Filter.Eventually.of_forall fun η => ?_)
      beta_reduce
      simp only [Pi.sub_apply]
      rw [← nearKernel_add_farKernel ν t h x η]; ring
    rw [← integral_add hnear' (hfarc x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    beta_reduce
    rw [← nearKernel_add_farKernel ν t h x η]; ring
  -- sup bound
  have hfarsup : ∀ x : Fin (n + m) → ℝ,
      |∫ η, farKernel ν t h (x, η) * Lop v η| ≤ Cf * (Cj * (h⁻¹) ^ Mj) * Mv := by
    intro x
    rw [hfarint x]
    refine (hfar x x).1.trans ?_
    have h1 : (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) ≤ Cf := by
      rw [hCf]
      have := hCc.1
      have : 0 ≤ (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) := by positivity
      nlinarith [Nat.cast_nonneg (α := ℝ) (n + m)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hBj) hMv0
  have hfarhol : ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)),
      |(∫ η, farKernel ν t h (x, η) * Lop v η) - ∫ η, farKernel ν t h (y, η) * Lop v η| ≤
        Cf * (Cj * (h⁻¹) ^ Mj) * Mv * (CE * D₀ ^ (1 - α)) * (C.dl x y).toReal ^ α := by
    intro x hx y hy
    rw [hfarint x, hfarint y]
    refine (hfar x y).2.trans ?_
    have h1 : (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) * (((n + m : ℕ) : ℝ) * (Cj * (h⁻¹) ^ Mj)) ≤
        Cf * (Cj * (h⁻¹) ^ Mj) := by
      have hc := hCc.1
      have e : Cf * (Cj * (h⁻¹) ^ Mj) = (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) *
          ((((n + m : ℕ) : ℝ) + 1) * (Cj * (h⁻¹) ^ Mj)) := by rw [hCf]; ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) (n + m)]
    have hxd := hE y (hVS hy) x (hVS hx)
    have hdd : (C.dl y x).toReal = (C.dl x y).toReal := by rw [C.dl_symm y x]
    rw [hdd] at hxd
    have hd0 : 0 ≤ (C.dl x y).toReal := ENNReal.toReal_nonneg
    have hdle : (C.dl x y).toReal ≤ D₀ ^ (1 - α) * (C.dl x y).toReal ^ α := by
      calc (C.dl x y).toReal = (C.dl x y).toReal ^ (1 - α) * (C.dl x y).toReal ^ α := by
            rw [← Real.rpow_add' hd0 (by linarith)]; simp
        _ ≤ D₀ ^ (1 - α) * (C.dl x y).toReal ^ α :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd0 (hD x (hVS hx) y (hVS hy)) hα'.le)
              (Real.rpow_nonneg hd0 _)
    have hnorm : ‖x - y‖ ≤ CE * D₀ ^ (1 - α) * (C.dl x y).toReal ^ α := by
      calc ‖x - y‖ ≤ CE * (C.dl x y).toReal := hxd
        _ ≤ CE * (D₀ ^ (1 - α) * (C.dl x y).toReal ^ α) := mul_le_mul_of_nonneg_left hdle hCE.le
        _ = CE * D₀ ^ (1 - α) * (C.dl x y).toReal ^ α := by ring
    have hMn : 0 ≤ Mv * ‖x - y‖ := by positivity
    calc _ ≤ (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) * (((n + m : ℕ) : ℝ) * (Cj * (h⁻¹) ^ Mj)) * Mv *
          ‖x - y‖ := le_rfl
      _ ≤ Cf * (Cj * (h⁻¹) ^ Mj) * Mv * ‖x - y‖ := by
          gcongr
      _ ≤ Cf * (Cj * (h⁻¹) ^ Mj) * Mv * (CE * D₀ ^ (1 - α) * (C.dl x y).toReal ^ α) := by
          have : 0 ≤ Cf * (Cj * (h⁻¹) ^ Mj) * Mv := by positivity
          exact mul_le_mul_of_nonneg_left hnorm this
      _ = _ := by ring
  have hcom : 0 ≤ Cf * (Cj * (h⁻¹) ^ Mj) * Mv := by positivity
  have hxM : 0 ≤ (h⁻¹) ^ Mj := pow_nonneg (inv_nonneg.mpr hh.le) _
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [hsplit x]
    refine (abs_add_le _ _).trans ?_
    have h1 := hnsup x hx
    have h2 := hfarsup x
    have e : Hc * (h⁻¹) ^ Mj * Mv = Cf * (Cj * (h⁻¹) ^ Mj) * Mv * (1 + CE * D₀ ^ (1 - α)) := by
      rw [hHc]; ring
    have h3 : Cf * (Cj * (h⁻¹) ^ Mj) * Mv ≤ Hc * (h⁻¹) ^ Mj * Mv := by
      rw [e]
      have : 0 ≤ Cf * (Cj * (h⁻¹) ^ Mj) * Mv * (CE * D₀ ^ (1 - α)) := by positivity
      nlinarith
    linarith
  · rw [hsplit x, hsplit y]
    have e1 : (∫ η, nearKernel ν t h x η * Lop v η) + (∫ η, farKernel ν t h (x, η) * Lop v η) -
        ((∫ η, nearKernel ν t h y η * Lop v η) + ∫ η, farKernel ν t h (y, η) * Lop v η) =
        ((∫ η, nearKernel ν t h x η * Lop v η) - ∫ η, nearKernel ν t h y η * Lop v η) +
        ((∫ η, farKernel ν t h (x, η) * Lop v η) - ∫ η, farKernel ν t h (y, η) * Lop v η) := by
      ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    have h1 := hnhol x hx y hy
    have h2 := hfarhol x hx y hy
    have hd0 : 0 ≤ (C.dl x y).toReal ^ α := Real.rpow_nonneg ENNReal.toReal_nonneg _
    have e : (Cn * h ^ (1 - α) * Mg + Hc * (h⁻¹) ^ Mj * Mv) * (C.dl x y).toReal ^ α =
        Cn * h ^ (1 - α) * Mg * (C.dl x y).toReal ^ α +
          Cf * (Cj * (h⁻¹) ^ Mj) * Mv * (1 + CE * D₀ ^ (1 - α)) * (C.dl x y).toReal ^ α := by
      rw [hHc]; ring
    rw [e]
    have : 0 ≤ Cf * (Cj * (h⁻¹) ^ Mj) * Mv * (C.dl x y).toReal ^ α := by positivity
    nlinarith

end RothschildStein.P2
