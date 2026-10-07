-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FractionalInterpolationFamily
public import RothschildStein.P2.FractionalInterpolationJet

/-!
# Hölder interpolation: jets of the far kernel

The far kernel of a principal term at scale `h` is `far_h(ξ, η) = k(ξ, η) farProfile ν h (Θ(η, ξ))`
with `k(ξ, η) = a(ξ) b(η) E(ξ, η, Θ(η, ξ))`. It is the composition `far_h(ξ, η) = a(ξ) b(η)
(farFamily ∘ Φ)(ξ, η)` with the chart map `Φ(ξ, η) = (ξ, η, Θ(η, ξ))`, so the far family bounds of
`FractionalInterpolationFamily` and the Faà di Bruno bound of Mathlib
(`ContDiffOn.norm_iteratedFDerivWithin_comp_le`) give the jet bound `‖D^j far_h‖ ≤ C (1/h)^M` for
`j ≤ 3` (`exists_farKernel_jetSup`), uniformly in `h ∈ (0, 1]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The chart map `Φ(ξ, η) = (ξ, η, Θ(η, ξ))` of the kernel. -/
def kernelPhi (C : LiftedChart w st Ω hΩ X x₀ m) (p : E2 (n + m)) : Z3 (n + m) :=
  (p.1, p.2, C.Θ p.2 p.1)

/-- The far kernel `k(ξ, η) farProfile ν h (Θ(η, ξ))` of a principal term at scale `h`. -/
def farKernel (ν : G2.HomogeneousNorm C.G) (t : PrincipalTerm F) (h : ℝ) (p : E2 (n + m)) : ℝ :=
  t.kernel p.1 p.2 * farProfile ν h (C.Θ p.2 p.1)

/-- The product of the output and input cutoffs of a principal term. -/
def cutoffProd (t : PrincipalTerm F) (p : E2 (n + m)) : ℝ := t.a p.1 * t.b p.2

theorem farKernel_eq (hF : C.IsLiftedFrame F) (ν : G2.HomogeneousNorm C.G) (t : PrincipalTerm F)
    (h : ℝ) (p : E2 (n + m)) :
    farKernel ν t h p = cutoffProd t p * farFamily ν t h (kernelPhi C p) := by
  unfold farKernel farFamily principalFamily kernelPhi cutoffProd PrincipalTerm.kernel
  simp only [hF.Θ_eq]
  ring

theorem exists_bound_iteratedFDeriv_of_compactSupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A := by
  have hcont : Continuous (iteratedFDeriv ℝ j f) :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨D, hD⟩ := hcont.bounded_above_of_compact_support (hc.iteratedFDeriv j)
  exact ⟨max D 0, le_max_right _ _, fun x => (hD x).trans (le_max_left _ _)⟩

theorem contDiff_cutoffProd (t : PrincipalTerm F) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffProd t : E2 (n + m) → ℝ) :=
  (t.a.contDiff.comp contDiff_fst).mul (t.b.contDiff.comp contDiff_snd)

theorem hasCompactSupport_cutoffProd (t : PrincipalTerm F) :
    HasCompactSupport (cutoffProd t : E2 (n + m) → ℝ) := by
  refine HasCompactSupport.intro (K := tsupport (t.a : (Fin (n + m) → ℝ) → ℝ) ×ˢ
    tsupport (t.b : (Fin (n + m) → ℝ) → ℝ)) (t.a.hasCompactSupport.prod t.b.hasCompactSupport)
    fun p hp => ?_
  have : p.1 ∉ tsupport (t.a : (Fin (n + m) → ℝ) → ℝ) ∨ p.2 ∉ tsupport (t.b : (Fin (n + m) → ℝ) → ℝ) := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hp ⟨hcon.1, hcon.2⟩
  rcases this with h | h
  · simp [cutoffProd, image_eq_zero_of_notMem_tsupport h]
  · simp [cutoffProd, image_eq_zero_of_notMem_tsupport h]

theorem tsupport_cutoffProd_subset (t : PrincipalTerm F) :
    tsupport (cutoffProd t : E2 (n + m) → ℝ) ⊆
      closure (F.V : Set (Fin (n + m) → ℝ)) ×ˢ closure (F.V : Set (Fin (n + m) → ℝ)) := by
  refine closure_minimal (fun p hp => ?_) (isClosed_closure.prod isClosed_closure)
  have h1 : t.a p.1 ≠ 0 := fun h => hp (by simp [cutoffProd, h])
  have h2 : t.b p.2 ≠ 0 := fun h => hp (by simp [cutoffProd, h])
  have h1' : p.1 ∈ tsupport (t.a : (Fin (n + m) → ℝ) → ℝ) := subset_closure h1
  have h2' : p.2 ∈ tsupport (t.b : (Fin (n + m) → ℝ) → ℝ) := subset_closure h2
  exact ⟨subset_closure (t.a.tsupport_subset h1'), subset_closure (t.b.tsupport_subset h2')⟩

theorem kernelPhi_contDiffOn (C : LiftedChart w st Ω hΩ X x₀ m) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kernelPhi C) (C.U ×ˢ C.U : Set (E2 (n + m))) := by
  have h3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : E2 (n + m) => C.Θ p.2 p.1) (C.U ×ˢ C.U) :=
    C.theta_smooth.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun p hp => ⟨hp.2, hp.1⟩)
  exact (contDiff_fst.contDiffOn).prodMk (contDiff_snd.contDiffOn.prodMk h3)

/-- The far kernel is smooth on `ℝ^N × ℝ^N`. -/
theorem contDiff_farKernel (hF : C.IsLiftedFrame F) (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth)
    (t : PrincipalTerm F) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ (⊤ : ℕ∞) (farKernel ν t h : E2 (n + m) → ℝ) := by
  have hs : IsOpen (C.U ×ˢ C.U : Set (E2 (n + m))) := C.isOpen_U.prod C.isOpen_U
  have heq : (farKernel ν t h : E2 (n + m) → ℝ) =
      fun p => cutoffProd t p * farFamily ν t h (kernelPhi C p) := funext (farKernel_eq hF ν t h)
  rw [heq]
  refine contDiff_iff_contDiffAt.2 fun p => ?_
  by_cases hp : p ∈ (C.U ×ˢ C.U : Set (E2 (n + m)))
  · have hΦ : ContDiffAt ℝ (⊤ : ℕ∞) (kernelPhi C) p :=
      (kernelPhi_contDiffOn C).contDiffAt (hs.mem_nhds hp)
    exact (contDiff_cutoffProd t).contDiffAt.mul
      ((contDiff_farFamily hF ν hν t hh).contDiffAt.comp p hΦ)
  · have hnot : p ∉ tsupport (cutoffProd t : E2 (n + m) → ℝ) := fun hmem => hp (by
      have := tsupport_cutoffProd_subset t hmem
      exact ⟨hF.closure_subset this.1, hF.closure_subset this.2⟩)
    have hev : (fun p => cutoffProd t p * farFamily ν t h (kernelPhi C p)) =ᶠ[𝓝 p]
        fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hnot] with q hq
      rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem farKernel_eq_zero_of_notMem (hF : C.IsLiftedFrame F) (ν : G2.HomogeneousNorm C.G)
    (t : PrincipalTerm F) (h : ℝ) {p : E2 (n + m)}
    (hp : p ∉ closure (F.V : Set (Fin (n + m) → ℝ)) ×ˢ closure (F.V : Set (Fin (n + m) → ℝ))) :
    farKernel ν t h p = 0 := by
  have hnot : p ∉ tsupport (cutoffProd t : E2 (n + m) → ℝ) := fun h' =>
    hp (tsupport_cutoffProd_subset t h')
  rw [farKernel_eq hF, image_eq_zero_of_notMem_tsupport hnot, zero_mul]

/-- **Jets of the far kernel** (BB pp. 594-595, Lem 11.51: "the far kernel has sup and
derivative bounds `≤ C h^{-M_0}`"): there are `Cj` and `M` with `‖D^j far_h‖ ≤ Cj (1/h)^M` for
`j ≤ 3`, uniformly in `h ∈ (0, 1]`. -/
theorem exists_farKernel_jetSup (hF : C.IsLiftedFrame F) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) (t : PrincipalTerm F) :
    ∃ (Cj : ℝ) (M : ℕ), 0 ≤ Cj ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      JetSup (farKernel ν t h : E2 (n + m) → ℝ) (Cj * (h⁻¹) ^ M) := by
  set Kc : Set (Fin (n + m) → ℝ) := closure (F.V : Set (Fin (n + m) → ℝ)) with hKcdef
  have hKc : IsCompact Kc := hF.isCompact_closure
  have hKcU : Kc ⊆ C.U := hF.closure_subset
  set L : Set (E2 (n + m)) := Kc ×ˢ Kc with hLdef
  have hL : IsCompact L := hKc.prod hKc
  set s : Set (E2 (n + m)) := C.U ×ˢ C.U with hsdef
  have hs : IsOpen s := C.isOpen_U.prod C.isOpen_U
  have hLs : L ⊆ s := Set.prod_mono hKcU hKcU
  -- the range of `ν ∘ Θ` on `L`
  have hνΘ : ContinuousOn (fun q : E2 (n + m) => ν (C.Θ q.2 q.1)) L :=
    ν.gauge.1.comp_continuousOn (C.theta_continuousOn.comp
      (continuous_snd.prodMk continuous_fst).continuousOn
      (fun q hq => ⟨(hLs hq).2, (hLs hq).1⟩))
  obtain ⟨R, hR⟩ := hL.exists_bound_of_continuousOn hνΘ
  have hR' : ∀ q ∈ L, ν (C.Θ q.2 q.1) ≤ R := fun q hq =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hR q hq)
  -- bounds of the far family
  choose Cb Mb hCb hFamB using fun i : ℕ =>
    exists_farFamily_iteratedFDeriv_bound hF ν hν t hL R i
  set Cm : ℝ := ∑ i ∈ Finset.range 4, Cb i with hCmdef
  set Mm : ℕ := ∑ i ∈ Finset.range 4, Mb i with hMmdef
  have hCm : 0 ≤ Cm := Finset.sum_nonneg fun i _ => hCb i
  have hFam : ∀ i : ℕ, i < 4 → ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ z : Z3 (n + m),
      (z.1, z.2.1) ∈ L → ν z.2.2 ≤ R →
      ‖iteratedFDeriv ℝ i (farFamily ν t h) z‖ ≤ Cm * (h⁻¹) ^ Mm := by
    intro i hi h hh hh1 z hzL hzR
    have hx : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
    have h1 : Cb i ≤ Cm := Finset.single_le_sum (f := Cb) (fun j _ => hCb j)
      (Finset.mem_range.mpr hi)
    have h2 : Mb i ≤ Mm := Finset.single_le_sum (f := Mb) (fun j _ => Nat.zero_le _)
      (Finset.mem_range.mpr hi)
    calc _ ≤ Cb i * (h⁻¹) ^ Mb i := hFamB i h hh hh1 z hzL hzR
      _ ≤ Cm * (h⁻¹) ^ Mm := mul_le_mul h1 (pow_le_pow_right₀ hx h2) (by positivity) hCm
  -- bounds of the chart map
  have hΦ := kernelPhi_contDiffOn C
  have hDΦ : ∀ i : ℕ, ∃ Di : ℝ, 0 ≤ Di ∧ ∀ p ∈ L,
      ‖iteratedFDerivWithin ℝ i (kernelPhi C) s p‖ ≤ Di := by
    intro i
    have hcont : ContinuousOn (iteratedFDerivWithin ℝ i (kernelPhi C) s) s :=
      hΦ.continuousOn_iteratedFDerivWithin (by simp) hs.uniqueDiffOn
    obtain ⟨D, hD⟩ := hL.exists_bound_of_continuousOn (hcont.mono hLs)
    exact ⟨max D 0, le_max_right _ _, fun p hp => (hD p hp).trans (le_max_left _ _)⟩
  choose Dphi hDphi0 hDphi using hDΦ
  set Dm : ℝ := 1 + ∑ i ∈ Finset.range 4, Dphi i with hDmdef
  have hDm1 : 1 ≤ Dm := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hDphi0 i)
  have hDi : ∀ p ∈ L, ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDerivWithin ℝ i (kernelPhi C) s p‖ ≤ Dm ^ i := by
    intro p hp i hi1 hi3
    have h1 : Dphi i ≤ ∑ j ∈ Finset.range 4, Dphi j :=
      Finset.single_le_sum (f := Dphi) (fun j _ => hDphi0 j) (Finset.mem_range.mpr (by omega))
    calc _ ≤ Dphi i := hDphi i p hp
      _ ≤ Dm := by rw [hDmdef]; linarith
      _ ≤ Dm ^ i := le_self_pow₀ hDm1 (by omega)
  -- bounds of the cutoff product
  choose Aab hAab0 hAab using fun i : ℕ => exists_bound_iteratedFDeriv_of_compactSupport
    (contDiff_cutoffProd t (F := F)) (hasCompactSupport_cutoffProd t) i
  set Am : ℝ := ∑ i ∈ Finset.range 4, Aab i with hAmdef
  have hAm : 0 ≤ Am := Finset.sum_nonneg fun i _ => hAab0 i
  refine ⟨48 * Am * Cm * Dm ^ 3, Mm, by positivity, fun h hh hh1 => ?_⟩
  have hx : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
  have hxM : 0 ≤ (h⁻¹) ^ Mm := pow_nonneg (by linarith) _
  have hfar : ContDiff ℝ (⊤ : ℕ∞) (farKernel ν t h : E2 (n + m) → ℝ) :=
    contDiff_farKernel hF ν hν t hh
  refine ⟨hfar.of_le (by simp), fun j hj p => ?_⟩
  by_cases hpL : p ∈ L
  · have hps : p ∈ s := hLs hpL
    have heq : (farKernel ν t h : E2 (n + m) → ℝ) =
        fun q => cutoffProd t q * (farFamily ν t h ∘ kernelPhi C) q := funext (farKernel_eq hF ν t h)
    have hG : ContDiffOn ℝ (⊤ : ℕ∞) (farFamily ν t h ∘ kernelPhi C) s :=
      ((contDiff_farFamily hF ν hν t hh).contDiffOn).comp hΦ (fun _ _ => mem_univ _)
    have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (f := cutoffProd t)
      (g := farFamily ν t h ∘ kernelPhi C) (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (contDiff_cutoffProd t).contDiffOn hG hs.uniqueDiffOn hps (n := j)
      (by simp)
    rw [← heq, iteratedFDerivWithin_of_isOpen j hs hps] at hmul
    refine hmul.trans ?_
    -- the bound for each term
    have hGi : ∀ i : ℕ, i ≤ j →
        ‖iteratedFDerivWithin ℝ (j - i) (farFamily ν t h ∘ kernelPhi C) s p‖ ≤
          6 * (Cm * (h⁻¹) ^ Mm) * Dm ^ 3 := by
      intro i hi
      have hji : j - i ≤ 3 := by omega
      have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := farFamily ν t h)
        (f := kernelPhi C) (n := j - i) (s := s) (t := (univ : Set (Z3 (n + m)))) (x := p)
        (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) (contDiff_farFamily hF ν hν t hh).contDiffOn hΦ
        (by simp) uniqueDiffOn_univ hs.uniqueDiffOn (fun _ _ => mem_univ _) hps
        (C := Cm * (h⁻¹) ^ Mm) (D := Dm)
        (fun i' hi' => by
          rw [iteratedFDerivWithin_univ]
          refine hFam i' (by omega) h hh hh1 (kernelPhi C p) hpL ?_
          exact hR' p hpL)
        (fun i' hi1 hi' => hDi p hpL i' hi1 (by omega))
      have hfact : ((j - i).factorial : ℝ) ≤ 6 := by
        have : j - i ≤ 3 := hji
        interval_cases (j - i) <;> norm_num [Nat.factorial]
      have hCc : 0 ≤ Cm * (h⁻¹) ^ Mm := mul_nonneg hCm hxM
      calc _ ≤ ((j - i).factorial : ℝ) * (Cm * (h⁻¹) ^ Mm) * Dm ^ (j - i) := hcomp
        _ ≤ 6 * (Cm * (h⁻¹) ^ Mm) * Dm ^ 3 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hfact hCc)
              (pow_le_pow_right₀ hDm1 hji) (by positivity) (by positivity)
    have hterm : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (cutoffProd t) s p‖ *
          ‖iteratedFDerivWithin ℝ (j - i) (farFamily ν t h ∘ kernelPhi C) s p‖ ≤
        (j.choose i : ℝ) * (Am * (6 * (Cm * (h⁻¹) ^ Mm) * Dm ^ 3)) := by
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h1 : ‖iteratedFDerivWithin ℝ i (cutoffProd t) s p‖ ≤ Am := by
        rw [iteratedFDerivWithin_of_isOpen i hs hps]
        refine (hAab i p).trans ?_
        exact Finset.single_le_sum (f := Aab) (fun j _ => hAab0 j) (Finset.mem_range.mpr (by omega))
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact mul_le_mul h1 (hGi i hi') (norm_nonneg _) hAm
    calc _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (Am * (6 * (Cm * (h⁻¹) ^ Mm) * Dm ^ 3)) := Finset.sum_le_sum hterm
      _ = (2 : ℝ) ^ j * (Am * (6 * (Cm * (h⁻¹) ^ Mm) * Dm ^ 3)) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 8 * (Am * (6 * (Cm * (h⁻¹) ^ Mm) * Dm ^ 3)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (2 : ℝ) ^ j ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
            _ = 8 := by norm_num
      _ = 48 * Am * Cm * Dm ^ 3 * (h⁻¹) ^ Mm := by ring
  · have hopen : IsOpen ((Kc ×ˢ Kc)ᶜ : Set (E2 (n + m))) := (hKc.prod hKc).isClosed.isOpen_compl
    have hev : (farKernel ν t h : E2 (n + m) → ℝ) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hpL] with q hq
      exact farKernel_eq_zero_of_notMem hF ν t h hq
    rw [(hev.iteratedFDeriv ℝ j).self_of_nhds, iteratedFDeriv_fun_zero]
    have : 0 ≤ 48 * Am * Cm * Dm ^ 3 * (h⁻¹) ^ Mm := by positivity
    simpa using this

end RothschildStein.P2
