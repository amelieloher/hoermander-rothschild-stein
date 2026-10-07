-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityTheoremTerm
public import RothschildStein.P1.StandardFrame
public import RothschildStein.P1.SingularSplitReflection

/-!
# Continuity: the kernel of every type-`λ` operator has principal-value bounds

Assembly of the continuity theorem from a type decomposition at budget `1`: a type-`λ`
kernel `k` equals, off the diagonal, the finite sum of its principal terms plus a regular remainder.
Each principal term of degree `≤ 1` and the regular remainder are patch kernels; each principal
term of degree `2` (only at `λ = 0`) has the near-plus-far reconstruction. By the closure of
`PVBounds` under finite sums and changes on the diagonal, `k` has principal-value bounds
(`TypeOperator.pvBounds`). On a standard frame, the pole of a term with `star = false` is the H1
kernel `Γ`, and for `star = true` it is the reflected kernel `Γ*` of the reversed-drift model, whose
shell cancellation follows from that of `Γ` (`kernelShellCancellation_reflection`).
(BB pp. 566–576, Thm 11.29.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {ν : (Fin (n + m) → ℝ) → ℝ}
  {V : Set (Fin (n + m) → ℝ)}

/-- Principal-value bounds are stable under finite sums. -/
theorem PVBounds.list_sum {ι : Type*} (l : List ι)
    {κι : ι → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (h : ∀ i ∈ l, C.PVBounds ν V (κι i)) :
    C.PVBounds ν V (fun ξ η => (l.map (fun i => κι i ξ η)).sum) := by
  induction l with
  | nil => simpa using (PVBounds.zero (C := C) (ν := ν) (V := V))
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simpa only [List.map_cons, List.sum_cons] using h1.add h2

variable {F : KernelFrame (n + m)} {q : ℕ} {H : H1.StandingHypotheses C.G q}
  {K : H1.FundamentalKernel C.G H} {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **Every principal term of a type-`λ` decomposition has principal-value bounds on a
standard frame**: degree `≤ 1` by the patch-kernel bounds, degree `2` by the singular reconstruction;
the pole of a starred term is the reflected kernel of the reversed-drift model. -/
theorem PVBounds.of_principalTerm (hF : C.IsStandardFrame F H K hQ) (t : PrincipalTerm F)
    (hdeg : t.degree ≤ 2) : C.PVBounds H.norm (F.V : Set (Fin (n + m) → ℝ)) t.kernel := by
  by_cases h2 : t.degree = 2
  · cases hs : t.star
    · have hpole : F.pole t.star = ⇑K := by simp [KernelFrame.pole, hs, hF.Γ_eq]
      exact PVBounds.of_principalTerm_degree_two hF.lifted hQ hF.norm_symm hF.norm_smooth K
        hF.kernel_props.cancellation t h2 hpole
    · have hpole : F.pole t.star = ⇑(K.reflection hQ) := by simp [KernelFrame.pole, hs, hF.Γs_eq]
      exact PVBounds.of_principalTerm_degree_two (H := H.reverseDrift C.G) hF.lifted hQ
        hF.norm_symm hF.norm_smooth (K.reflection hQ)
        (kernelShellCancellation_reflection K hQ C.G_inv_eq_neg hF.norm_symm
          hF.kernel_props.cancellation) t h2 hpole
  · exact PVBounds.of_principalTerm_degree_le_one hF.lifted t (by omega)

/-- **A decomposition of budget `m ≥ 1` gives principal-value bounds on a
standard frame**: the principal terms and the regular remainder (jointly `C^m ⊆ C¹`, compactly
supported in `V × V`) are summed, and the diagonal is null. -/
theorem _root_.RothschildStein.P1.TypeDecomposition.pvBounds (hF : C.IsStandardFrame F H K hQ)
    {lam m' : ℕ} {kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (d : TypeDecomposition F lam m' kk) (hm : 1 ≤ m') :
    C.PVBounds H.norm (F.V : Set (Fin (n + m) → ℝ)) kk := by
  have hprin : C.PVBounds H.norm (F.V : Set (Fin (n + m) → ℝ))
      (fun ξ η => (d.principal.map (fun t => t.kernel ξ η)).sum) :=
    PVBounds.list_sum d.principal (fun t ht =>
      PVBounds.of_principalTerm hF t (by have := d.principal_degree t ht; omega))
  have hreg := PVBounds.of_patchKernel (C := C) (ν := H.norm) H.norm.gauge
    ((d.regular_isRegular.mono hm).patchKernel hF.lifted)
  exact (hprin.add hreg).congr_off_diagonal fun ξ η hne => (d.eq_off_diagonal ξ η hne).symm

/-- **The kernel of every type-`λ` operator has principal-value bounds on a standard
frame** (a decomposition of budget `1` exists for every type-`λ` kernel). -/
theorem _root_.RothschildStein.P1.TypeOperator.pvBounds (hF : C.IsStandardFrame F H K hQ) {lam : ℕ}
    (T : TypeOperator F lam) : C.PVBounds H.norm (F.V : Set (Fin (n + m) → ℝ)) T.kernel := by
  obtain ⟨d⟩ := T.isType 1
  exact d.pvBounds hF le_rfl

end LiftedChart

end RothschildStein.P1
