-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DilatedInputCoordinates
public import RothschildStein.G3.RetainedLieListProducts
@[expose] public section
noncomputable section
namespace RothschildStein.G3

theorem dilatedInputCoordinates_singleton {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (i : Fin a) (t : ℝ) :
    dilatedInputCoordinates D (wordLieElement [i]) t =
      D.basis.equivFun ((t^(p i : ℕ)) • (wordLieElement [i] : formalSpan a s p)) := by
  have hf : (⟨finiteDilate t (wordLieElement [i]).val,
      finiteDilate_mem_formalSpan t (wordLieElement [i]).property⟩ : formalSpan a s p) =
      t^(p i : ℕ) • (wordLieElement [i] : formalSpan a s p) := by
    apply Subtype.ext
    exact congrArg (fun f : coefficientLieAlgebra a s p => f.val)
      (quasiExponentialLogAt_singleton (s := s) (p := p) t i)
  exact (dilatedInputCoordinates_eq D (wordLieElement [i]) t).trans (congrArg D.basis.equivFun hf)

theorem dilatedInputCoordinates_neg {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) (t : ℝ) :
    dilatedInputCoordinates D (-f) t = -(dilatedInputCoordinates D f t) := by
  funext j
  simp [dilatedInputCoordinates,coordinateDilation]

def signedPrimitiveTime {a : ℕ} (p : Fin a → ℕ+) (b : Fin a × Bool) (t : ℝ) : ℝ :=
  if b.2 then t^(p b.1 : ℕ) else -(t^(p b.1 : ℕ))

theorem signedPrimitiveTime_abs {a : ℕ} (p : Fin a → ℕ+)
    (b : Fin a × Bool) (t : ℝ) : |signedPrimitiveTime p b t| = |t|^(p b.1 : ℕ) := by
  rcases b with ⟨i,b⟩
  cases b <;> simp [signedPrimitiveTime,abs_pow]

theorem signedPrimitiveTime_abs_le {a : ℕ} (p : Fin a → ℕ+)
    (b : Fin a × Bool) {t : ℝ} (ht : |t| ≤ 1) : |signedPrimitiveTime p b t| ≤ |t| := by
  rw [signedPrimitiveTime_abs]
  exact (pow_le_pow_of_le_one (abs_nonneg t) ht (p b.1).pos).trans_eq (pow_one _)

theorem dilatedInputCoordinates_signed_primitive {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (b : Fin a × Bool) (t : ℝ) :
    dilatedInputCoordinates D (primitiveScheduleLieInput b) t =
      D.basis.equivFun (signedPrimitiveTime p b t • (wordLieElement [b.1] : formalSpan a s p)) := by
  rcases b with ⟨i,b⟩
  cases b
  · change dilatedInputCoordinates D (-(wordLieElement [i] : formalSpan a s p)) t =
      D.basis.equivFun (-(t^(p i : ℕ)) • (wordLieElement [i] : formalSpan a s p))
    rw [dilatedInputCoordinates_neg,dilatedInputCoordinates_singleton]
    exact (D.basis.equivFun.map_neg _).symm.trans
      (congrArg D.basis.equivFun (neg_smul _ _).symm)
  · exact dilatedInputCoordinates_singleton D i t
end RothschildStein.G3
