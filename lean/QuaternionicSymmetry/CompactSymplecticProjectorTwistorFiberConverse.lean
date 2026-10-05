import QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberConstant
import QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberSpan

/-! Converse CP¹-fiber calculation: a vector whose normalized paired-column
projector is the projector of a fixed unit quaternionic column lies in that
column's complex two-plane. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberConverse

open Matrix
open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnAlgebra
open CompactSymplecticProjectorColumnUnit
open CompactSymplecticProjectorTwistorNormalized
open CompactSymplecticProjectorTwistorFiberSpan

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ

theorem columnProjector_mulVec_self (n : ℕ) (v : V n) :
    columnProjector n v *ᵥ v = columnNormSq n v • v := by
  rw [columnProjector_mulVec]
  have ho : (star (pairedColumn n v)) ⬝ᵥ v = 0 :=
    pairedColumn_orthogonal_rev n v
  simp [columnNormSq, ho]

theorem normalizedProjector_mulVec_self (n : ℕ) (v : V n) (hv : v ≠ 0) :
    normalizedProjector n v *ᵥ v = v := by
  rw [normalizedProjector, smul_mulVec, columnProjector_mulVec_self,
    smul_smul, inv_mul_cancel₀ (columnNormSq_ne_zero n hv), one_smul]

theorem same_normalizedProjector_implies_span (n : ℕ)
    (v w : V n) (hw : w ≠ 0)
    (h : normalizedProjector n v = normalizedProjector n w) :
    ∃ a b : ℂ, w = a • v + b • pairedColumn n v := by
  have hfix : normalizedProjector n v *ᵥ w = w := by
    rw [h]
    exact normalizedProjector_mulVec_self n w hw
  let a := (columnNormSq n v)⁻¹ * ((star v) ⬝ᵥ w)
  let b := (columnNormSq n v)⁻¹ * ((star (pairedColumn n v)) ⬝ᵥ w)
  refine ⟨a,b,?_⟩
  rw [normalizedProjector, smul_mulVec, columnProjector_mulVec] at hfix
  simpa [a,b, smul_add, smul_smul] using hfix.symm

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberConverse
