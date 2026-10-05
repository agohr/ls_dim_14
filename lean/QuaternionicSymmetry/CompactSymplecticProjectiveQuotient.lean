import QuaternionicSymmetry.CompactSymplecticHaar
import Mathlib.Topology.Algebra.ProperAction.Basic

/-! A first concrete homogeneous carrier for quaternionic projective
space: the actual compact symplectic matrix group modulo the closed
stabilizer of the orthogonal projector onto the first paired complex
coordinate (one quaternionic coordinate line). This does not yet claim
an invariant quaternionic-Kähler metric, charts, or a Wolf-space
classification theorem. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectiveQuotient

open Matrix CompactSymplecticHaar
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- The diagonal orthogonal projector onto the first paired complex
coordinates in the standard `ℂⁿ ⊕ ℂⁿ` realization. -/
def firstPairProjector (n : ℕ) :
    Matrix (Fin (n + 1) ⊕ Fin (n + 1))
      (Fin (n + 1) ⊕ Fin (n + 1)) ℂ :=
  Matrix.diagonal (fun i =>
    if i = Sum.inl (0 : Fin (n + 1)) ∨
       i = Sum.inr (0 : Fin (n + 1)) then 1 else 0)

/-- The coordinate projector is genuinely idempotent. -/
theorem firstPairProjector_idempotent (n : ℕ) :
    firstPairProjector n * firstPairProjector n = firstPairProjector n := by
  classical
  simp only [firstPairProjector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- The coordinate projector is self-adjoint for the standard Hermitian form. -/
theorem firstPairProjector_selfAdjoint (n : ℕ) :
    (firstPairProjector n)ᴴ = firstPairProjector n := by
  classical
  simp [firstPairProjector]

/-- The actual subgroup preserving the first quaternionic coordinate
line: in the unitary realization, this is exactly commutation with the
orthogonal projector onto that line. -/
def firstPairStabilizer (n : ℕ) : Subgroup (CompactSymplecticHaar.Group (n + 1)) where
  carrier := {u | (u.1 : Matrix _ _ ℂ) * firstPairProjector n =
    firstPairProjector n * (u.1 : Matrix _ _ ℂ)}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ((u.1 : Matrix _ _ ℂ) * (v.1 : Matrix _ _ ℂ)) *
      firstPairProjector n = firstPairProjector n *
      ((u.1 : Matrix _ _ ℂ) * (v.1 : Matrix _ _ ℂ))
    calc
      _ = (u.1 : Matrix _ _ ℂ) *
          ((v.1 : Matrix _ _ ℂ) * firstPairProjector n) := by simp [mul_assoc]
      _ = (u.1 : Matrix _ _ ℂ) *
          (firstPairProjector n * (v.1 : Matrix _ _ ℂ)) := by rw [hv]
      _ = ((u.1 : Matrix _ _ ℂ) * firstPairProjector n) *
          (v.1 : Matrix _ _ ℂ) := by simp [mul_assoc]
      _ = _ := by rw [hu]; simp [mul_assoc]
  inv_mem' := by
    intro u hu
    let U : Matrix _ _ ℂ := u.1.1
    let V : Matrix _ _ ℂ := (u⁻¹).1.1
    have hUV : U * V = 1 := by
      change ((u * u⁻¹ : CompactSymplecticHaar.Group (n + 1)).1.1 : Matrix _ _ ℂ) = 1
      simp
    have hVU : V * U = 1 := by
      change ((u⁻¹ * u : CompactSymplecticHaar.Group (n + 1)).1.1 : Matrix _ _ ℂ) = 1
      simp
    have hUVP : U * firstPairProjector n = firstPairProjector n * U := hu
    change V * firstPairProjector n = firstPairProjector n * V
    calc
      V * firstPairProjector n = V * (firstPairProjector n * (U * V)) := by rw [hUV, mul_one]
      _ = V * ((firstPairProjector n * U) * V) := by simp [mul_assoc]
      _ = V * ((U * firstPairProjector n) * V) := by rw [← hUVP]
      _ = (V * U) * firstPairProjector n * V := by simp [mul_assoc]
      _ = firstPairProjector n * V := by rw [hVU]; simp

/-- The stabilizer is a closed subset of the actual compact group. -/
theorem isClosed_firstPairStabilizer (n : ℕ) :
    IsClosed (firstPairStabilizer n : Set (CompactSymplecticHaar.Group (n + 1))) := by
  apply isClosed_eq
  · exact ((continuous_subtype_val.comp continuous_subtype_val).mul
      continuous_const)
  · exact (continuous_const.mul
      (continuous_subtype_val.comp continuous_subtype_val))

/-- The genuine quotient carrier, with Mathlib's quotient topology. -/
abbrev ProjectiveCarrier (n : ℕ) :=
  CompactSymplecticHaar.Group (n + 1) ⧸ firstPairStabilizer n

instance (n : ℕ) : CompactSpace (ProjectiveCarrier n) := inferInstance

instance (n : ℕ) : T2Space (ProjectiveCarrier n) := by
  letI : IsClosed (firstPairStabilizer n : Set (CompactSymplecticHaar.Group (n + 1))) :=
    isClosed_firstPairStabilizer n
  infer_instance

instance (n : ℕ) : SecondCountableTopology (ProjectiveCarrier n) := inferInstance

instance (n : ℕ) : Nonempty (ProjectiveCarrier n) :=
  ⟨(1 : CompactSymplecticHaar.Group (n + 1))⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectiveQuotient
