import QuaternionicSymmetry.CompactSymplecticProjectorColumnQuaternionic
import QuaternionicSymmetry.CompactSymplecticProjectorReflection

/-! A quaternionic orthogonal projector built from any unit complex column
yields a genuine compact-symplectic reflection. Unlike the orbit reflection,
this does not assume that the projector was already known to lie in the orbit. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnReflection

open Matrix CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnIdempotent
open CompactSymplecticProjectorColumnQuaternionic
open CompactSymplecticProjectorReflection
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem reflectionMatrix_quaternionic {n : ℕ} (P : Mat n)
    (hP : P * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * P.map star) :
    reflectionMatrix P * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * (reflectionMatrix P).map star := by
  have hmap : (P + P - 1).map star = P.map star + P.map star - 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  unfold reflectionMatrix
  rw [hmap]
  calc
    (P + P - 1) * CompactSymplecticHaar.standardJ (n + 1) =
        P * CompactSymplecticHaar.standardJ (n + 1) +
          P * CompactSymplecticHaar.standardJ (n + 1) -
          CompactSymplecticHaar.standardJ (n + 1) := by noncomm_ring
    _ = CompactSymplecticHaar.standardJ (n + 1) *
          (P.map star + P.map star - 1) := by rw [hP]; noncomm_ring

def reflectionOfProjector {n : ℕ} (P : Mat n)
    (hSelf : Pᴴ = P) (hIdem : P * P = P)
    (hQuat : P * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * P.map star) :
    CompactSymplecticHaar.Group (n + 1) := by
  let R := reflectionMatrix P
  let J := CompactSymplecticHaar.standardJ (n + 1)
  have hAdj : Rᴴ = R := reflectionMatrix_selfAdjoint P hSelf
  have hSq : R * R = 1 := reflectionMatrix_sq P hIdem
  have hUnit : R ∈ Matrix.unitaryGroup (I n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa only [Matrix.star_eq_conjTranspose, hAdj] using hSq
  have hTranspose : Rᵀ = R.map star := by
    have h := congrArg Matrix.transpose hAdj
    simpa only [Matrix.conjTranspose, Matrix.transpose_map,
      Matrix.transpose_transpose] using h.symm
  have hRJ : R * J = J * Rᵀ := by
    rw [hTranspose]
    exact reflectionMatrix_quaternionic P hQuat
  have hTransposeJ : Rᵀ * J = J * R := by
    have hJ2 : J * J = -1 := CompactSymplecticHaar.standardJ_sq (n + 1)
    calc
      Rᵀ * J = -(J * J) * Rᵀ * J := by rw [hJ2]; noncomm_ring
      _ = -J * (J * Rᵀ) * J := by noncomm_ring
      _ = -J * (R * J) * J := by rw [hRJ]
      _ = J * R := by
        calc
          -J * (R * J) * J = -J * R * (J * J) := by noncomm_ring
          _ = J * R := by rw [hJ2]; noncomm_ring
  refine ⟨⟨R, hUnit⟩, ?_⟩
  change Rᵀ * J * R = J
  rw [hTransposeJ, mul_assoc, hSq, mul_one]

def unitColumnReflection (n : ℕ)
    (v : Metric.sphere (0 : EuclideanSpace ℂ (I n)) 1) :
    CompactSymplecticHaar.Group (n + 1) :=
  reflectionOfProjector
    (columnProjector n ((EuclideanSpace.equiv (I n) ℂ) v.1))
    (columnProjector_selfAdjoint n _)
    (unit_columnProjector_idempotent n v)
    (columnProjector_quaternionic n _)

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnReflection
