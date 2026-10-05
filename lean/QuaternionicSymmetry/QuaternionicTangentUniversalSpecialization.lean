import QuaternionicSymmetry.QuaternionicTangentFormalMatrix

/-! Universal tangent trace binomial after substitution into any
commutative real algebra, including the even exterior algebra. -/
namespace QuaternionicSymmetry.QuaternionicTangentUniversalSpecialization
open QuaternionicTangentFormalMatrix
noncomputable section

variable {E R : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [CommRing R] [Algebra ℝ R]
variable (S : QuaternionicStructure E) (η : Index S → R)

private def evalMatrix (A : Matrix (MatrixIndex (E := E))
    (MatrixIndex (E := E)) (MvPolynomial (Index S) ℝ)) :
    Matrix (MatrixIndex (E := E)) (MatrixIndex (E := E)) R :=
  (MvPolynomial.aeval η).toRingHom.mapMatrix A

def spMatrix : Matrix (MatrixIndex (E := E)) (MatrixIndex (E := E)) R :=
  evalMatrix S η (spPolynomial S)

def scalarMatrix : Matrix (MatrixIndex (E := E)) (MatrixIndex (E := E)) R :=
  evalMatrix S η (scalarPolynomial S)

def scalarNorm : R := MvPolynomial.aeval η (scalarNormPolynomial S)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem aeval_trace_pow (A : Matrix (MatrixIndex (E := E))
    (MatrixIndex (E := E)) (MvPolynomial (Index S) ℝ)) (k : ℕ) :
    MvPolynomial.aeval η (Matrix.trace (A ^ k)) =
      Matrix.trace ((evalMatrix S η A) ^ k) := by
  rw [AddMonoidHom.map_trace]
  change Matrix.trace ((MvPolynomial.aeval η).toRingHom.mapMatrix (A ^ k)) = _
  rw [RingHom.mapMatrix_apply, Matrix.map_pow]
  rfl

/-- Division-free all-rank tangent/Sp trace conversion after arbitrary
real-algebra substitution. -/
theorem tangent_even_trace_specialized (j : ℕ) :
    Matrix.trace ((spMatrix S η + scalarMatrix S η) ^ (2 * j)) =
      ∑ m ∈ Finset.range (2 * j + 1),
        (if Even (2 * j - m) then
          (-(scalarNorm S η)) ^ ((2 * j - m) / 2) *
            Matrix.trace ((spMatrix S η) ^ m)
         else 0) * (Nat.choose (2 * j) m : R) := by
  have h := congrArg (MvPolynomial.aeval η)
    (tangent_even_trace_polynomial S j)
  simp only [map_sum, map_mul] at h
  rw [aeval_trace_pow S η (fullPolynomial S) (2 * j)] at h
  have hfull : evalMatrix S η (fullPolynomial S) =
      spMatrix S η + scalarMatrix S η := by
    change (spPolynomial S + scalarPolynomial S).map
      (MvPolynomial.aeval η) =
        (spPolynomial S).map (MvPolynomial.aeval η) +
          (scalarPolynomial S).map (MvPolynomial.aeval η)
    ext i j
    simp [Matrix.map_apply]
  rw [hfull] at h
  have hrhs :
      (∑ m ∈ Finset.range (2 * j + 1),
        (MvPolynomial.aeval η)
          (if Even (2 * j - m) then
            (-(scalarNormPolynomial S)) ^ ((2 * j - m) / 2) *
              Matrix.trace ((spPolynomial S) ^ m)
           else 0) *
          (MvPolynomial.aeval η)
            (Nat.choose (2 * j) m : MvPolynomial (Index S) ℝ)) =
      ∑ m ∈ Finset.range (2 * j + 1),
        (if Even (2 * j - m) then
          (-(scalarNorm S η)) ^ ((2 * j - m) / 2) *
            Matrix.trace ((spMatrix S η) ^ m)
         else 0) * (Nat.choose (2 * j) m : R) := by
    apply Finset.sum_congr rfl
    intro m hm
    by_cases he : Even (2 * j - m) <;>
      simp [he, scalarNorm, aeval_trace_pow S η (spPolynomial S) m,
        spMatrix, evalMatrix]
  exact h.trans hrhs


end
end QuaternionicSymmetry.QuaternionicTangentUniversalSpecialization
