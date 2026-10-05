import QuaternionicSymmetry.QuaternionicRootRecoveryNaturality
import QuaternionicSymmetry.DimensionElevenTwelveDensity

/-! Substituting the recovered standard powers into the logarithmic A-hat
polynomials gives the Bernoulli coefficient times the tangent half trace.
The identity is in a rational polynomial ring, so it also applies to
characteristic classes and exterior algebras with nilpotents. -/
namespace QuaternionicSymmetry.RecoveredLogAhat
open MvPolynomial QuaternionicTangentRootConversion
noncomputable section
set_option maxHeartbeats 1500000

abbrev P := DimensionElevenTwelveDensity.P

def tangentVariables : ℕ → P := fun j =>
  if h : j < 6 then X ⟨j, h⟩ else 0

def recoveredValues (n : ℕ) : Fin 6 → P :=
  ![X 0,
    recoveredStandardPower n (X 0) tangentVariables 1,
    recoveredStandardPower n (X 0) tangentVariables 2,
    recoveredStandardPower n (X 0) tangentVariables 3,
    recoveredStandardPower n (X 0) tangentVariables 4,
    recoveredStandardPower n (X 0) tangentVariables 5]

def logarithmicPolynomial (n : ℕ) : Fin 5 → P :=
  ![DimensionElevenTwelveDensity.b1 n, DimensionElevenTwelveDensity.b2 n,
    DimensionElevenTwelveDensity.b3 n, DimensionElevenTwelveDensity.b4 n,
    DimensionElevenTwelveDensity.b5 n]

theorem recovered_logarithmic (n : ℕ) (j : Fin 5) :
    aeval (recoveredValues n) (logarithmicPolynomial n j) =
      C (LogAhat.ell (j.val+1)) * tangentVariables (j.val+1) := by
  apply MvPolynomial.funext
  intro v
  change (aeval v) ((aeval (recoveredValues n)) (logarithmicPolynomial n j)) =
    (aeval v) (C (LogAhat.ell (j.val+1)) * tangentVariables (j.val+1))
  rw [comp_aeval_apply]
  fin_cases j <;>
    simp [logarithmicPolynomial, recoveredValues,
      DimensionElevenTwelveDensity.b1, DimensionElevenTwelveDensity.b2,
      DimensionElevenTwelveDensity.b3, DimensionElevenTwelveDensity.b4,
      DimensionElevenTwelveDensity.b5, DimensionElevenTwelveDensity.old,
      AlgebraCertificates.evaluate, AlgebraCertificates.b₁,
      AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄,
      AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁,
      AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄,
      DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1,
      DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3,
      DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5,
      recoveredStandardPower, recoveredSymplecticPowers,
      recoveredQ1, recoveredQ2, recoveredQ3, recoveredQ4, recoveredQ5,
      half, tangentVariables, LogAhat.ell_one, LogAhat.ell_two,
      LogAhat.ell_three, LogAhat.ell_four, LogAhat.ell_five] <;> ring


variable {R : Type} [CommRing R] [Algebra ℚ R]

def tangentValues (u : R) (t : ℕ → R) : Fin 6 → R :=
  ![u, t 1, t 2, t 3, t 4, t 5]

def standardValues (n : ℕ) (u : R) (t : ℕ → R) : Fin 6 → R :=
  ![u, recoveredStandardPower n u t 1, recoveredStandardPower n u t 2,
    recoveredStandardPower n u t 3, recoveredStandardPower n u t 4,
    recoveredStandardPower n u t 5]

theorem evaluate_recoveredValues (n : ℕ) (u : R) (t : ℕ → R) :
    (fun i => (aeval (tangentValues u t)) (recoveredValues n i)) =
      standardValues n u t := by
  funext i
  fin_cases i <;>
    simp [recoveredValues, standardValues, tangentValues,
      recoveredStandardPower, recoveredSymplecticPowers,
      recoveredQ1, recoveredQ2, recoveredQ3, recoveredQ4, recoveredQ5,
      half, tangentVariables]

theorem evaluated_logarithmic (n : ℕ) (u : R) (t : ℕ → R) (j : Fin 5) :
    aeval (standardValues n u t) (logarithmicPolynomial n j) =
      algebraMap ℚ R (LogAhat.ell (j.val+1)) * t (j.val+1) := by
  have h := congrArg (aeval (tangentValues u t)) (recovered_logarithmic n j)
  rw [comp_aeval_apply, evaluate_recoveredValues] at h
  rw [h, map_mul, aeval_C]
  congr 1
  fin_cases j <;> simp [tangentVariables, tangentValues]

end
end QuaternionicSymmetry.RecoveredLogAhat
