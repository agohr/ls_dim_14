import QuaternionicSymmetry.UniversalProjectionGeneralCubic
import QuaternionicSymmetry.ElevenTwelveProjectionCertificates

/-! The checked general cubic Haar moment has the exact printed
Schur--Weyl coefficients, including the rank-three/four C12 generators. -/
namespace QuaternionicSymmetry.ProjectionCubicSchurBridge

open MvPolynomial UniversalProjectionGeneralCubic UnitaryProjectionGeneralCubic

noncomputable section
variable {S : Type*} [CommRing S] [Algebra ℝ S]

def schurCubicValue (r ell : ℝ) (z1 z2 z3 : S) : S :=
  algebraMap ℝ S (ell * (ell + 1) * (ell + 2) / (r * (r + 1) * (r + 2)) / 6) *
    (z1 ^ 3 + 3 * z1 * z2 + 2 * z3) +
  algebraMap ℝ S (2 * ell * (ell - 1) * (ell + 1) / (r * (r - 1) * (r + 1)) / 3) *
    (z1 ^ 3 - z3) +
  algebraMap ℝ S (ell * (ell - 1) * (ell - 2) / (r * (r - 1) * (r - 2)) / 6) *
    (z1 ^ 3 - 3 * z1 * z2 + 2 * z3)

theorem cubicValue_eq_schur (r ell : ℝ) (hr : 2 < r) (z1 z2 z3 : S) :
    cubicValue r ell z1 z2 z3 = schurCubicValue r ell z1 z2 z3 := by
  have h0 : r ≠ 0 := by linarith
  have h1 : r - 1 ≠ 0 := by linarith
  have h2 : r - 2 ≠ 0 := by linarith
  have hp1 : r + 1 ≠ 0 := by linarith
  have hp2 : r + 2 ≠ 0 := by linarith
  have hp : cubicValue r ell (X 0 : MvPolynomial (Fin 3) ℝ) (X 1) (X 2) =
      schurCubicValue r ell (X 0) (X 1) (X 2) := by
    apply MvPolynomial.funext
    intro v
    simp only [cubicValue, schurCubicValue, MvPolynomial.algebraMap_eq,
      map_add, map_mul, map_sub, map_pow, map_ofNat, eval_C, eval_X]
    simp only [distinctCoefficient, pairCoefficient, pairMoment, sameCoefficient]
    field_simp
    ring
  have h := congrArg (MvPolynomial.aeval ![z1, z2, z3]) hp
  simpa [cubicValue, schurCubicValue, Matrix.cons_val_two] using h

variable [Algebra ℚ S] [IsScalarTower ℚ ℝ S]

theorem m3_eval (r ell : ℚ) (hr : 2 < r) (v : Fin 6 → S) :
    MvPolynomial.aeval v (ElevenTwelveProjectionCertificates.m3 r ell) =
      cubicValue (r : ℝ) (ell : ℝ) (2 * v 1) (2 * v 2) (2 * v 3) := by
  have hp : MvPolynomial.map (algebraMap ℚ ℝ)
      (ElevenTwelveProjectionCertificates.m3 r ell) =
      cubicValue (r : ℝ) (ell : ℝ)
        (2 * X 1 : MvPolynomial (Fin 6) ℝ) (2 * X 2) (2 * X 3) := by
    apply MvPolynomial.funext
    intro x
    rw [show MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℝ)
        (ElevenTwelveProjectionCertificates.m3 r ell)) =
        MvPolynomial.aeval x (ElevenTwelveProjectionCertificates.m3 r ell) by
          simp [MvPolynomial.eval_map, MvPolynomial.aeval_def]]
    simp [ElevenTwelveProjectionCertificates.m3,
      ElevenTwelveProjectionCertificates.schur3,
      ElevenTwelveProjectionCertificates.schur21,
      ElevenTwelveProjectionCertificates.schur111,
      ElevenTwelveProjectionCertificates.z1, ElevenTwelveProjectionCertificates.z2,
      ElevenTwelveProjectionCertificates.z3,
      DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
      DimensionElevenTwelveDensity.p3, cubicValue, MvPolynomial.algebraMap_eq]
    rw [show distinctCoefficient (r : ℝ) (ell : ℝ) * (2 * x 1) ^ 3 +
        3 * (pairCoefficient (r : ℝ) (ell : ℝ) - distinctCoefficient (r : ℝ) (ell : ℝ)) *
          (2 * x 1) * (2 * x 2) +
        (sameCoefficient (r : ℝ) (ell : ℝ) - 3 * pairCoefficient (r : ℝ) (ell : ℝ) +
          2 * distinctCoefficient (r : ℝ) (ell : ℝ)) * (2 * x 3) =
        schurCubicValue (r : ℝ) (ell : ℝ) (2 * x 1) (2 * x 2) (2 * x 3) from
      cubicValue_eq_schur (r : ℝ) (ell : ℝ) (by exact_mod_cast hr) _ _ _]
    simp [schurCubicValue]
    ring
  have h := congrArg (MvPolynomial.aeval v) hp
  have he : MvPolynomial.aeval v
      (MvPolynomial.map (algebraMap ℚ ℝ) (ElevenTwelveProjectionCertificates.m3 r ell)) =
      MvPolynomial.aeval v (ElevenTwelveProjectionCertificates.m3 r ell) := by
    change MvPolynomial.eval₂Hom (algebraMap ℝ S) v
      (MvPolynomial.map (algebraMap ℚ ℝ) _) = MvPolynomial.eval₂Hom (algebraMap ℚ S) v _
    rw [MvPolynomial.eval₂Hom_map_hom]
    rw [← IsScalarTower.algebraMap_eq ℚ ℝ S]
  rw [he] at h
  simpa [cubicValue, MvPolynomial.algebraMap_eq] using h

end
end QuaternionicSymmetry.ProjectionCubicSchurBridge
