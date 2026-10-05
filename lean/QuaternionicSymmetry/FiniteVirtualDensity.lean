import QuaternionicSymmetry.TangentAhatLowerDensities
import QuaternionicSymmetry.PrintedTwoSixLinearAssembly

/-! One explicit finite density family for the classification range through
quaternionic dimension twelve, with its full tangent-character interpretation. -/
namespace QuaternionicSymmetry.FiniteVirtualDensity
open TangentAhatCharacterDensity TangentAhatLowerDensities RecoveredLogAhat
noncomputable section

def density : ℕ → DimensionElevenTwelveDensity.P
  | 2 => PrintedTwoSixLinearAssembly.density2
  | 3 => PrintedTwoSixLinearAssembly.density3
  | 4 => PrintedTwoSixLinearAssembly.density4
  | 5 => ReconstructionExamples.k5
  | 6 => ReconstructionExamples.k6
  | 7 => PrintedCertificatesSevenTen.rhs7
  | 8 => PrintedCertificatesSevenTen.rhs8
  | 9 => PrintedCertificatesSevenTen.rhs9
  | 10 => PrintedCertificatesSevenTen.rhs10
  | 11 => DimensionElevenTwelveDensity.density11
  | 12 => DimensionElevenTwelveDensity.density12
  | _ => 0

variable {R : Type} [CommRing R] [Algebra ℚ R]

theorem characterDensity_eq (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 12)
    (u : R) (t : ℕ → R) :
    characterDensity n u t (Characters.virtual n) =
      MvPolynomial.aeval (standardValues n u t) (density n) := by
  interval_cases n
  · exact characterDensity_2 u t
  · exact characterDensity_3 u t
  · exact characterDensity_4 u t
  · exact characterDensity_5 u t
  · exact characterDensity_6 u t
  · simpa only [density, PrintedCertificatesSevenTen.certificate7] using characterDensity_7 u t
  · simpa only [density, PrintedCertificatesSevenTen.certificate8] using characterDensity_8 u t
  · simpa only [density, PrintedCertificatesSevenTen.certificate9] using characterDensity_9 u t
  · simpa only [density, PrintedCertificatesSevenTen.certificate10] using characterDensity_10 u t
  · exact characterDensity_11 u t
  · exact characterDensity_12 u t

end
end QuaternionicSymmetry.FiniteVirtualDensity
