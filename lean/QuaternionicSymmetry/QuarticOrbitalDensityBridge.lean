import QuaternionicSymmetry.DimensionElevenTwelveDensity
import QuaternionicSymmetry.QuarticOrbitalTwelve

/-!
The dimension-eleven/twelve orbital certificates are transported into the
six-variable density ring.  The four-variable orbital ring has only
`p₁,…,p₄`; the density ring additionally retains `u` and `p₅`.  This bridge
uses a polynomial algebra homomorphism, so no specialization of `u` or `p₅`
is made and the result holds in algebras with nilpotents.
-/

namespace QuaternionicSymmetry.QuarticOrbitalDensityBridge

open MvPolynomial
noncomputable section

/-- Include quartic power-sum polynomials into the complete density ring. -/
def includeQuartic : QuarticOrbitalEleven.P →ₐ[ℚ] DimensionElevenTwelveDensity.P :=
  aeval ![DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
    DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4]

theorem include_Q₁₁₄ :
    includeQuartic QuarticOrbitalEleven.Q₁₁₄ = DimensionElevenTwelveDensity.q11 := by
  simp [includeQuartic, QuarticOrbitalEleven.Q₁₁₄,
    QuarticOrbitalEleven.p₁, QuarticOrbitalEleven.p₂,
    QuarticOrbitalEleven.p₃, QuarticOrbitalEleven.p₄,
    DimensionElevenTwelveDensity.q11]

theorem include_Q₁₂₄ :
    includeQuartic QuarticOrbitalTwelve.Q₁₂₄ = DimensionElevenTwelveDensity.q12 := by
  simp [includeQuartic, QuarticOrbitalTwelve.Q₁₂₄,
    QuarticOrbitalEleven.p₁, QuarticOrbitalEleven.p₂,
    QuarticOrbitalEleven.p₃, QuarticOrbitalEleven.p₄,
    DimensionElevenTwelveDensity.q12]

def orbital11 (a : List ℕ) : DimensionElevenTwelveDensity.P :=
  includeQuartic (QuarticOrbitalEleven.orbital a)

def orbital12 (a : List ℕ) : DimensionElevenTwelveDensity.P :=
  includeQuartic (QuarticOrbitalTwelve.orbital a)

/-- The quartic term in the reconstructed full dimension-eleven density
is the finite orbital certificate in the same polynomial ring. -/
theorem q11_orbital :
    DimensionElevenTwelveDensity.q11 =
      C QuarticOrbitalEleven.c₁ * orbital11 QuarticOrbitalEleven.a₁ +
      C QuarticOrbitalEleven.c₂ * orbital11 QuarticOrbitalEleven.a₂ +
      C QuarticOrbitalEleven.c₃ * orbital11 QuarticOrbitalEleven.a₃ +
      C QuarticOrbitalEleven.c₄ * orbital11 QuarticOrbitalEleven.a₄ +
      C QuarticOrbitalEleven.c₅ * orbital11 QuarticOrbitalEleven.a₅ := by
  rw [← include_Q₁₁₄]
  simpa only [orbital11, map_add, map_mul, includeQuartic, MvPolynomial.aeval_C] using
    congrArg includeQuartic QuarticOrbitalEleven.Q₁₁₄_orbital

/-- The corresponding quartic term in the reconstructed dimension-twelve
density is the finite orbital certificate. -/
theorem q12_orbital :
    DimensionElevenTwelveDensity.q12 =
      C QuarticOrbitalTwelve.c₁ * orbital12 QuarticOrbitalTwelve.b₁ +
      C QuarticOrbitalTwelve.c₂ * orbital12 QuarticOrbitalTwelve.b₂ +
      C QuarticOrbitalTwelve.c₃ * orbital12 QuarticOrbitalTwelve.b₃ +
      C QuarticOrbitalTwelve.c₄ * orbital12 QuarticOrbitalTwelve.b₄ +
      C QuarticOrbitalTwelve.c₅ * orbital12 QuarticOrbitalTwelve.b₅ := by
  rw [← include_Q₁₂₄]
  simpa only [orbital12, map_add, map_mul, includeQuartic, MvPolynomial.aeval_C] using
    congrArg includeQuartic QuarticOrbitalTwelve.Q₁₂₄_orbital

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem q11_orbital_eval (v : Fin 6 → R) :
    aeval v DimensionElevenTwelveDensity.q11 =
      aeval v (C QuarticOrbitalEleven.c₁ * orbital11 QuarticOrbitalEleven.a₁ +
        C QuarticOrbitalEleven.c₂ * orbital11 QuarticOrbitalEleven.a₂ +
        C QuarticOrbitalEleven.c₃ * orbital11 QuarticOrbitalEleven.a₃ +
        C QuarticOrbitalEleven.c₄ * orbital11 QuarticOrbitalEleven.a₄ +
        C QuarticOrbitalEleven.c₅ * orbital11 QuarticOrbitalEleven.a₅) :=
  congrArg (aeval v) q11_orbital

theorem q12_orbital_eval (v : Fin 6 → R) :
    aeval v DimensionElevenTwelveDensity.q12 =
      aeval v (C QuarticOrbitalTwelve.c₁ * orbital12 QuarticOrbitalTwelve.b₁ +
        C QuarticOrbitalTwelve.c₂ * orbital12 QuarticOrbitalTwelve.b₂ +
        C QuarticOrbitalTwelve.c₃ * orbital12 QuarticOrbitalTwelve.b₃ +
        C QuarticOrbitalTwelve.c₄ * orbital12 QuarticOrbitalTwelve.b₄ +
        C QuarticOrbitalTwelve.c₅ * orbital12 QuarticOrbitalTwelve.b₅) :=
  congrArg (aeval v) q12_orbital

end
end QuaternionicSymmetry.QuarticOrbitalDensityBridge
