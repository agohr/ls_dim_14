import QuaternionicSymmetry.ManifoldTwistorContactQuotientNaturality

/-! Multiplication by `i` on the actual contact quotient is the quotient
of the checked tangent almost-complex operator. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactQuotientIMk
open ManifoldTwistorSphereCore ManifoldTwistorGlobalAlmostComplex
open ManifoldQuaternionicMetric ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

theorem i_smul_mk (z : SphereBundleTotal Q)
    (v : TangentSpace (J (E := E)) z) :
    letI := contactQuotientComplexModule Q D z
    Complex.I • (Submodule.Quotient.mk v :
      TangentSpace (J (E := E)) z ⧸ horizontalTangentSubmodule Q D z) =
      Submodule.Quotient.mk (tangentComplex Q D z v) := by
  letI := contactQuotientComplexModule Q D z
  rw [← contactQuotientTangentComplex_eq_i_smul Q D z,
    contactQuotientTangentComplex, Submodule.mapQ_apply]

end
end QuaternionicSymmetry.ManifoldTwistorContactQuotientIMk
