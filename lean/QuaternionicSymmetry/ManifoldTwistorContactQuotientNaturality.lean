import QuaternionicSymmetry.ManifoldTwistorContactFiberCharts

/-! The quotient complex structure is exactly the one induced by the
actual global twistor endomorphism, rather than an unrelated transport
of a rank-two vector-space structure. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The twistor complex operator descends through the genuine horizontal
contact plane, since that plane is J-invariant. -/
def contactQuotientTangentComplex (z : SphereBundleTotal Q) :
    (TangentSpace (I (E := E)) z ⧸ horizontalTangentSubmodule Q D z) →ₗ[ℝ]
      (TangentSpace (I (E := E)) z ⧸ horizontalTangentSubmodule Q D z) :=
  (horizontalTangentSubmodule Q D z).mapQ
    (horizontalTangentSubmodule Q D z)
    (tangentComplex Q D z) (by
      intro v hv
      exact tangentComplex_mem_horizontalTangentSubmodule Q D z v hv)

theorem contactQuotientTangentComplex_vertical (z : SphereBundleTotal Q)
    (w : verticalTangentSubmodule Q z) :
    contactQuotientComplexEquiv Q D z
        (contactQuotientTangentComplex Q D z
          (Submodule.Quotient.mk w.1)) =
      verticalTangentComplex Q D z w := by
  rw [contactQuotientTangentComplex, Submodule.mapQ_apply]
  exact Submodule.quotientEquivOfIsCompl_apply_mk_coe
    (horizontalTangentSubmodule Q D z) (verticalTangentSubmodule Q z)
    (horizontal_vertical_isCompl Q D z) (verticalTangentComplex Q D z w)

/-- Multiplication by `i` on the contact quotient agrees with the
operator induced from the actual tangent almost-complex structure. -/
theorem contactQuotientTangentComplex_eq_i_smul (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z ⧸ horizontalTangentSubmodule Q D z) :
    letI := contactQuotientComplexModule Q D z
    contactQuotientTangentComplex Q D z v = Complex.I • v := by
  letI := contactQuotientComplexModule Q D z
  letI := verticalComplexModule Q D z
  let w := contactQuotientComplexEquiv Q D z v
  have hv : v = Submodule.Quotient.mk (w : TangentSpace (I (E := E)) z) := by
    exact ((contactQuotientEquiv Q D z).symm_apply_apply v).symm
  rw [hv]
  apply (contactQuotientComplexEquiv Q D z).injective
  rw [contactQuotientTangentComplex_vertical]
  simp only [map_smul]
  have he : contactQuotientComplexEquiv Q D z
      (Submodule.Quotient.mk (w : TangentSpace (I (E := E)) z)) = w := by
    exact Submodule.quotientEquivOfIsCompl_apply_mk_coe
      (horizontalTangentSubmodule Q D z) (verticalTangentSubmodule Q z)
      (horizontal_vertical_isCompl Q D z) w
  rw [he]
  exact (verticalComplexSmul_i Q D z w).symm

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
