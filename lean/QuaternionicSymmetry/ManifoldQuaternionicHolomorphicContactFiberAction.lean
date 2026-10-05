import QuaternionicSymmetry.ManifoldTwistorLeBrunHolomorphicLine
import QuaternionicSymmetry.ManifoldQuaternionicIsometryVerticalComplex

/-! The derivative of a genuine quaternionic isometry induces a complex
linear action on each fiber of the actual holomorphic contact line. This is
the pointwise part of the canonical contact linearization; holomorphic
dependence on the total space is a separate obligation. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHolomorphicContactFiberAction

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryVerticalComplex
open ManifoldQuaternionicIsometryContactQuotient
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The actual holomorphic contact-line fiber carries the transported
quotient derivative of the smooth isometry lift. -/
def contactLineFiberMap {n : ℕ} {C : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n C)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    L.core.Fiber z →ₗ[ℂ] L.core.Fiber (sphereTotalMap Q f z) := by
  letI := contactQuotientComplexModule Q D z
  letI := contactQuotientComplexModule Q D (sphereTotalMap Q f z)
  exact (L.quotientEquiv (sphereTotalMap Q f z)).symm.toLinearMap.comp
    ((actualContactQuotientDerivativeComplex Q D f z).comp
      (L.quotientEquiv z).toLinearMap)

theorem quotientEquiv_contactLineFiberMap {n : ℕ}
    {C : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n C)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (v : L.core.Fiber z) :
    letI := contactQuotientComplexModule Q D z
    letI := contactQuotientComplexModule Q D (sphereTotalMap Q f z)
    L.quotientEquiv (sphereTotalMap Q f z)
      (contactLineFiberMap Q D L f z v) =
      actualContactQuotientDerivativeComplex Q D f z (L.quotientEquiv z v) := by
  letI := contactQuotientComplexModule Q D z
  letI := contactQuotientComplexModule Q D (sphereTotalMap Q f z)
  simp [contactLineFiberMap]

/-- The action on the holomorphic line agrees exactly with the derivative
of the actual lifted isometry after applying the contact form. -/
theorem contactLineFiberMap_contactFormReal {n : ℕ}
    {C : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n C)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (v : TangentSpace (J (E := E)) z) :
    contactLineFiberMap Q D L f z (L.contactFormReal Q D z v) =
      L.contactFormReal Q D (sphereTotalMap Q f z)
        (mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z v) := by
  letI := contactQuotientComplexModule Q D z
  letI := contactQuotientComplexModule Q D (sphereTotalMap Q f z)
  apply (L.quotientEquiv (sphereTotalMap Q f z)).injective
  rw [quotientEquiv_contactLineFiberMap]
  simp only [HolomorphicContactLine.contactFormReal, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.restrictScalars_apply,
    LinearEquiv.apply_symm_apply]
  change actualContactQuotientDerivativeComplex Q D f z
      (Submodule.Quotient.mk v) =
    (Submodule.Quotient.mk
      (mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z v) :
      TangentSpace (J (E := E)) (sphereTotalMap Q f z) ⧸
        horizontalTangentSubmodule Q D (sphereTotalMap Q f z))
  rw [actualContactQuotientDerivativeComplex_apply]
  rfl

/-- The geometric contact form onto the source line fiber is surjective. -/
theorem contactFormReal_surjective {n : ℕ}
    {C : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n C) (z : SphereBundleTotal Q) :
    Function.Surjective (L.contactFormReal Q D z) := by
  letI := contactQuotientComplexModule Q D z
  intro w
  obtain ⟨v, hv⟩ :=
    (horizontalTangentSubmodule Q D z).mkQ_surjective (L.quotientEquiv z w)
  refine ⟨v, (L.quotientEquiv z).injective ?_⟩
  simpa only [HolomorphicContactLine.contactFormReal, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.restrictScalars_apply,
    LinearEquiv.apply_symm_apply] using hv

end
end QuaternionicSymmetry.ManifoldQuaternionicHolomorphicContactFiberAction
