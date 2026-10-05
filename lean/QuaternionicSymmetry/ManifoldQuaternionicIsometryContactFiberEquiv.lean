import QuaternionicSymmetry.ManifoldQuaternionicHolomorphicContactFiberAction
import QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficients
import QuaternionicSymmetry.ManifoldQuaternionicTwistorVerticalDerivative

/-! The derivative-defined map between actual contact-line fibers of an
isometry is a complex-linear equivalence. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryContactFiberEquiv

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorVerticalDerivative
open ManifoldQuaternionicTwistorContactWeight
open ManifoldQuaternionicIsometryVerticalComplex
open ManifoldQuaternionicHolomorphicContactFiberAction
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorLeBrunComplexAtlas
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

local instance : Fact (Module.finrank ℝ
    ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

theorem coefficientAction_injective
    (f : QuaternionicIsometries Q) (x : M) :
    Function.Injective (coefficientAction Q f x) := by
  intro a b hab
  have h := congrArg (coefficientAction Q f⁻¹ (f • x)) hab
  have ha := coefficientAction_mul Q f⁻¹ f x a
  have hb := coefficientAction_mul Q f⁻¹ f x b
  rw [inv_mul_cancel, coefficientAction_one] at ha hb
  exact ha.trans (h.trans hb.symm)

theorem actualVerticalDerivative_injective
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    Function.Injective (actualVerticalDerivative Q f z) := by
  intro u v huv
  have h := congrArg
    (fun w : verticalTangentSubmodule Q (sphereTotalMap Q f z) =>
      ((verticalTangentEquiv Q (sphereTotalMap Q f z)) w).1) huv
  change ((verticalTangentEquiv Q (sphereTotalMap Q f z))
      (actualVerticalDerivative Q f z u)).1 =
    ((verticalTangentEquiv Q (sphereTotalMap Q f z))
      (actualVerticalDerivative Q f z v)).1 at h
  have hu := vertical_mfderiv_coefficient Q f z u
  have hv := vertical_mfderiv_coefficient Q f z v
  change ((verticalTangentEquiv Q (sphereTotalMap Q f z))
      (actualVerticalDerivative Q f z u)).1 =
    coefficientAction Q f z.1 ((verticalTangentEquiv Q z u).1) at hu
  change ((verticalTangentEquiv Q (sphereTotalMap Q f z))
      (actualVerticalDerivative Q f z v)).1 =
    coefficientAction Q f z.1 ((verticalTangentEquiv Q z v).1) at hv
  have hcoeff := coefficientAction_injective Q f z.1 (hu.symm.trans (h.trans hv))
  apply (verticalTangentEquiv Q z).injective
  apply Subtype.ext
  exact hcoeff

/-- Actual complex-line equivalence on vertical tangent planes. -/
def actualVerticalDerivativeComplexEquiv
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    letI := verticalComplexModule Q D z
    letI := verticalComplexModule Q D (sphereTotalMap Q f z)
    verticalTangentSubmodule Q z ≃ₗ[ℂ]
      verticalTangentSubmodule Q (sphereTotalMap Q f z) := by
  letI := verticalComplexModule Q D z
  letI := verticalComplexModule Q D (sphereTotalMap Q f z)
  letI : FiniteDimensional ℂ (verticalTangentSubmodule Q z) :=
    FiniteDimensional.of_finrank_pos (by
      rw [verticalComplex_finrank Q D z]
      omega)
  letI : FiniteDimensional ℂ (verticalTangentSubmodule Q (sphereTotalMap Q f z)) :=
    FiniteDimensional.of_finrank_pos (by
      rw [verticalComplex_finrank Q D (sphereTotalMap Q f z)]
      omega)
  let F := actualVerticalDerivativeComplex Q D f z
  have hdim : Module.finrank ℂ (verticalTangentSubmodule Q z) =
      Module.finrank ℂ (verticalTangentSubmodule Q (sphereTotalMap Q f z)) := by
    rw [verticalComplex_finrank Q D z,
      verticalComplex_finrank Q D (sphereTotalMap Q f z)]
  have hinj : Function.Injective F := actualVerticalDerivative_injective Q f z
  exact LinearEquiv.ofBijective F
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

/-- The canonical actual holomorphic contact-line fiber map, promoted to a
complex-linear equivalence by the invertibility of the true derivative. -/
theorem contactLineFiberMap_injective
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {C : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n C)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    Function.Injective (contactLineFiberMap Q D L f z) := by
  letI := contactQuotientComplexModule Q D z
  letI := contactQuotientComplexModule Q D (sphereTotalMap Q f z)
  letI := verticalComplexModule Q D z
  letI := verticalComplexModule Q D (sphereTotalMap Q f z)
  intro u v huv
  have h := congrArg (L.quotientEquiv (sphereTotalMap Q f z)) huv
  rw [quotientEquiv_contactLineFiberMap,
    quotientEquiv_contactLineFiberMap] at h
  have h' := congrArg (contactQuotientComplexEquiv Q D
    (sphereTotalMap Q f z)) h
  have hvertical : actualVerticalDerivativeComplex Q D f z
      ((contactQuotientComplexEquiv Q D z) (L.quotientEquiv z u)) =
    actualVerticalDerivativeComplex Q D f z
      ((contactQuotientComplexEquiv Q D z) (L.quotientEquiv z v)) := by
    simpa only [actualContactQuotientDerivativeComplex,
      LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply] using h'
  have h'' := actualVerticalDerivative_injective Q f z hvertical
  exact (L.quotientEquiv z).injective
    ((contactQuotientComplexEquiv Q D z).injective h'')

def contactLineFiberEquiv
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {C : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n C)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    L.core.Fiber z ≃ₗ[ℂ] L.core.Fiber (sphereTotalMap Q f z) := by
  letI := contactQuotientComplexModule Q D z
  letI := contactQuotientComplexModule Q D (sphereTotalMap Q f z)
  letI : FiniteDimensional ℂ (L.core.Fiber z) :=
    FiniteDimensional.of_finrank_pos (by
      rw [(L.quotientEquiv z).finrank_eq,
        contactQuotient_complex_finrank Q D z]
      omega)
  letI : FiniteDimensional ℂ (L.core.Fiber (sphereTotalMap Q f z)) :=
    FiniteDimensional.of_finrank_pos (by
      rw [(L.quotientEquiv (sphereTotalMap Q f z)).finrank_eq,
        contactQuotient_complex_finrank Q D (sphereTotalMap Q f z)]
      omega)
  have hdim : Module.finrank ℂ (L.core.Fiber z) =
      Module.finrank ℂ (L.core.Fiber (sphereTotalMap Q f z)) := by
    rw [(L.quotientEquiv z).finrank_eq,
      (L.quotientEquiv (sphereTotalMap Q f z)).finrank_eq,
      contactQuotient_complex_finrank Q D z,
      contactQuotient_complex_finrank Q D (sphereTotalMap Q f z)]
  let F := contactLineFiberMap Q D L f z
  have hinj : Function.Injective F := contactLineFiberMap_injective Q D L f z
  exact LinearEquiv.ofBijective F
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

theorem contactLineFiberEquiv_apply
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {C : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n C)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (v : L.core.Fiber z) :
    contactLineFiberEquiv Q D L f z v =
      contactLineFiberMap Q D L f z v := rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryContactFiberEquiv
