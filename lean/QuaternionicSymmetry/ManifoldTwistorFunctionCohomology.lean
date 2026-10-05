import QuaternionicSymmetry.ManifoldTwistorZeroTwistFunctionSheaf
import QuaternionicSymmetry.ComplexAbelianSheafCohomology
import QuaternionicSymmetry.ManifoldTwistorHolomorphicComplexCohomology
import QuaternionicSymmetry.HolomorphicExponentialCohomology

/-! The precise comparison from the zeroth twist in the literature-facing
complex-module cohomology to the actual holomorphic-function cohomology
used by the exponential sequence. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open ManifoldTwistorSphereCore ManifoldQuaternionicMetric
  ManifoldQuaternionicConnection CategoryTheory CategoryTheory.Abelian TopologicalSpace
open HolomorphicExponentialCohomology
open scoped Manifold ContDiff
noncomputable section

local instance (X : TopCat.{0}) : HasExt.{1} (TopCat.Sheaf (ModuleCat.{0} ℂ) X) :=
  HasExt.standard _

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A)

def zeroTwistFunctionCohomologyEquiv (s : ℕ) :
    letI := A.charts
    holomorphicTwistComplexCohomology Q D L 0 s ≃+
      functionCohomology (B := SphereBundleTotal Q) 𝓘(ℂ, ComplexTwistorModel n) s := by
  letI := A.charts
  exact (ComplexAbelianSheafCohomology.cohomologyAddEquiv
    (TopCat.of (SphereBundleTotal Q)) (holomorphicSectionComplexSheaf Q D L 0) s).trans
      ((extFunctorObj (AbelianSheafCohomology.integralSheaf (SphereBundleTotal Q)) s).mapIso
        (zeroTwistFunctionSheafIso Q D L)).addCommGroupIsoToAddEquiv

theorem functionCohomology_subsingleton_of_zeroTwist (s : ℕ)
    (h : Subsingleton (holomorphicTwistComplexCohomology Q D L 0 s)) :
    letI := A.charts
    Subsingleton (functionCohomology
      (B := SphereBundleTotal Q) 𝓘(ℂ, ComplexTwistorModel n) s) := by
  letI := A.charts
  letI := h
  exact (zeroTwistFunctionCohomologyEquiv Q D L s).symm.injective.subsingleton

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
