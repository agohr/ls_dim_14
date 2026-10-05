import QuaternionicSymmetry.ManifoldTwistorHolomorphicSections
import Mathlib.Topology.Sheaves.LocalPredicate

/-! The sheaf of locally holomorphic sections of the actual contact-line
twists. The sheaf condition is obtained from pointwise gluing of dependent
functions and locality of complex differentiability. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open CategoryTheory
open TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev IX (n : ℕ) := 𝓘(ℂ, ComplexTwistorModel n)

/-- Holomorphicity of a section over an open set, expressed as
complex smoothness of the map into the genuine bundle total space. -/
def holomorphicSectionPrelocal {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    letI := A.charts
    TopCat.PrelocalPredicate
      (fun z : TopCat.of (SphereBundleTotal Q) => (L.integerTwistCore Q D r).Fiber z) := by
  letI := A.charts
  letI := L.integerTwistCore_holomorphic Q D r
  let P : ∀ {U : Opens (TopCat.of (SphereBundleTotal Q))},
      (∀ x : U, (L.integerTwistCore Q D r).Fiber x) → Prop :=
    fun {U} f =>
      ContMDiff (IX n) ((IX n).prod 𝓘(ℂ,ℂ)) ∞
        (fun x : U => (⟨x.1, f x⟩ :
          Bundle.TotalSpace ℂ (L.integerTwistCore Q D r).Fiber))
  refine { pred := P, res := ?_ }
  intro U V i f hf
  convert hf.comp (contMDiff_inclusion i.le) using 1

/-- A genuine sheaf of types of locally holomorphic sections. Its
objects are dependent sections of `L^r`, with the local complex-smoothness
predicate. The additive sheaf and derived cohomology upgrade is separate. -/
def holomorphicSectionSheaf {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    letI := A.charts
    TopCat.Sheaf (Type _) (TopCat.of (SphereBundleTotal Q)) := by
  letI := A.charts
  exact TopCat.subsheafToTypes (holomorphicSectionPrelocal Q D L r).sheafify

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
