import QuaternionicSymmetry.ManifoldTwistorContactIntegerTwists
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

/-! Genuine holomorphic sections of every integer power of the twistor
contact line. The base uses the supplied complex atlas, and the fiber is the
actual holomorphic line core constructed from its transition functions. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

/-- Global holomorphic sections `H⁰(Z,L^r)` of the actual integer twist.
Mathlib's bundled `ContMDiffSection` has a complex vector-space structure. -/
abbrev HolomorphicTwistSections {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) : Type _ := by
  letI := A.charts
  letI := L.integerTwistCore_holomorphic Q D r
  exact ContMDiffSection 𝓘(ℂ, ComplexTwistorModel n) ℂ ∞
    (L.integerTwistCore Q D r).Fiber

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
