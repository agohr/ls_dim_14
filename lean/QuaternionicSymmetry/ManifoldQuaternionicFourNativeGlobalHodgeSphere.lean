import QuaternionicSymmetry.ManifoldQuaternionicFourNativeHodgePredicate
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSmoothCore

/-! The independently topologized smooth native bundle's sphere subset is
the literal negative-Hodge unit locus in every actual tangent chart. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeGlobalHodgeSphere

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeNegativeSphereSet
open ManifoldQuaternionicFourNativeHodgePredicate
open ManifoldQuaternionicFourNativeSmoothCore
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : TopologicalSpace (nativeTwoFormVectorCore Q).TotalSpace :=
  (nativeTwoFormVectorCore Q).toTopologicalSpace

/-- Literal preferred-coordinate description of the global negative-Hodge
unit sphere inside the genuine native alternating-form vector bundle. -/
theorem nativeNegativeSphereTotal_iff_preferred
    (p : (nativeTwoFormVectorCore Q).TotalSpace) :
    p ∈ nativeNegativeSphereTotal Q ↔
      p.2 ∈ nativeNegativeUnitPredicate Q hdim
        (Q.frames.adaptedCore.indexAt p.1) p.1 :=
  nativeLocalSphereSet_iff_hodge Q hdim
    (Q.frames.adaptedCore.indexAt p.1) p.1
    (Q.frames.adaptedCore.mem_baseSet_at p.1) p.2

/-- Equivalent negative-Hodge equation in any adapted chart; therefore
the literal equation is independent of the chosen local trivialization. -/
theorem nativeNegativeSphereTotal_iff_chart_hodge
    (p : (nativeTwoFormVectorCore Q).TotalSpace)
    (i : atlas E M) (hi : p.1 ∈ Q.frames.adaptedCore.baseSet i) :
    p ∈ nativeNegativeSphereTotal Q ↔
      (nativeTwoFormVectorCore Q).coordChange
        (Q.frames.adaptedCore.indexAt p.1) i p.1 p.2 ∈
        nativeNegativeUnitPredicate Q hdim i p.1 := by
  rw [nativeNegativeSphereTotal_iff_chart Q hdim p i hi]
  exact nativeLocalSphereSet_iff_hodge Q hdim i p.1 hi _

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeGlobalHodgeSphere
