import QuaternionicSymmetry.ManifoldTwistorLeBrunHolomorphicLine

/-! The holomorphic contact map in the cited twistor theorem is a map of
genuine complex-manifold vector-bundle total spaces. Its formula is fixed
by the previously checked smooth horizontal quotient. Holomorphicity is
the remaining source conclusion, not inferred from smoothness. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
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

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The map fixed by the real quotient identification: complex tangent
directions are transferred to the original real sphere atlas and then
projected to the actual horizontal quotient/contact line. -/
def HolomorphicContactLine.contactFormTotal {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A) :
    letI := A.charts
    TangentBundle 𝓘(ℂ, ComplexTwistorModel n) (SphereBundleTotal Q) →
      Bundle.TotalSpace ℂ L.core.Fiber := by
  letI := A.charts
  intro t
  exact ⟨t.1, L.contactFormReal Q D t.1
    (mfderiv 𝓘(ℝ, ComplexTwistorModel n) (RealModel (E := E))
      (id : SphereBundleTotal Q → SphereBundleTotal Q) t.1 t.2)⟩

/-- The total-space form is complex linear on tangent fibers, as a
consequence of the source atlas matching the internally constructed
twistor complex structure and the proved quotient-line naturality. -/
theorem HolomorphicContactLine.contactFormTotal_i {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (z : SphereBundleTotal Q) :
    letI := A.charts
    ∀ (v : TangentSpace 𝓘(ℝ, ComplexTwistorModel n) z),
    L.contactFormReal Q D z
      (mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
        (id : SphereBundleTotal Q → SphereBundleTotal Q) z
        ((Complex.I : ℂ) • (show ComplexTwistorModel n from v))) =
      Complex.I • L.contactFormReal Q D z
        (mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
          (id : SphereBundleTotal Q → SphereBundleTotal Q) z v) := by
  letI := A.charts
  intro v
  rw [A.tangentI z v]
  exact L.contactFormReal_i Q D z _

/-- LeBrun's holomorphic contact conclusion on the concrete twistor
sphere bundle. The holomorphic line has complex rank one, its real form
has the proved horizontal kernel, and the induced map is holomorphic.
There is no holomorphic horizontal splitting field. -/
structure HolomorphicContactData (n : ℕ) (A : CompatibleComplexAtlas Q D n) where
  line : HolomorphicContactLine Q D n A
  contactHolomorphic : letI := A.charts
    letI := A.complexManifold
    letI := line.holomorphic
    ContMDiff (𝓘(ℂ, ComplexTwistorModel n)).tangent
      ((𝓘(ℂ, ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ)) ∞
      (line.contactFormTotal Q D)

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
