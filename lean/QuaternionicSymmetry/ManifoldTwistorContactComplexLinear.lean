import QuaternionicSymmetry.ManifoldTwistorLeBrunHolomorphicContact

/-! The geometric contact form, originally identified with the checked
real horizontal quotient, is complex-linear on the actual source complex
tangent fiber. This follows from its proved intertwining with `i`, not
from an extra source-data field. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

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

/-- A real-linear map between complex vector spaces is complex-linear
when it intertwines multiplication by `i`. -/
private theorem map_complex_smul_of_i {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
    [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
    (f : V →ₗ[ℝ] W) (hi : ∀ v, f (Complex.I • v) = Complex.I • f v)
    (c : ℂ) (v : V) : f (c • v) = c • f v := by
  rw [← Complex.re_add_im c]
  simp only [add_smul, map_add, mul_smul]
  have hreal (r : ℝ) (x : V) : f ((r : ℂ) • x) = (r : ℂ) • f x := by
    change f ((algebraMap ℝ ℂ) r • x) = (algebraMap ℝ ℂ) r • f x
    rw [IsScalarTower.algebraMap_smul ℂ r x,
      IsScalarTower.algebraMap_smul ℂ r (f x)]
    exact f.map_smul r x
  rw [hreal c.re v, hreal c.im (Complex.I • v), hi]

/-- The actual complex-linear contact one-form in each complex tangent
fiber, obtained by moving the proved real quotient contact form across
the compatible complex atlas. -/
def HolomorphicContactLine.contactFormComplex {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A) :
    letI := A.charts
    ∀ z : SphereBundleTotal Q,
      TangentSpace 𝓘(ℂ,ComplexTwistorModel n) z →ₗ[ℂ] L.core.Fiber z := by
  letI := A.charts
  intro z
  let f : ComplexTwistorModel n →ₗ[ℝ] L.core.Fiber z :=
    (L.contactFormReal Q D z).comp
      (mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
        (id : SphereBundleTotal Q → SphereBundleTotal Q) z).toLinearMap
  exact {
    toFun := f
    map_add' := f.map_add
    map_smul' := by
      intro c v
      have hi : ∀ v : ComplexTwistorModel n,
          f (Complex.I • v) = Complex.I • f v :=
        L.contactFormTotal_i Q D z
      exact map_complex_smul_of_i f hi c v
  }

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
