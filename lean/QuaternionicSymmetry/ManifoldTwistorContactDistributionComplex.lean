import QuaternionicSymmetry.ManifoldTwistorContactQuotientComplex

/-! The actual connection-horizontal tangent distribution is preserved by
the global smooth twistor almost-complex structure. Each contact-plane
fiber is therefore a complex vector space. This is the smooth complex
distribution underlying the holomorphic contact distribution of T1. -/

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

def horizontalTangentComplex (z : SphereBundleTotal Q) :
    horizontalTangentSubmodule Q D z →ₗ[ℝ]
      horizontalTangentSubmodule Q D z where
  toFun v := ⟨tangentComplex Q D z v.1,
    tangentComplex_mem_horizontalTangentSubmodule Q D z v.1 v.2⟩
  map_add' u v := by
    apply Subtype.ext
    exact (tangentComplex Q D z).map_add u.1 v.1
  map_smul' r v := by
    apply Subtype.ext
    exact (tangentComplex Q D z).map_smul r v.1

theorem horizontalTangentComplex_sq (z : SphereBundleTotal Q)
    (v : horizontalTangentSubmodule Q D z) :
    horizontalTangentComplex Q D z (horizontalTangentComplex Q D z v) = -v := by
  apply Subtype.ext
  exact tangentComplex_sq Q D z v.1

def horizontalComplexSmul (z : SphereBundleTotal Q) (c : ℂ)
    (v : horizontalTangentSubmodule Q D z) :
    horizontalTangentSubmodule Q D z :=
  c.re • v + c.im • horizontalTangentComplex Q D z v

theorem horizontalComplexSmul_real (z : SphereBundleTotal Q) (r : ℝ)
    (v : horizontalTangentSubmodule Q D z) :
    horizontalComplexSmul Q D z (r : ℂ) v = r • v := by
  simp [horizontalComplexSmul]

theorem horizontalComplexSmul_one (z : SphereBundleTotal Q)
    (v : horizontalTangentSubmodule Q D z) :
    horizontalComplexSmul Q D z 1 v = v := by
  simp [horizontalComplexSmul]

theorem horizontalComplexSmul_add (z : SphereBundleTotal Q)
    (a b : ℂ) (v : horizontalTangentSubmodule Q D z) :
    horizontalComplexSmul Q D z (a + b) v =
      horizontalComplexSmul Q D z a v + horizontalComplexSmul Q D z b v := by
  simp only [horizontalComplexSmul, Complex.add_re, Complex.add_im, add_smul]
  abel

theorem horizontalComplexSmul_mul (z : SphereBundleTotal Q)
    (a b : ℂ) (v : horizontalTangentSubmodule Q D z) :
    horizontalComplexSmul Q D z (a * b) v =
      horizontalComplexSmul Q D z a (horizontalComplexSmul Q D z b v) := by
  simp only [horizontalComplexSmul, Complex.mul_re, Complex.mul_im,
    sub_smul, add_smul, smul_add, mul_smul, map_add, map_smul,
    horizontalTangentComplex_sq, smul_neg]
  abel

/-- The pointwise complex scalar action on the genuine horizontal tangent
plane, induced by the globally smooth twistor almost-complex operator. -/
def horizontalComplexModule (z : SphereBundleTotal Q) :
    Module ℂ (horizontalTangentSubmodule Q D z) where
  smul := horizontalComplexSmul Q D z
  one_smul := horizontalComplexSmul_one Q D z
  mul_smul := horizontalComplexSmul_mul Q D z
  smul_zero := by
    intro c
    change horizontalComplexSmul Q D z c 0 = 0
    simp [horizontalComplexSmul]
  smul_add := by
    intro c u v
    change horizontalComplexSmul Q D z c (u + v) =
      horizontalComplexSmul Q D z c u + horizontalComplexSmul Q D z c v
    simp only [horizontalComplexSmul, smul_add, map_add]
    abel
  add_smul := horizontalComplexSmul_add Q D z
  zero_smul := by
    intro v
    change horizontalComplexSmul Q D z 0 v = 0
    simp [horizontalComplexSmul]

theorem horizontalComplexSmul_i (z : SphereBundleTotal Q)
    (v : horizontalTangentSubmodule Q D z) :
    horizontalComplexSmul Q D z Complex.I v =
      horizontalTangentComplex Q D z v := by
  simp [horizontalComplexSmul]

/-- The horizontal projector intertwines the actual smooth global J.
This is the complex-linearity statement at each tangent fiber. -/
theorem horizontalProjection_complex_linear (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z) :
    horizontalProjection Q D z (tangentComplex Q D z v) =
      tangentComplex Q D z (horizontalProjection Q D z v) :=
  horizontalProjection_complex_commute Q D z v

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
