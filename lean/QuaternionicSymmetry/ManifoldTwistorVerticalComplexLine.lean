import QuaternionicSymmetry.ManifoldTwistorContactSplitting
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! The vertical projection kernel carries a canonical complex scalar action
from the globally smooth twistor almost-complex operator. Pointwise this is
a complex line because its real rank is two. A holomorphic line bundle still
requires the integrable twistor structure and holomorphic transition maps. -/

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

def verticalComplexSmul (z : SphereBundleTotal Q) (c : ℂ)
    (v : verticalTangentSubmodule Q z) : verticalTangentSubmodule Q z :=
  c.re • v + c.im • verticalTangentComplex Q D z v

theorem verticalComplexSmul_one (z : SphereBundleTotal Q)
    (v : verticalTangentSubmodule Q z) :
    verticalComplexSmul Q D z 1 v = v := by
  simp [verticalComplexSmul]

theorem verticalComplexSmul_add (z : SphereBundleTotal Q)
    (a b : ℂ) (v : verticalTangentSubmodule Q z) :
    verticalComplexSmul Q D z (a + b) v =
      verticalComplexSmul Q D z a v + verticalComplexSmul Q D z b v := by
  simp only [verticalComplexSmul, Complex.add_re, Complex.add_im, add_smul]
  abel

theorem verticalComplexSmul_mul (z : SphereBundleTotal Q)
    (a b : ℂ) (v : verticalTangentSubmodule Q z) :
    verticalComplexSmul Q D z (a * b) v =
      verticalComplexSmul Q D z a (verticalComplexSmul Q D z b v) := by
  simp only [verticalComplexSmul, Complex.mul_re, Complex.mul_im,
    sub_smul, add_smul, smul_add, mul_smul, map_add, map_smul,
    verticalTangentComplex_sq]
  simp only [smul_neg]
  abel

theorem verticalComplexSmul_i (z : SphereBundleTotal Q)
    (v : verticalTangentSubmodule Q z) :
    verticalComplexSmul Q D z Complex.I v = verticalTangentComplex Q D z v := by
  simp [verticalComplexSmul]

/-- The pointwise complex vector-space structure carried by the actual
vertical projection kernel. This definition is deliberately explicit in
`Q`, `D`, and `z` rather than a global instance that could silently choose a
connection. -/
def verticalComplexModule (z : SphereBundleTotal Q) :
    Module ℂ (verticalTangentSubmodule Q z) where
  smul := verticalComplexSmul Q D z
  one_smul := verticalComplexSmul_one Q D z
  mul_smul := verticalComplexSmul_mul Q D z
  smul_zero := by
    intro c
    change verticalComplexSmul Q D z c 0 = 0
    simp [verticalComplexSmul]
  smul_add := by
    intro c u v
    change verticalComplexSmul Q D z c (u + v) =
      verticalComplexSmul Q D z c u + verticalComplexSmul Q D z c v
    simp only [verticalComplexSmul, smul_add, map_add]
    abel
  add_smul := verticalComplexSmul_add Q D z
  zero_smul := by
    intro v
    change verticalComplexSmul Q D z 0 v = 0
    simp [verticalComplexSmul]

theorem verticalComplexSmul_real (z : SphereBundleTotal Q) (r : ℝ)
    (v : verticalTangentSubmodule Q z) :
    verticalComplexSmul Q D z (r : ℂ) v = r • v := by
  simp [verticalComplexSmul]

theorem verticalComplex_finrank (z : SphereBundleTotal Q) :
    letI := verticalComplexModule Q D z
    Module.finrank ℂ (verticalTangentSubmodule Q z) = 1 := by
  let realModule : Module ℝ (verticalTangentSubmodule Q z) := inferInstance
  letI : Module ℝ (verticalTangentSubmodule Q z) := realModule
  letI := verticalComplexModule Q D z
  letI : IsScalarTower ℝ ℂ (verticalTangentSubmodule Q z) := ⟨by
    intro r c v
    change verticalComplexSmul Q D z (r • c) v =
      r • verticalComplexSmul Q D z c v
    rw [show r • c = (r : ℂ) * c by simp,
      verticalComplexSmul_mul, verticalComplexSmul_real]⟩
  have hmodule : Module.complexToReal (verticalTangentSubmodule Q z) = realModule := by
    apply Module.ext'
    intro r v
    change verticalComplexSmul Q D z (r : ℂ) v = r • v
    exact verticalComplexSmul_real Q D z r v
  have h := finrank_real_of_complex (verticalTangentSubmodule Q z)
  rw [hmodule] at h
  have hreal : Module.finrank ℝ (verticalTangentSubmodule Q z) = 2 :=
    verticalTangent_finrank Q z
  have hh : 2 = 2 * Module.finrank ℂ (verticalTangentSubmodule Q z) :=
    hreal.symm.trans h
  omega

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
