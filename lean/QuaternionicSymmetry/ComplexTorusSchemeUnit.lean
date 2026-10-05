import QuaternionicSymmetry.ComplexProjectiveDiagonalAlgebraicCharts
import Mathlib.AlgebraicGeometry.Pullbacks

/-! The literal identity section of the algebraic complex torus is a
scheme morphism over the canonical `Spec ℂ` structural map. -/

namespace QuaternionicSymmetry.ComplexTorusSchemeUnit

open AlgebraicGeometry CategoryTheory
open ComplexProjectiveDiagonalAlgebraicCharts
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r : ℕ}

theorem evalTorus_algebraMap (z : ComplexTorus r) (c : ℂ) :
    evalTorus z (algebraMap ℂ (TorusCoordinateRing r) c) = c := by
  simp [evalTorus]

def torusUnitSpec (r : ℕ) :
    Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (TorusCoordinateRing r)) :=
  Spec.map (CommRingCat.ofHom (evalTorus (1 : ComplexTorus r)))

theorem torusUnitSpec_over_complex (r : ℕ) :
    torusUnitSpec r ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))) =
    𝟙 (Spec (CommRingCat.of ℂ)) := by
  simp only [torusUnitSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (evalTorus (1 : ComplexTorus r)).comp
      (algebraMap ℂ (TorusCoordinateRing r)) = RingHom.id ℂ := by
    apply RingHom.ext
    intro c
    exact evalTorus_algebraMap 1 c
  rw [h]
  simp

end
end QuaternionicSymmetry.ComplexTorusSchemeUnit
