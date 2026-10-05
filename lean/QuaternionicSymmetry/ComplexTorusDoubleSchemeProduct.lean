import QuaternionicSymmetry.ComplexTorusSchemeMultiplication
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductMultiplication

/-! The double-Laurent affine scheme is isomorphic to the literal
fiber product of two algebraic complex torus schemes over `Spec ℂ`.
The multiplication map used in the global action law is the standard
torus group-scheme multiplication under this isomorphism. -/

namespace QuaternionicSymmetry.ComplexTorusDoubleSchemeProduct

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexTorusLaurentComultiplication
open ComplexTorusDoubleCoordinateTensor
open ComplexTorusSchemeMultiplication
open ComplexProjectiveActualConeDoubleProductMultiplication
open scoped TensorProduct
noncomputable section

variable {r : ℕ}

def doubleTorusSchemeProductIso (r : ℕ) :
    Spec (CommRingCat.of (DoubleTorusCoordinateRing r)) ≅
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r)))) :=
  (Scheme.Spec.mapIso
    (doubleTorusTensorEquiv (r := r)).symm.toCommRingCatIso.op) ≪≫
    (pullbackSpecIso ℂ (TorusCoordinateRing r) (TorusCoordinateRing r)).symm

theorem doubleTorusSchemeProductIso_multiplication (r : ℕ) :
    (doubleTorusSchemeProductIso r).hom ≫ torusMultiplication r =
      doubleTorusMultiplicationSpec r := by
  simp [doubleTorusSchemeProductIso, torusMultiplication,
    torusMultiplicationSpec, doubleTorusMultiplicationSpec,
    torusComultiplicationTensor, Category.assoc,
    ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (by
    apply RingHom.ext
    intro t
    exact (doubleTorusTensorEquiv (r := r)).symm_apply_apply
      (comultiplication t))

end
end QuaternionicSymmetry.ComplexTorusDoubleSchemeProduct
