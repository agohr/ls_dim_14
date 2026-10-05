import QuaternionicSymmetry.ComplexTorusDoubleCoordinateTensor
import Mathlib.AlgebraicGeometry.Pullbacks

/-! Genuine algebraic complex-torus multiplication on the coordinate-ring
tensor product, with exact character formula. -/

namespace QuaternionicSymmetry.ComplexTorusSchemeMultiplication

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexTorusLaurentComultiplication
open ComplexTorusDoubleCoordinateTensor
open scoped TensorProduct
noncomputable section

variable {r : ℕ}

def torusComultiplicationTensor :
    TorusCoordinateRing r →+*
      TorusCoordinateRing r ⊗[ℂ] TorusCoordinateRing r :=
  (doubleTorusTensorEquiv (r := r)).toRingHom.comp
    (comultiplication (r := r))

@[simp] theorem torusComultiplicationTensor_laurentMonomial
    (μ : Fin r → ℤ) :
    torusComultiplicationTensor (laurentMonomial μ) =
      (laurentMonomial μ) ⊗ₜ[ℂ] (laurentMonomial μ) := by
  simp [torusComultiplicationTensor]

def torusMultiplicationSpec (r : ℕ) :
    Spec (CommRingCat.of (TorusCoordinateRing r ⊗[ℂ] TorusCoordinateRing r)) ⟶
      Spec (CommRingCat.of (TorusCoordinateRing r)) :=
  Spec.map (CommRingCat.ofHom (torusComultiplicationTensor (r := r)))

def torusMultiplication (r : ℕ) :
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r)))) ⟶
      Spec (CommRingCat.of (TorusCoordinateRing r)) :=
  (pullbackSpecIso ℂ (TorusCoordinateRing r) (TorusCoordinateRing r)).hom ≫
    torusMultiplicationSpec r

end
end QuaternionicSymmetry.ComplexTorusSchemeMultiplication
