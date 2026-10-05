import QuaternionicSymmetry.FourDimensionalQuaternionicPositiveSubmodule
import QuaternionicSymmetry.HyperholomorphicExterior
import QuaternionicSymmetry.ExteriorBasisCoordinates

/-! The six-coordinate Hodge calculation on genuine exterior covectors.
The construction uses an actual orthonormal basis. Independence under an
arbitrary oriented orthonormal change of basis is a separate obligation. -/
namespace QuaternionicSymmetry.FourDimensionalExteriorHodge

open Module FourDimensionalCoordinateHodge
open FourDimensionalQuaternionicHodgeFrame
open scoped BigOperators
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

abbrev TwoForm (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V)

def coordinates (b : Basis (Fin 4) ℝ V) : TwoForm V →ₗ[ℝ] Two where
  toFun α := ![BilinearExterior.evaluate (b 0) (b 1) α,
    BilinearExterior.evaluate (b 0) (b 2) α,
    BilinearExterior.evaluate (b 0) (b 3) α,
    BilinearExterior.evaluate (b 1) (b 2) α,
    BilinearExterior.evaluate (b 1) (b 3) α,
    BilinearExterior.evaluate (b 2) (b 3) α]
  map_add' α β := by funext i; fin_cases i <;> simp
  map_smul' c α := by funext i; fin_cases i <;> simp

def reconstruct (b : Basis (Fin 4) ℝ V) : Two →ₗ[ℝ] TwoForm V where
  toFun x := x 0 • exteriorPower.ιMulti ℝ 2 ![b.coord 0, b.coord 1] +
    x 1 • exteriorPower.ιMulti ℝ 2 ![b.coord 0, b.coord 2] +
    x 2 • exteriorPower.ιMulti ℝ 2 ![b.coord 0, b.coord 3] +
    x 3 • exteriorPower.ιMulti ℝ 2 ![b.coord 1, b.coord 2] +
    x 4 • exteriorPower.ιMulti ℝ 2 ![b.coord 1, b.coord 3] +
    x 5 • exteriorPower.ιMulti ℝ 2 ![b.coord 2, b.coord 3]
  map_add' x y := by simp [add_smul]; module
  map_smul' c x := by simp [smul_add, smul_smul]

private theorem evaluate_basis_wedge (b : Basis (Fin 4) ℝ V)
    (i j a c : Fin 4) :
    BilinearExterior.evaluate (b i) (b j)
      (exteriorPower.ιMulti ℝ 2 ![b.coord a, b.coord c]) =
        (if i = a then 1 else 0) * (if j = c then 1 else 0) -
          (if i = c then 1 else 0) * (if j = a then 1 else 0) := by
  rw [BilinearExterior.evaluate_wedge]
  simp only [Basis.coord_apply, Basis.repr_self_apply]

private theorem coordinates_basis_wedge (b : Basis (Fin 4) ℝ V)
    (a c : Fin 4) :
    coordinates b (exteriorPower.ιMulti ℝ 2 ![b.coord a, b.coord c]) =
      ![(if (0 : Fin 4) = a then 1 else 0) * (if (1 : Fin 4) = c then 1 else 0) -
          (if (0 : Fin 4) = c then 1 else 0) * (if (1 : Fin 4) = a then 1 else 0),
        (if (0 : Fin 4) = a then 1 else 0) * (if (2 : Fin 4) = c then 1 else 0) -
          (if (0 : Fin 4) = c then 1 else 0) * (if (2 : Fin 4) = a then 1 else 0),
        (if (0 : Fin 4) = a then 1 else 0) * (if (3 : Fin 4) = c then 1 else 0) -
          (if (0 : Fin 4) = c then 1 else 0) * (if (3 : Fin 4) = a then 1 else 0),
        (if (1 : Fin 4) = a then 1 else 0) * (if (2 : Fin 4) = c then 1 else 0) -
          (if (1 : Fin 4) = c then 1 else 0) * (if (2 : Fin 4) = a then 1 else 0),
        (if (1 : Fin 4) = a then 1 else 0) * (if (3 : Fin 4) = c then 1 else 0) -
          (if (1 : Fin 4) = c then 1 else 0) * (if (3 : Fin 4) = a then 1 else 0),
        (if (2 : Fin 4) = a then 1 else 0) * (if (3 : Fin 4) = c then 1 else 0) -
          (if (2 : Fin 4) = c then 1 else 0) * (if (3 : Fin 4) = a then 1 else 0)] := by
  funext t
  fin_cases t <;>
    simp [coordinates, evaluate_basis_wedge, Finsupp.single_apply,
      mul_ite, ite_mul]

@[simp] theorem coordinates_reconstruct (b : Basis (Fin 4) ℝ V) (x : Two) :
    coordinates b (reconstruct b x) = x := by
  change coordinates b (x 0 • exteriorPower.ιMulti ℝ 2 ![b.coord 0, b.coord 1] +
    x 1 • exteriorPower.ιMulti ℝ 2 ![b.coord 0, b.coord 2] +
    x 2 • exteriorPower.ιMulti ℝ 2 ![b.coord 0, b.coord 3] +
    x 3 • exteriorPower.ιMulti ℝ 2 ![b.coord 1, b.coord 2] +
    x 4 • exteriorPower.ιMulti ℝ 2 ![b.coord 1, b.coord 3] +
    x 5 • exteriorPower.ιMulti ℝ 2 ![b.coord 2, b.coord 3]) = x
  simp only [map_add, map_smul, coordinates_basis_wedge]
  funext i
  fin_cases i <;> simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem evaluate_self (α : TwoForm V) (v : V) :
    BilinearExterior.evaluate v v α = 0 := by
  have h : exteriorPower.ιMulti ℝ 2 ![v, v] = 0 :=
    (exteriorPower.ιMulti ℝ 2).map_eq_zero_of_eq ![v, v]
      (i := 0) (j := 1) rfl (by decide)
  simp [BilinearExterior.evaluate, h]

private theorem evaluate_swap (α : TwoForm V) (v w : V) :
    BilinearExterior.evaluate w v α = -BilinearExterior.evaluate v w α := by
  have h := (exteriorPower.ιMulti ℝ 2 (M := V)).map_swap ![v,w]
    (i := 0) (j := 1) (by decide)
  have hp : (![v,w] : Fin 2 → V) ∘ Equiv.swap 0 1 = ![w,v] := by
    funext i
    fin_cases i <;> simp
  rw [hp] at h
  simp [BilinearExterior.evaluate, h]

set_option maxHeartbeats 1000000 in
@[simp] theorem reconstruct_coordinates (b : Basis (Fin 4) ℝ V) (α : TwoForm V) :
    reconstruct b (coordinates b α) = α := by
  apply ExteriorBasisCoordinates.twoform_ext_basis b
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [reconstruct, coordinates, BilinearExterior.evaluate_wedge,
      evaluate_self, evaluate_swap α (b 0) (b 1),
      evaluate_swap α (b 0) (b 2), evaluate_swap α (b 0) (b 3),
      evaluate_swap α (b 1) (b 2), evaluate_swap α (b 1) (b 3),
      evaluate_swap α (b 2) (b 3)]

/-- Coordinates on all actual exterior two-covectors, with no skewness
or representability assumption on the form. -/
def coordinateEquiv (b : Basis (Fin 4) ℝ V) : TwoForm V ≃ₗ[ℝ] Two :=
  { coordinates b with
    invFun := reconstruct b
    left_inv := reconstruct_coordinates b
    right_inv := coordinates_reconstruct b }

/-- The Hodge star in the orientation of this actual orthonormal frame. -/
def frameStar (b : OrthonormalBasis (Fin 4) ℝ V) : TwoForm V →ₗ[ℝ] TwoForm V :=
  (reconstruct b.toBasis).comp
    (FourDimensionalCoordinateHodge.star.comp (coordinates b.toBasis))

theorem coordinates_frameStar (b : OrthonormalBasis (Fin 4) ℝ V) (α : TwoForm V) :
    coordinates b.toBasis (frameStar b α) =
      FourDimensionalCoordinateHodge.star (coordinates b.toBasis α) := by
  exact coordinates_reconstruct _ _

@[simp] theorem frameStar_frameStar (b : OrthonormalBasis (Fin 4) ℝ V)
    (α : TwoForm V) : frameStar b (frameStar b α) = α := by
  apply (coordinateEquiv b.toBasis).injective
  change coordinates b.toBasis _ = coordinates b.toBasis α
  rw [coordinates_frameStar, coordinates_frameStar, star_star]

theorem coordinates_operatorForm (b : OrthonormalBasis (Fin 4) ℝ V)
    (A : V →ₗ[ℝ] V)
    (hA : ∀ v w, inner ℝ (A v) w = -inner ℝ v (A w)) :
    coordinates b.toBasis (HyperholomorphicExterior.form b.toBasis A) =
      operatorTwoCoords b A := by
  funext i
  fin_cases i <;> simp [coordinates, operatorTwoCoords,
    HyperholomorphicExterior.evaluate_form b.toBasis A hA]

end
end QuaternionicSymmetry.FourDimensionalExteriorHodge
