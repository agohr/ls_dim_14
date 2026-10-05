import QuaternionicSymmetry.FourDimensionalCoordinateHodge
import QuaternionicSymmetry.QuaternionicEigenbasisCoordinates

/-! A quaternionic unit vector in real dimension four supplies an actual
orthonormal frame. Its three fundamental two-form coordinate vectors are
positive eigenvectors of the coordinate Hodge star, certified by the exterior
wedge/Euclidean pairing in `FourDimensionalCoordinateHodge`. -/
namespace QuaternionicSymmetry.FourDimensionalQuaternionicHodgeFrame

open FourDimensionalCoordinateHodge
open QuaternionicStructure
open scoped BigOperators
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

def frameBasis (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    OrthonormalBasis (Fin 4) ℝ V := by
  apply OrthonormalBasis.mk (Q.frame_orthonormal v hv)
  have htop : Q.frameSpan v = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Q.frameSpan_finrank v hv, hdim]
  simpa only [QuaternionicStructure.frameSpan] using htop.ge

theorem frameBasis_apply (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1)
    (k : Fin 4) : frameBasis Q hdim v hv k = Q.frame v k := by
  simp [frameBasis, OrthonormalBasis.mk,
    _root_.Module.Basis.coe_toOrthonormalBasis, Module.Basis.coe_mk]

/-- The six independent coefficients of the skew operator's two-form,
in the actual quaternionic orthonormal basis. -/
def operatorTwoCoords (b : OrthonormalBasis (Fin 4) ℝ V)
    (A : V →ₗ[ℝ] V) : Two :=
  ![inner ℝ (A (b 0)) (b 1), inner ℝ (A (b 0)) (b 2),
    inner ℝ (A (b 0)) (b 3), inner ℝ (A (b 1)) (b 2),
    inner ℝ (A (b 1)) (b 3), inner ℝ (A (b 2)) (b 3)]

theorem I_coordinates (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    operatorTwoCoords (frameBasis Q hdim v hv) Q.I.toLinearEquiv.toLinearMap = plusI := by
  have horth := Q.frame_orthonormal v hv
  have hinner (i j : Fin 4) :
      inner ℝ (Q.frame v i) (Q.frame v j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp horth i j
  have hnorm (i : Fin 4) : ‖Q.frame v i‖ = 1 := horth.norm_eq_one i
  funext k
  fin_cases k <;>
    simp [operatorTwoCoords, frameBasis_apply, plusI,
      Q.I_frame_zero, Q.I_frame_one, Q.I_frame_two,
      hinner, hnorm, Fin.ext_iff]

theorem J_coordinates (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    operatorTwoCoords (frameBasis Q hdim v hv) Q.J.toLinearEquiv.toLinearMap = plusJ := by
  have horth := Q.frame_orthonormal v hv
  have hinner (i j : Fin 4) :
      inner ℝ (Q.frame v i) (Q.frame v j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp horth i j
  have hnorm (i : Fin 4) : ‖Q.frame v i‖ = 1 := horth.norm_eq_one i
  funext k
  fin_cases k <;>
    simp [operatorTwoCoords, frameBasis_apply, plusJ,
      Q.J_frame_zero, Q.J_frame_one, Q.J_frame_two,
      hinner, hnorm, Fin.ext_iff]

theorem K_coordinates (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    operatorTwoCoords (frameBasis Q hdim v hv) Q.K.toLinearEquiv.toLinearMap = plusK := by
  have horth := Q.frame_orthonormal v hv
  have hinner (i j : Fin 4) :
      inner ℝ (Q.frame v i) (Q.frame v j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp horth i j
  have hnorm (i : Fin 4) : ‖Q.frame v i‖ = 1 := horth.norm_eq_one i
  funext k
  fin_cases k <;>
    simp [operatorTwoCoords, frameBasis_apply, plusK,
      Q.K_frame_zero, Q.K_frame_one, Q.K_frame_two,
      hinner, hnorm, Fin.ext_iff]

theorem centralizer_coordinates_negative (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1)
    (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer) :
    FourDimensionalCoordinateHodge.star
      (operatorTwoCoords (frameBasis Q hdim v hv) A) =
      -operatorTwoCoords (frameBasis Q hdim v hv) A := by
  have h12 : inner ℝ (A (Q.I v)) (Q.J v) =
      -inner ℝ (A v) (Q.K v) := by
    rw [hA.2.1 v, Q.I_skew]
    rfl
  have h13 : inner ℝ (A (Q.I v)) (Q.K v) =
      inner ℝ (A v) (Q.J v) := by
    rw [hA.2.1 v, Q.I_skew]
    change -inner ℝ (A v) (Q.I (Q.I (Q.J v))) = _
    rw [Q.I_sq]
    simp
  have h23 : inner ℝ (A (Q.J v)) (Q.K v) =
      -inner ℝ (A v) (Q.I v) := by
    rw [hA.2.2 v, Q.J_skew]
    change -inner ℝ (A v) (Q.J (Q.I (Q.J v))) = _
    rw [Q.J_I_anti, Q.J_sq]
    simp
  simp only [K_apply] at h12 h13 h23
  funext k
  fin_cases k <;> simp [FourDimensionalCoordinateHodge.star,
    operatorTwoCoords, frameBasis_apply,
    QuaternionicStructure.frame, h12, h13, h23, Fin.ext_iff]

end
end QuaternionicSymmetry.FourDimensionalQuaternionicHodgeFrame
