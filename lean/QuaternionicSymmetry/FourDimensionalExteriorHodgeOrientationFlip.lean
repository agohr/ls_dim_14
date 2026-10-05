import QuaternionicSymmetry.FourDimensionalExteriorHodge

/-! An explicit reversal of one quaternionic orthonormal frame reverses the
genuine exterior two-form star. This certifies the sign change, without
identifying either orientation with an external spinor convention. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorHodgeOrientationFlip

open FourDimensionalExteriorHodge FourDimensionalCoordinateHodge
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def swap01 (b : OrthonormalBasis (Fin 4) ℝ V) :
    OrthonormalBasis (Fin 4) ℝ V :=
  b.reindex (Equiv.swap (0 : Fin 4) 1)

def swap01Coords : Two →ₗ[ℝ] Two where
  toFun x := ![-x 0, x 3, x 4, x 1, x 2, x 5]
  map_add' x y := by funext i; fin_cases i <;> simp [Pi.add_apply] <;> abel
  map_smul' c x := by funext i; fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]

private theorem evaluate_swap (α : TwoForm V) (v w : V) :
    BilinearExterior.evaluate w v α = -BilinearExterior.evaluate v w α := by
  have h := (exteriorPower.ιMulti ℝ 2 (M := V)).map_swap
    ![v,w] (i := 0) (j := 1) (by decide)
  have hp : (![v,w] : Fin 2 → V) ∘ Equiv.swap 0 1 = ![w,v] := by
    funext i
    fin_cases i <;> simp
  rw [hp] at h
  simp [BilinearExterior.evaluate, h]

theorem coordinates_swap01 (b : OrthonormalBasis (Fin 4) ℝ V)
    (α : TwoForm V) :
    coordinates (swap01 b).toBasis α =
      swap01Coords (coordinates b.toBasis α) := by
  funext i
  fin_cases i <;>
    simp [coordinates, swap01, swap01Coords,
      OrthonormalBasis.reindex_toBasis,
      Equiv.swap_apply_def]
  exact evaluate_swap α (b 0) (b 1)

theorem swap01Coords_star (x : Two) :
    swap01Coords (FourDimensionalCoordinateHodge.star x) =
      -FourDimensionalCoordinateHodge.star (swap01Coords x) := by
  funext i
  fin_cases i <;> simp [swap01Coords, FourDimensionalCoordinateHodge.star]

/-- Swapping the first two vectors reverses the literal Mathlib orientation
of the real four-dimensional vector space. -/
theorem swap01_orientation [FiniteDimensional ℝ V]
    (b : OrthonormalBasis (Fin 4) ℝ V) :
    (swap01 b).toBasis.orientation = -b.toBasis.orientation := by
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 1
  have hdet : b.toBasis.det (swap01 b).toBasis = -1 := by
    rw [swap01, OrthonormalBasis.reindex_toBasis, Module.Basis.coe_reindex]
    change b.toBasis.det (b.toBasis ∘ σ.symm) = -1
    rw [AlternatingMap.map_perm]
    simp [σ]
    simpa only [OrthonormalBasis.coe_toBasis] using b.toBasis.det_self
  apply (b.toBasis.orientation_ne_iff_eq_neg _).mp
  intro he
  have hp := (Module.Basis.orientation_eq_iff_det_pos b.toBasis
    (swap01 b).toBasis).mp he.symm
  rw [hdet] at hp
  norm_num at hp

theorem frameStar_swap01 (b : OrthonormalBasis (Fin 4) ℝ V)
    (α : TwoForm V) :
    frameStar (swap01 b) α = -frameStar b α := by
  apply (coordinateEquiv (swap01 b).toBasis).injective
  change coordinates (swap01 b).toBasis (frameStar (swap01 b) α) =
    coordinates (swap01 b).toBasis (-frameStar b α)
  rw [coordinates_frameStar, coordinates_swap01, map_neg,
    coordinates_swap01, coordinates_frameStar,
    swap01Coords_star]
  simp

end
end QuaternionicSymmetry.FourDimensionalExteriorHodgeOrientationFlip
