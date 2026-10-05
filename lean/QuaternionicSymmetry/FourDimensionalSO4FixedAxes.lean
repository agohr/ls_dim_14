import QuaternionicSymmetry.FourDimensionalSO4PairTransport
import QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedOrientation

/-! An orientation-preserving real orthogonal map of `ℍ` that fixes the
standard scalar, I, and J axes also fixes K. This is the missing sign check
for the concrete `Sp(1) × Sp(1)` presentation of `SO(4)`. -/

namespace QuaternionicSymmetry.FourDimensionalSO4FixedAxes

open scoped Quaternion
open QuaternionicUnitQuaternionTransport

noncomputable section

private def b :=
  QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1)

private theorem det_fixed_three (G : ℍ ≃ₗᵢ[ℝ] ℍ)
    (h0 : G 1 = 1) (hI : G basisI = basisI)
    (hJ : G basisJ = basisJ) :
    LinearMap.det (G : ℍ →ₗ[ℝ] ℍ) = (G (b 3)).imK := by
  let M := LinearMap.toMatrix b b (G : ℍ →ₗ[ℝ] ℍ)
  have hm (i j : Fin 4) : M i j = (b.repr (G (b j))) i := by
    exact LinearMap.toMatrix_apply _ _ _ _ _
  have hcol (j : Fin 4) (hj : j < 3) : G (b j) = b j := by
    fin_cases j
    · simpa [b, QuaternionAlgebra.basisOneIJK] using h0
    · simpa [b, QuaternionAlgebra.basisOneIJK, basisI] using hI
    · simpa [b, QuaternionAlgebra.basisOneIJK, basisJ] using hJ
    · exact False.elim ((by decide : ¬ ((3 : Fin 4) < 3)) hj)
  have htri : M.BlockTriangular id := by
    intro i j hij
    change j < i at hij
    have hj : j < 3 := by omega
    rw [hm, hcol j hj]
    rw [b.repr_self_apply]
    simp [ne_of_lt hij]
  have hdiag (i : Fin 4) : M i i = if i = 3 then (G (b 3)).imK else 1 := by
    by_cases hi : i = 3
    · subst i
      simp [hm, b, QuaternionAlgebra.coe_basisOneIJK_repr]
    · have hil : i < 3 := by omega
      rw [hm, hcol i hil]
      simp [b, hi]
  calc
    LinearMap.det (G : ℍ →ₗ[ℝ] ℍ) = M.det :=
      (LinearMap.det_toMatrix b _).symm
    _ = ∏ i : Fin 4, M i i := Matrix.det_of_upperTriangular htri
    _ = (G (b 3)).imK := by
      simp [hdiag, Fin.prod_univ_succ]

theorem eq_one_of_fixed_three (G : ℍ ≃ₗᵢ[ℝ] ℍ)
    (h0 : G 1 = 1) (hI : G basisI = basisI)
    (hJ : G basisJ = basisJ)
    (hdet : 0 < LinearMap.det (G : ℍ →ₗ[ℝ] ℍ)) :
    G = 1 := by
  have hb0 : (b 0 : ℍ) = 1 := by
    ext <;> norm_num [b, QuaternionAlgebra.basisOneIJK]
  have hb1 : (b 1 : ℍ) = basisI := by
    simp [b, QuaternionAlgebra.basisOneIJK, basisI]
  have hb2 : (b 2 : ℍ) = basisJ := by
    simp [b, QuaternionAlgebra.basisOneIJK, basisJ]
  have hreal : (G (b 3)).re = 0 := by
    have h := G.inner_map_map (b 3) (b 0)
    rw [hb0, h0] at h
    simpa [Quaternion.inner_def, b, QuaternionAlgebra.basisOneIJK] using h
  have hIcoord : (G (b 3)).imI = 0 := by
    have h := G.inner_map_map (b 3) (b 1)
    rw [hb1, hI] at h
    simpa [Quaternion.inner_def, basisI, b,
      QuaternionAlgebra.basisOneIJK] using h
  have hJcoord : (G (b 3)).imJ = 0 := by
    have h := G.inner_map_map (b 3) (b 2)
    rw [hb2, hJ] at h
    simpa [Quaternion.inner_def, basisJ, b,
      QuaternionAlgebra.basisOneIJK] using h
  have hn : Quaternion.normSq (G (b 3)) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self,
      show ‖G (b 3)‖ = ‖b 3‖ from G.norm_map (b 3),
      ← Quaternion.normSq_eq_norm_mul_self]
    norm_num [b, QuaternionAlgebra.basisOneIJK,
      Quaternion.normSq_def']
  have hkpos : 0 < (G (b 3)).imK := by
    simpa [det_fixed_three G h0 hI hJ] using hdet
  have hk : (G (b 3)).imK = 1 := by
    rw [Quaternion.normSq_def'] at hn
    nlinarith
  have hK : G (b 3) = b 3 := by
    ext
    · simpa [b, QuaternionAlgebra.basisOneIJK] using hreal
    · simpa [b, QuaternionAlgebra.basisOneIJK] using hIcoord
    · simpa [b, QuaternionAlgebra.basisOneIJK] using hJcoord
    · simpa [b, QuaternionAlgebra.basisOneIJK] using hk
  have hmap : (G : ℍ →ₗ[ℝ] ℍ) = LinearMap.id := by
    apply b.ext
    intro i
    fin_cases i
    · simpa [hb0] using h0
    · simpa [hb1] using hI
    · simpa [hb2] using hJ
    · simpa using hK
  apply LinearIsometryEquiv.ext
  intro x
  simpa using congrArg (fun f : ℍ →ₗ[ℝ] ℍ => f x) hmap

end
end QuaternionicSymmetry.FourDimensionalSO4FixedAxes
