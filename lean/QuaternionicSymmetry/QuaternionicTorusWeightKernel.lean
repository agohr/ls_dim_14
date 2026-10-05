import QuaternionicSymmetry.ManifoldQuaternionicTorusAction

/-! A nonzero integral character of a torus of rank at least two has a
nontrivial connected kernel. The witness is an explicit continuous curve
in the actual standard torus, not an assumed Lie-rank calculation. -/

namespace QuaternionicSymmetry.QuaternionicTorusWeightKernel

open ManifoldQuaternionicTorusAction
noncomputable section

variable {r : ℕ} (μ : Fin r → ℤ)

theorem continuous_weightCharacter : Continuous (weightCharacter μ) := by
  change Continuous (fun t : Torus r => ∏ i, t i ^ μ i)
  fun_prop

theorem isClosed_weightKernel : IsClosed (weightKernel μ : Set (Torus r)) :=
  isClosed_singleton.preimage (continuous_weightCharacter μ)

theorem isCompact_connectedWeightKernel :
    IsCompact (connectedWeightKernel μ : Set (Torus r)) := by
  letI : CompactSpace (weightKernel μ) :=
    isCompact_iff_compactSpace.mp (isClosed_weightKernel μ).isCompact
  have hc : IsCompact (connectedComponent (1 : weightKernel μ)) :=
    isClosed_connectedComponent.isCompact
  exact hc.image continuous_subtype_val

theorem isConnected_connectedWeightKernel :
    IsConnected (connectedWeightKernel μ : Set (Torus r)) :=
  isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn

theorem weightCharacter_mulSingle (i : Fin r) (z : Circle) :
    weightCharacter μ (Pi.mulSingle i z) = z ^ μ i := by
  classical
  simp [weightCharacter, Pi.mulSingle_apply]

def twoCoordinateCurve (i j : Fin r) (t : ℝ) : Torus r :=
  Pi.mulSingle i (Circle.exp ((μ j : ℝ)*t)) *
    Pi.mulSingle j (Circle.exp (-(μ i : ℝ)*t))

theorem continuous_twoCoordinateCurve (i j : Fin r) :
    Continuous (twoCoordinateCurve μ i j) := by
  classical
  apply continuous_pi
  intro k
  simp only [twoCoordinateCurve, Pi.mul_apply, Pi.mulSingle_apply]
  split_ifs <;> fun_prop

theorem twoCoordinateCurve_zero (i j : Fin r) :
    twoCoordinateCurve μ i j 0 = 1 := by
  classical
  simp [twoCoordinateCurve]

theorem twoCoordinateCurve_mem_kernel (i j : Fin r) (t : ℝ) :
    twoCoordinateCurve μ i j t ∈ weightKernel μ := by
  change weightCharacter μ (twoCoordinateCurve μ i j t) = 1
  rw [twoCoordinateCurve, map_mul, weightCharacter_mulSingle, weightCharacter_mulSingle,
    ← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul, ← Circle.exp_add]
  convert Circle.exp_zero using 1 <;> congr 1 <;> ring

theorem twoCoordinateCurve_mem_connectedKernel (i j : Fin r) (t : ℝ) :
    twoCoordinateCurve μ i j t ∈ connectedWeightKernel μ := by
  let c : ℝ → weightKernel μ := fun t =>
    ⟨twoCoordinateCurve μ i j t, twoCoordinateCurve_mem_kernel μ i j t⟩
  have hc : Continuous c :=
    (continuous_twoCoordinateCurve μ i j).subtype_mk _
  have hzero : c 0 = 1 := Subtype.ext (twoCoordinateCurve_zero μ i j)
  have ht : t ∈ connectedComponent (0 : ℝ) := by
    rw [preconnectedSpace_iff_connectedComponent.mp inferInstance]
    trivial
  have hmem := hc.mapsTo_connectedComponent 0 ht
  rw [hzero] at hmem
  exact ⟨c t, hmem, rfl⟩

theorem connectedKernel_has_nonidentity
    (hr : 2 ≤ r) (hμ : μ ≠ 0) :
    ∃ t : Torus r, t ∈ connectedWeightKernel μ ∧ t ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
    by_contra h
    apply hμ
    funext i
    simpa using not_exists.mp h i
  have hcard : 1 < Fintype.card (Fin r) := by simpa using hr
  haveI : Nontrivial (Fin r) := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨j, hji⟩ := exists_ne i
  let a : ℝ := -Real.pi / (μ i : ℝ)
  refine ⟨twoCoordinateCurve μ i j a,
    twoCoordinateCurve_mem_connectedKernel μ i j a, ?_⟩
  intro h
  have hj := congrArg (fun t : Torus r => t j) h
  have hμreal : (μ i : ℝ) ≠ 0 := by exact_mod_cast hi
  have hangle : -(μ i : ℝ) * a = Real.pi := by
    dsimp [a]
    field_simp
  simp only [twoCoordinateCurve, Pi.mul_apply,
    Pi.mulSingle_eq_of_ne hji, Pi.mulSingle_eq_same, one_mul, Pi.one_apply] at hj
  rw [hangle] at hj
  exact Circle.exp_pi_ne_one hj

end
end QuaternionicSymmetry.QuaternionicTorusWeightKernel
