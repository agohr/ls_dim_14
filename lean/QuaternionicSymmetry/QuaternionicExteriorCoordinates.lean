import QuaternionicSymmetry.QuaternionicEigenbasisCoordinates
import QuaternionicSymmetry.ExteriorCovectorTransport
import QuaternionicSymmetry.ExteriorBasisCoordinates
import QuaternionicSymmetry.HyperholomorphicExterior
import QuaternionicSymmetry.QuaternionicBlocks

/-! Identification of quaternionic coordinate blocks with actual exterior two-forms. -/

namespace QuaternionicSymmetry
namespace QuaternionicExteriorCoordinates

open Module
open scoped BigOperators

noncomputable section

variable {V β : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fintype β] [DecidableEq β]

omit [Fintype β] in
private theorem insert_e (j : β) (k : Fin 4) :
    QuaternionicBlocks.insert j (FourDimensionalForms.e k) =
      Pi.single (j, k) 1 := by
  funext p
  rcases p with ⟨r, a⟩
  by_cases hr : r = j
  · subst r
    by_cases ha : a = k
    · subst a
      simp [QuaternionicBlocks.insert, FourDimensionalForms.e]
    · simp [QuaternionicBlocks.insert, FourDimensionalForms.e, ha]
  · simp [QuaternionicBlocks.insert, hr]

theorem transport_g (b : Basis (β × Fin 4) ℝ V) (j : β) (k : Fin 4) :
    ExteriorCovectorTransport.exteriorCovectorMap b (QuaternionicBlocks.g j k) =
      ExteriorAlgebra.ι ℝ (b.coord (j, k)) := by
  rw [QuaternionicBlocks.g, ExteriorCovectorTransport.exteriorCovectorMap_ι]
  rw [insert_e, ExteriorCovectorTransport.covectorMap_single]

theorem transport_alpha_expanded (b : Basis (β × Fin 4) ℝ V) (j : β) :
    ExteriorCovectorTransport.exteriorCovectorMap b (QuaternionicBlocks.α j) =
      ExteriorAlgebra.ι ℝ (b.coord (j, 0)) * ExteriorAlgebra.ι ℝ (b.coord (j, 1)) -
        ExteriorAlgebra.ι ℝ (b.coord (j, 2)) * ExteriorAlgebra.ι ℝ (b.coord (j, 3)) := by
  rw [QuaternionicBlocks.alpha_eq]
  simp only [map_sub, map_mul, transport_g]

theorem transport_omegaI_expanded (b : Basis (β × Fin 4) ℝ V) (j : β) :
    ExteriorCovectorTransport.exteriorCovectorMap b (QuaternionicBlocks.ωI j) =
      ExteriorAlgebra.ι ℝ (b.coord (j, 0)) * ExteriorAlgebra.ι ℝ (b.coord (j, 1)) +
        ExteriorAlgebra.ι ℝ (b.coord (j, 2)) * ExteriorAlgebra.ι ℝ (b.coord (j, 3)) := by
  rw [QuaternionicBlocks.omegaI_eq]
  simp only [map_add, map_mul, transport_g]

theorem transport_omegaJ_expanded (b : Basis (β × Fin 4) ℝ V) (j : β) :
    ExteriorCovectorTransport.exteriorCovectorMap b (QuaternionicBlocks.ωJ j) =
      ExteriorAlgebra.ι ℝ (b.coord (j, 0)) * ExteriorAlgebra.ι ℝ (b.coord (j, 2)) -
        ExteriorAlgebra.ι ℝ (b.coord (j, 1)) * ExteriorAlgebra.ι ℝ (b.coord (j, 3)) := by
  rw [QuaternionicBlocks.omegaJ_eq]
  simp only [map_sub, map_mul, transport_g]

theorem transport_omegaK_expanded (b : Basis (β × Fin 4) ℝ V) (j : β) :
    ExteriorCovectorTransport.exteriorCovectorMap b (QuaternionicBlocks.ωK j) =
      ExteriorAlgebra.ι ℝ (b.coord (j, 0)) * ExteriorAlgebra.ι ℝ (b.coord (j, 3)) +
        ExteriorAlgebra.ι ℝ (b.coord (j, 1)) * ExteriorAlgebra.ι ℝ (b.coord (j, 2)) := by
  rw [QuaternionicBlocks.omegaK_eq]
  simp only [map_add, map_mul, transport_g]

private def pair (b : Basis (β × Fin 4) ℝ V) (p q : β × Fin 4) :
    ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) :=
  exteriorPower.ιMulti ℝ 2 ![b.coord p, b.coord q]

private def alphaCoordinates (b : Basis (β × Fin 4) ℝ V) (vals : β → ℝ) :
    ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) :=
  ∑ j, vals j • (pair b (j, 0) (j, 1) - pair b (j, 2) (j, 3))

omit [Fintype β] [DecidableEq β] in
private theorem coe_pair (b : Basis (β × Fin 4) ℝ V) (p q : β × Fin 4) :
    (pair b p q : ExteriorAlgebra ℝ (Module.Dual ℝ V)) =
      ExteriorAlgebra.ι ℝ (b.coord p) * ExteriorAlgebra.ι ℝ (b.coord q) := by
  simp [pair, ExteriorAlgebra.ιMulti_apply]

theorem transport_alpha_sum (b : Basis (β × Fin 4) ℝ V) (vals : β → ℝ) :
    ExteriorCovectorTransport.exteriorCovectorMap b
        (∑ j, vals j • QuaternionicBlocks.α j) = alphaCoordinates b vals := by
  simp only [map_sum, map_smul, transport_alpha_expanded, alphaCoordinates, coe_pair,
    Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_sub]

private theorem sum_single_product (vals : β → ℝ) (j l : β) (r s : Fin 4) :
    ∑ x, vals x *
      ((Finsupp.single (j, r) 1) (x, r) * (Finsupp.single (l, s) 1) (x, s)) =
      if j = l then vals j else 0 := by
  by_cases h : j = l
  · subst l
    rw [Finset.sum_eq_single j]
    · simp
    · intro x _ hx
      simp [hx]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro x _
    simp only [Finsupp.single_apply]
    by_cases hxj : x = j
    · subst x
      simp [Ne.symm h]
    · simp [Ne.symm hxj]

private theorem sum_single_product_one (j l : β) (r s : Fin 4) :
    ∑ x, (Finsupp.single (j, r) (1 : ℝ)) (x, r) *
      (Finsupp.single (l, s) (1 : ℝ)) (x, s) =
      if j = l then (1 : ℝ) else 0 := by
  simpa using sum_single_product (fun _ : β => (1 : ℝ)) j l r s

set_option maxHeartbeats 1000000 in
private theorem evaluate_alphaCoordinates (b : Basis (β × Fin 4) ℝ V) (vals : β → ℝ)
    (j l : β) (k m : Fin 4) :
    BilinearExterior.evaluate (b (j, k)) (b (l, m)) (alphaCoordinates b vals) =
      if j = l then vals j * QuaternionicStructure.alphaCoeff k m else 0 := by
  unfold alphaCoordinates pair
  fin_cases k <;> fin_cases m <;> by_cases h : j = l <;>
    simp [BilinearExterior.evaluate_wedge, QuaternionicStructure.alphaCoeff,
      sum_single_product, h]

theorem alphaCoordinates_eq_form (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) (vals : β → ℝ) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2)
    (heig : ∀ j, A (v j) = vals j • Q.I (v j)) :
    alphaCoordinates b.toBasis vals = HyperholomorphicExterior.form b.toBasis A := by
  have horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2) := by
    rw [show (fun p : β × Fin 4 => Q.frame (v p.1) p.2) = b by
      funext p
      exact (hb p).symm]
    exact b.orthonormal
  apply ExteriorBasisCoordinates.twoform_ext_basis b.toBasis
  rintro ⟨j, k⟩ ⟨l, m⟩
  rw [evaluate_alphaCoordinates]
  rw [HyperholomorphicExterior.evaluate_form b.toBasis A hA.1]
  simpa only [OrthonormalBasis.coe_toBasis, hb] using
    (QuaternionicStructure.A_coordinate Q A hA vals v horth heig j l k m).symm

theorem transport_alpha_sum_eq_form (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) (vals : β → ℝ) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2)
    (heig : ∀ j, A (v j) = vals j • Q.I (v j)) :
    ExteriorCovectorTransport.exteriorCovectorMap b.toBasis
        (∑ j, vals j • QuaternionicBlocks.α j) =
      (HyperholomorphicExterior.form b.toBasis A : ExteriorAlgebra ℝ (Module.Dual ℝ V)) := by
  rw [transport_alpha_sum]
  exact congrArg Subtype.val (alphaCoordinates_eq_form Q A hA vals v b hb heig)

private def omegaICoordinates (b : Basis (β × Fin 4) ℝ V) :
    ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) :=
  ∑ j, (pair b (j, 0) (j, 1) + pair b (j, 2) (j, 3))

private def omegaJCoordinates (b : Basis (β × Fin 4) ℝ V) :
    ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) :=
  ∑ j, (pair b (j, 0) (j, 2) - pair b (j, 1) (j, 3))

private def omegaKCoordinates (b : Basis (β × Fin 4) ℝ V) :
    ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) :=
  ∑ j, (pair b (j, 0) (j, 3) + pair b (j, 1) (j, 2))

set_option maxHeartbeats 1000000 in
private theorem evaluate_omegaICoordinates (b : Basis (β × Fin 4) ℝ V)
    (j l : β) (k m : Fin 4) :
    BilinearExterior.evaluate (b (j, k)) (b (l, m)) (omegaICoordinates b) =
      if j = l then QuaternionicStructure.omegaICoeff k m else 0 := by
  unfold omegaICoordinates pair
  fin_cases k <;> fin_cases m <;> by_cases h : j = l <;>
    simp [BilinearExterior.evaluate_wedge, QuaternionicStructure.omegaICoeff,
      sum_single_product_one, h]

set_option maxHeartbeats 1000000 in
private theorem evaluate_omegaJCoordinates (b : Basis (β × Fin 4) ℝ V)
    (j l : β) (k m : Fin 4) :
    BilinearExterior.evaluate (b (j, k)) (b (l, m)) (omegaJCoordinates b) =
      if j = l then QuaternionicStructure.omegaJCoeff k m else 0 := by
  unfold omegaJCoordinates pair
  fin_cases k <;> fin_cases m <;> by_cases h : j = l <;>
    simp [BilinearExterior.evaluate_wedge, QuaternionicStructure.omegaJCoeff,
      sum_single_product_one, h]

set_option maxHeartbeats 1000000 in
private theorem evaluate_omegaKCoordinates (b : Basis (β × Fin 4) ℝ V)
    (j l : β) (k m : Fin 4) :
    BilinearExterior.evaluate (b (j, k)) (b (l, m)) (omegaKCoordinates b) =
      if j = l then QuaternionicStructure.omegaKCoeff k m else 0 := by
  unfold omegaKCoordinates pair
  fin_cases k <;> fin_cases m <;> by_cases h : j = l <;>
    simp [BilinearExterior.evaluate_wedge, QuaternionicStructure.omegaKCoeff,
      sum_single_product_one, h]

theorem transport_omegaI_sum (b : Basis (β × Fin 4) ℝ V) :
    ExteriorCovectorTransport.exteriorCovectorMap b (∑ j, QuaternionicBlocks.ωI j) =
      omegaICoordinates b := by
  simp only [map_sum, transport_omegaI_expanded, omegaICoordinates, coe_pair,
    Submodule.coe_sum, Submodule.coe_add]

theorem transport_omegaJ_sum (b : Basis (β × Fin 4) ℝ V) :
    ExteriorCovectorTransport.exteriorCovectorMap b (∑ j, QuaternionicBlocks.ωJ j) =
      omegaJCoordinates b := by
  simp only [map_sum, transport_omegaJ_expanded, omegaJCoordinates, coe_pair,
    Submodule.coe_sum, Submodule.coe_sub]

theorem transport_omegaK_sum (b : Basis (β × Fin 4) ℝ V) :
    ExteriorCovectorTransport.exteriorCovectorMap b (∑ j, QuaternionicBlocks.ωK j) =
      omegaKCoordinates b := by
  simp only [map_sum, transport_omegaK_expanded, omegaKCoordinates, coe_pair,
    Submodule.coe_sum, Submodule.coe_add]

omit [DecidableEq β] in
private theorem frame_orthonormal (Q : QuaternionicStructure V) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2) :
    Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2) := by
  rw [show (fun p : β × Fin 4 => Q.frame (v p.1) p.2) = b by
    funext p
    exact (hb p).symm]
  exact b.orthonormal

theorem omegaICoordinates_eq_form (Q : QuaternionicStructure V) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2) :
    omegaICoordinates b.toBasis = HyperholomorphicExterior.form b.toBasis Q.I.toLinearMap := by
  have horth := frame_orthonormal Q v b hb
  apply ExteriorBasisCoordinates.twoform_ext_basis b.toBasis
  rintro ⟨j, k⟩ ⟨l, m⟩
  rw [evaluate_omegaICoordinates]
  rw [HyperholomorphicExterior.evaluate_form b.toBasis Q.I.toLinearMap Q.I_skew]
  simpa only [OrthonormalBasis.coe_toBasis, hb] using
    (QuaternionicStructure.I_coordinate Q v horth j l k m).symm

theorem omegaJCoordinates_eq_form (Q : QuaternionicStructure V) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2) :
    omegaJCoordinates b.toBasis = HyperholomorphicExterior.form b.toBasis Q.J.toLinearMap := by
  have horth := frame_orthonormal Q v b hb
  apply ExteriorBasisCoordinates.twoform_ext_basis b.toBasis
  rintro ⟨j, k⟩ ⟨l, m⟩
  rw [evaluate_omegaJCoordinates]
  rw [HyperholomorphicExterior.evaluate_form b.toBasis Q.J.toLinearMap Q.J_skew]
  simpa only [OrthonormalBasis.coe_toBasis, hb] using
    (QuaternionicStructure.J_coordinate Q v horth j l k m).symm

theorem omegaKCoordinates_eq_form (Q : QuaternionicStructure V) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2) :
    omegaKCoordinates b.toBasis = HyperholomorphicExterior.form b.toBasis Q.K.toLinearMap := by
  have horth := frame_orthonormal Q v b hb
  apply ExteriorBasisCoordinates.twoform_ext_basis b.toBasis
  rintro ⟨j, k⟩ ⟨l, m⟩
  rw [evaluate_omegaKCoordinates]
  rw [HyperholomorphicExterior.evaluate_form b.toBasis Q.K.toLinearMap Q.K_skew]
  simpa only [OrthonormalBasis.coe_toBasis, hb] using
    (QuaternionicStructure.K_coordinate Q v horth j l k m).symm

theorem transport_omegaI_sum_eq_form (Q : QuaternionicStructure V) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2) :
    ExteriorCovectorTransport.exteriorCovectorMap b.toBasis (∑ j, QuaternionicBlocks.ωI j) =
      (HyperholomorphicExterior.form b.toBasis Q.I.toLinearMap : ExteriorAlgebra ℝ (Module.Dual ℝ V)) := by
  rw [transport_omegaI_sum]
  exact congrArg Subtype.val (omegaICoordinates_eq_form Q v b hb)

theorem transport_omegaJ_sum_eq_form (Q : QuaternionicStructure V) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2) :
    ExteriorCovectorTransport.exteriorCovectorMap b.toBasis (∑ j, QuaternionicBlocks.ωJ j) =
      (HyperholomorphicExterior.form b.toBasis Q.J.toLinearMap : ExteriorAlgebra ℝ (Module.Dual ℝ V)) := by
  rw [transport_omegaJ_sum]
  exact congrArg Subtype.val (omegaJCoordinates_eq_form Q v b hb)

theorem transport_omegaK_sum_eq_form (Q : QuaternionicStructure V) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2) :
    ExteriorCovectorTransport.exteriorCovectorMap b.toBasis (∑ j, QuaternionicBlocks.ωK j) =
      (HyperholomorphicExterior.form b.toBasis Q.K.toLinearMap : ExteriorAlgebra ℝ (Module.Dual ℝ V)) := by
  rw [transport_omegaK_sum]
  exact congrArg Subtype.val (omegaKCoordinates_eq_form Q v b hb)

end
end QuaternionicExteriorCoordinates
end QuaternionicSymmetry
