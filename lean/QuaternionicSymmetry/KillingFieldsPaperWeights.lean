import QuaternionicSymmetry.KillingFieldsPaperLinearBound
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
open ManifoldSevenVariableGradedEvaluation
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

private theorem h0 : IsWeightedHomogeneous slotGrade u 1 :=
  isWeightedHomogeneous_X ℚ slotGrade 0

private theorem h1 : IsWeightedHomogeneous slotGrade p1 1 :=
  isWeightedHomogeneous_X ℚ slotGrade 1

private theorem h2 : IsWeightedHomogeneous slotGrade p2 2 :=
  isWeightedHomogeneous_X ℚ slotGrade 2

private theorem h3 : IsWeightedHomogeneous slotGrade p3 3 :=
  isWeightedHomogeneous_X ℚ slotGrade 3

private theorem h4 : IsWeightedHomogeneous slotGrade p4 4 :=
  isWeightedHomogeneous_X ℚ slotGrade 4

private theorem h5 : IsWeightedHomogeneous slotGrade p5 5 :=
  isWeightedHomogeneous_X ℚ slotGrade 5

private theorem h6 : IsWeightedHomogeneous slotGrade p6 6 :=
  isWeightedHomogeneous_X ℚ slotGrade 6

theorem eta_weighted : IsWeightedHomogeneous slotGrade eta 3 := by
  rw [eta_eq]
  unfold expandedEta
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    ((((((isWeightedHomogeneous_C slotGrade (960 / 203 : ℚ)).mul (h0.pow 2)).mul h1).add ((isWeightedHomogeneous_C slotGrade (20560 / 72891819 : ℚ)).mul h3)).add (((isWeightedHomogeneous_C slotGrade (136 / 207669 : ℚ)).mul h1).mul h2)).add ((isWeightedHomogeneous_C slotGrade (27176 / 72891819 : ℚ)).mul (h1.pow 3)))

theorem reduced2_weighted : IsWeightedHomogeneous slotGrade (reduced 2) 0 := by
  change IsWeightedHomogeneous slotGrade reduced2 _
  unfold reduced2
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    (isWeightedHomogeneous_C slotGrade (16 : ℚ))

theorem reduced3_weighted : IsWeightedHomogeneous slotGrade (reduced 3) 1 := by
  change IsWeightedHomogeneous slotGrade reduced3 _
  unfold reduced3
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    (((isWeightedHomogeneous_C slotGrade (32 : ℚ)).mul h0).add ((isWeightedHomogeneous_C slotGrade (8 / 3 : ℚ)).mul h1))

theorem reduced4_weighted : IsWeightedHomogeneous slotGrade (reduced 4) 1 := by
  change IsWeightedHomogeneous slotGrade reduced4 _
  unfold reduced4
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    (((isWeightedHomogeneous_C slotGrade (48 : ℚ)).mul h0).add ((isWeightedHomogeneous_C slotGrade (16 / 3 : ℚ)).mul h1))

theorem reduced5_weighted : IsWeightedHomogeneous slotGrade (reduced 5) 2 := by
  change IsWeightedHomogeneous slotGrade reduced5 _
  unfold reduced5
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    (((((isWeightedHomogeneous_C slotGrade (72 : ℚ)).mul (h0.pow 2)).add (((isWeightedHomogeneous_C slotGrade (536 / 45 : ℚ)).mul h0).mul h1)).add ((isWeightedHomogeneous_C slotGrade (4 / 45 : ℚ)).mul h2)).add ((isWeightedHomogeneous_C slotGrade (4 / 9 : ℚ)).mul (h1.pow 2)))

theorem reduced6_weighted : IsWeightedHomogeneous slotGrade (reduced 6) 2 := by
  change IsWeightedHomogeneous slotGrade reduced6 _
  unfold reduced6
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    (((((isWeightedHomogeneous_C slotGrade (96 : ℚ)).mul (h0.pow 2)).add (((isWeightedHomogeneous_C slotGrade (832 / 45 : ℚ)).mul h0).mul h1)).add ((isWeightedHomogeneous_C slotGrade (8 / 45 : ℚ)).mul h2)).add ((isWeightedHomogeneous_C slotGrade (8 / 9 : ℚ)).mul (h1.pow 2)))

theorem reduced7_weighted : IsWeightedHomogeneous slotGrade (reduced 7) 3 := by
  change IsWeightedHomogeneous slotGrade reduced7 _
  unfold reduced7
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    ((((((((isWeightedHomogeneous_C slotGrade (128 : ℚ)).mul (h0.pow 3)).add (((isWeightedHomogeneous_C slotGrade (208 / 7 : ℚ)).mul (h0.pow 2)).mul h1)).add (((isWeightedHomogeneous_C slotGrade (368 / 945 : ℚ)).mul h0).mul h2)).add (((isWeightedHomogeneous_C slotGrade (296 / 135 : ℚ)).mul h0).mul (h1.pow 2))).add ((isWeightedHomogeneous_C slotGrade (16 / 2835 : ℚ)).mul h3)).add (((isWeightedHomogeneous_C slotGrade (4 / 135 : ℚ)).mul h1).mul h2)).add ((isWeightedHomogeneous_C slotGrade (4 / 81 : ℚ)).mul (h1.pow 3)))

theorem reduced8_weighted : IsWeightedHomogeneous slotGrade (reduced 8) 3 := by
  change IsWeightedHomogeneous slotGrade reduced8 _
  unfold reduced8
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    ((((((((isWeightedHomogeneous_C slotGrade (160 : ℚ)).mul (h0.pow 3)).add (((isWeightedHomogeneous_C slotGrade (12896 / 315 : ℚ)).mul (h0.pow 2)).mul h1)).add (((isWeightedHomogeneous_C slotGrade (568 / 945 : ℚ)).mul h0).mul h2)).add (((isWeightedHomogeneous_C slotGrade (472 / 135 : ℚ)).mul h0).mul (h1.pow 2))).add ((isWeightedHomogeneous_C slotGrade (32 / 2835 : ℚ)).mul h3)).add (((isWeightedHomogeneous_C slotGrade (8 / 135 : ℚ)).mul h1).mul h2)).add ((isWeightedHomogeneous_C slotGrade (8 / 81 : ℚ)).mul (h1.pow 3)))

theorem reduced9_weighted : IsWeightedHomogeneous slotGrade (reduced 9) 4 := by
  change IsWeightedHomogeneous slotGrade reduced9 _
  unfold reduced9
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    (((((((((((((isWeightedHomogeneous_C slotGrade (200 : ℚ)).mul (h0.pow 4)).add (((isWeightedHomogeneous_C slotGrade (90256 / 1575 : ℚ)).mul (h0.pow 3)).mul h1)).add (((isWeightedHomogeneous_C slotGrade (4376 / 4725 : ℚ)).mul (h0.pow 2)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (85072 / 14175 : ℚ)).mul (h0.pow 2)).mul (h1.pow 2))).add (((isWeightedHomogeneous_C slotGrade (104 / 4725 : ℚ)).mul h0).mul h3)).add ((((isWeightedHomogeneous_C slotGrade (2036 / 14175 : ℚ)).mul h0).mul h1).mul h2)).add (((isWeightedHomogeneous_C slotGrade (4 / 15 : ℚ)).mul h0).mul (h1.pow 3))).add ((isWeightedHomogeneous_C slotGrade (2 / 4725 : ℚ)).mul h4)).add (((isWeightedHomogeneous_C slotGrade (16 / 8505 : ℚ)).mul h1).mul h3)).add ((isWeightedHomogeneous_C slotGrade (1 / 2025 : ℚ)).mul (h2.pow 2))).add (((isWeightedHomogeneous_C slotGrade (2 / 405 : ℚ)).mul (h1.pow 2)).mul h2)).add ((isWeightedHomogeneous_C slotGrade (1 / 243 : ℚ)).mul (h1.pow 4)))

theorem reduced10_weighted : IsWeightedHomogeneous slotGrade (reduced 10) 4 := by
  change IsWeightedHomogeneous slotGrade reduced10 _
  unfold reduced10
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    (((((((((((((isWeightedHomogeneous_C slotGrade (240 : ℚ)).mul (h0.pow 4)).add (((isWeightedHomogeneous_C slotGrade (16576 / 225 : ℚ)).mul (h0.pow 3)).mul h1)).add (((isWeightedHomogeneous_C slotGrade (5912 / 4725 : ℚ)).mul (h0.pow 2)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (120584 / 14175 : ℚ)).mul (h0.pow 2)).mul (h1.pow 2))).add (((isWeightedHomogeneous_C slotGrade (464 / 14175 : ℚ)).mul h0).mul h3)).add ((((isWeightedHomogeneous_C slotGrade (3232 / 14175 : ℚ)).mul h0).mul h1).mul h2)).add (((isWeightedHomogeneous_C slotGrade (176 / 405 : ℚ)).mul h0).mul (h1.pow 3))).add ((isWeightedHomogeneous_C slotGrade (4 / 4725 : ℚ)).mul h4)).add (((isWeightedHomogeneous_C slotGrade (32 / 8505 : ℚ)).mul h1).mul h3)).add ((isWeightedHomogeneous_C slotGrade (2 / 2025 : ℚ)).mul (h2.pow 2))).add (((isWeightedHomogeneous_C slotGrade (4 / 405 : ℚ)).mul (h1.pow 2)).mul h2)).add ((isWeightedHomogeneous_C slotGrade (2 / 243 : ℚ)).mul (h1.pow 4)))

theorem reduced11_weighted : IsWeightedHomogeneous slotGrade (reduced 11) 5 := by
  change IsWeightedHomogeneous slotGrade reduced11 _
  unfold reduced11
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    ((((((((((((((((((((isWeightedHomogeneous_C slotGrade (288 : ℚ)).mul (h0.pow 5)).add (((isWeightedHomogeneous_C slotGrade (4965304 / 51975 : ℚ)).mul (h0.pow 4)).mul h1)).add (((isWeightedHomogeneous_C slotGrade (154736 / 93555 : ℚ)).mul (h0.pow 3)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (35416 / 2835 : ℚ)).mul (h0.pow 3)).mul (h1.pow 2))).add (((isWeightedHomogeneous_C slotGrade (18848 / 467775 : ℚ)).mul (h0.pow 2)).mul h3)).add ((((isWeightedHomogeneous_C slotGrade (16052 / 42525 : ℚ)).mul (h0.pow 2)).mul h1).mul h2)).add (((isWeightedHomogeneous_C slotGrade (33772 / 42525 : ℚ)).mul (h0.pow 2)).mul (h1.pow 3))).add (((isWeightedHomogeneous_C slotGrade (8 / 6237 : ℚ)).mul h0).mul h4)).add ((((isWeightedHomogeneous_C slotGrade (1048 / 127575 : ℚ)).mul h0).mul h1).mul h3)).add (((isWeightedHomogeneous_C slotGrade (4 / 1701 : ℚ)).mul h0).mul (h2.pow 2))).add ((((isWeightedHomogeneous_C slotGrade (124 / 4725 : ℚ)).mul h0).mul (h1.pow 2)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (88 / 3645 : ℚ)).mul h0).mul (h1.pow 4))).add ((isWeightedHomogeneous_C slotGrade (16 / 467775 : ℚ)).mul h5)).add (((isWeightedHomogeneous_C slotGrade (2 / 14175 : ℚ)).mul h1).mul h4)).add (((isWeightedHomogeneous_C slotGrade (8 / 127575 : ℚ)).mul h2).mul h3)).add (((isWeightedHomogeneous_C slotGrade (8 / 25515 : ℚ)).mul (h1.pow 2)).mul h3)).add (((isWeightedHomogeneous_C slotGrade (1 / 6075 : ℚ)).mul h1).mul (h2.pow 2))).add (((isWeightedHomogeneous_C slotGrade (2 / 3645 : ℚ)).mul (h1.pow 3)).mul h2)).add ((isWeightedHomogeneous_C slotGrade (1 / 3645 : ℚ)).mul (h1.pow 5)))

theorem reduced12_weighted : IsWeightedHomogeneous slotGrade (reduced 12) 5 := by
  change IsWeightedHomogeneous slotGrade reduced12 _
  unfold reduced12
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    ((((((((((((((((((((isWeightedHomogeneous_C slotGrade (336 : ℚ)).mul (h0.pow 5)).add (((isWeightedHomogeneous_C slotGrade (6101552 / 51975 : ℚ)).mul (h0.pow 4)).mul h1)).add (((isWeightedHomogeneous_C slotGrade (962072 / 467775 : ℚ)).mul (h0.pow 3)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (33368 / 2025 : ℚ)).mul (h0.pow 3)).mul (h1.pow 2))).add (((isWeightedHomogeneous_C slotGrade (22384 / 467775 : ℚ)).mul (h0.pow 2)).mul h3)).add ((((isWeightedHomogeneous_C slotGrade (22408 / 42525 : ℚ)).mul (h0.pow 2)).mul h1).mul h2)).add (((isWeightedHomogeneous_C slotGrade (49064 / 42525 : ℚ)).mul (h0.pow 2)).mul (h1.pow 3))).add (((isWeightedHomogeneous_C slotGrade (268 / 155925 : ℚ)).mul h0).mul h4)).add ((((isWeightedHomogeneous_C slotGrade (1616 / 127575 : ℚ)).mul h0).mul h1).mul h3)).add (((isWeightedHomogeneous_C slotGrade (158 / 42525 : ℚ)).mul h0).mul (h2.pow 2))).add ((((isWeightedHomogeneous_C slotGrade (604 / 14175 : ℚ)).mul h0).mul (h1.pow 2)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (146 / 3645 : ℚ)).mul h0).mul (h1.pow 4))).add ((isWeightedHomogeneous_C slotGrade (32 / 467775 : ℚ)).mul h5)).add (((isWeightedHomogeneous_C slotGrade (4 / 14175 : ℚ)).mul h1).mul h4)).add (((isWeightedHomogeneous_C slotGrade (16 / 127575 : ℚ)).mul h2).mul h3)).add (((isWeightedHomogeneous_C slotGrade (16 / 25515 : ℚ)).mul (h1.pow 2)).mul h3)).add (((isWeightedHomogeneous_C slotGrade (2 / 6075 : ℚ)).mul h1).mul (h2.pow 2))).add (((isWeightedHomogeneous_C slotGrade (4 / 3645 : ℚ)).mul (h1.pow 3)).mul h2)).add ((isWeightedHomogeneous_C slotGrade (2 / 3645 : ℚ)).mul (h1.pow 5)))

theorem reduced13_weighted : IsWeightedHomogeneous slotGrade (reduced 13) 6 := by
  change IsWeightedHomogeneous slotGrade reduced13 _
  unfold reduced13
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    (((((((((((((((((((((((((((((((isWeightedHomogeneous_C slotGrade (392 : ℚ)).mul (h0.pow 6)).add (((isWeightedHomogeneous_C slotGrade (45727288 / 315315 : ℚ)).mul (h0.pow 5)).mul h1)).add (((isWeightedHomogeneous_C slotGrade (1781548 / 716625 : ℚ)).mul (h0.pow 4)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (121006364 / 5457375 : ℚ)).mul (h0.pow 4)).mul (h1.pow 2))).add (((isWeightedHomogeneous_C slotGrade (1323256 / 34827975 : ℚ)).mul (h0.pow 3)).mul h3)).add ((((isWeightedHomogeneous_C slotGrade (36184556 / 49116375 : ℚ)).mul (h0.pow 3)).mul h1).mul h2)).add (((isWeightedHomogeneous_C slotGrade (3397924 / 1913625 : ℚ)).mul (h0.pow 3)).mul (h1.pow 3))).add (((isWeightedHomogeneous_C slotGrade (8894 / 19348875 : ℚ)).mul (h0.pow 2)).mul h4)).add ((((isWeightedHomogeneous_C slotGrade (284456 / 16372125 : ℚ)).mul (h0.pow 2)).mul h1).mul h3)).add (((isWeightedHomogeneous_C slotGrade (26423 / 4465125 : ℚ)).mul (h0.pow 2)).mul (h2.pow 2))).add ((((isWeightedHomogeneous_C slotGrade (16042 / 212625 : ℚ)).mul (h0.pow 2)).mul (h1.pow 2)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (9911 / 127575 : ℚ)).mul (h0.pow 2)).mul (h1.pow 4))).add (((isWeightedHomogeneous_C slotGrade (1168 / 19348875 : ℚ)).mul h0).mul h5)).add ((((isWeightedHomogeneous_C slotGrade (1154 / 2338875 : ℚ)).mul h0).mul h1).mul h4)).add ((((isWeightedHomogeneous_C slotGrade (3596 / 13395375 : ℚ)).mul h0).mul h2).mul h3)).add ((((isWeightedHomogeneous_C slotGrade (116 / 76545 : ℚ)).mul h0).mul (h1.pow 2)).mul h3)).add ((((isWeightedHomogeneous_C slotGrade (61 / 70875 : ℚ)).mul h0).mul h1).mul (h2.pow 2))).add ((((isWeightedHomogeneous_C slotGrade (1214 / 382725 : ℚ)).mul h0).mul (h1.pow 3)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (19 / 10935 : ℚ)).mul h0).mul (h1.pow 5))).add ((isWeightedHomogeneous_C slotGrade (5528 / 1915538625 : ℚ)).mul h6)).add (((isWeightedHomogeneous_C slotGrade (16 / 1403325 : ℚ)).mul h1).mul h5)).add (((isWeightedHomogeneous_C slotGrade (1 / 212625 : ℚ)).mul h2).mul h4)).add (((isWeightedHomogeneous_C slotGrade (1 / 42525 : ℚ)).mul (h1.pow 2)).mul h4)).add ((isWeightedHomogeneous_C slotGrade (16 / 8037225 : ℚ)).mul (h3.pow 2))).add ((((isWeightedHomogeneous_C slotGrade (8 / 382725 : ℚ)).mul h1).mul h2).mul h3)).add (((isWeightedHomogeneous_C slotGrade (8 / 229635 : ℚ)).mul (h1.pow 3)).mul h3)).add ((isWeightedHomogeneous_C slotGrade (1 / 546750 : ℚ)).mul (h2.pow 3))).add (((isWeightedHomogeneous_C slotGrade (1 / 36450 : ℚ)).mul (h1.pow 2)).mul (h2.pow 2))).add (((isWeightedHomogeneous_C slotGrade (1 / 21870 : ℚ)).mul (h1.pow 4)).mul h2)).add ((isWeightedHomogeneous_C slotGrade (1 / 65610 : ℚ)).mul (h1.pow 6)))

theorem reduced14_weighted : IsWeightedHomogeneous slotGrade (reduced 14) 6 := by
  change IsWeightedHomogeneous slotGrade reduced14 _
  unfold reduced14
  simpa only [smul_eq_mul, Nat.reduceMul, Nat.reduceAdd] using
    (((((((((((((((((((((((((((((((isWeightedHomogeneous_C slotGrade (448 : ℚ)).mul (h0.pow 6)).add (((isWeightedHomogeneous_C slotGrade (816577408 / 4729725 : ℚ)).mul (h0.pow 5)).mul h1)).add (((isWeightedHomogeneous_C slotGrade (620496752 / 212837625 : ℚ)).mul (h0.pow 4)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (152085968 / 5457375 : ℚ)).mul (h0.pow 4)).mul (h1.pow 2))).add (((isWeightedHomogeneous_C slotGrade (10779136 / 383107725 : ℚ)).mul (h0.pow 3)).mul h3)).add ((((isWeightedHomogeneous_C slotGrade (46487872 / 49116375 : ℚ)).mul (h0.pow 3)).mul h1).mul h2)).add (((isWeightedHomogeneous_C slotGrade (655424 / 273375 : ℚ)).mul (h0.pow 3)).mul (h1.pow 3))).add (((isWeightedHomogeneous_C slotGrade (-170152 / 212837625 : ℚ)).mul (h0.pow 2)).mul h4)).add ((((isWeightedHomogeneous_C slotGrade (1084576 / 49116375 : ℚ)).mul (h0.pow 2)).mul h1).mul h3)).add (((isWeightedHomogeneous_C slotGrade (36256 / 4465125 : ℚ)).mul (h0.pow 2)).mul (h2.pow 2))).add ((((isWeightedHomogeneous_C slotGrade (23024 / 212625 : ℚ)).mul (h0.pow 2)).mul (h1.pow 2)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (4904 / 42525 : ℚ)).mul (h0.pow 2)).mul (h1.pow 4))).add (((isWeightedHomogeneous_C slotGrade (3712 / 70945875 : ℚ)).mul h0).mul h5)).add ((((isWeightedHomogeneous_C slotGrade (1648 / 2338875 : ℚ)).mul h0).mul h1).mul h4)).add ((((isWeightedHomogeneous_C slotGrade (5512 / 13395375 : ℚ)).mul h0).mul h2).mul h3)).add ((((isWeightedHomogeneous_C slotGrade (184 / 76545 : ℚ)).mul h0).mul (h1.pow 2)).mul h3)).add ((((isWeightedHomogeneous_C slotGrade (296 / 212625 : ℚ)).mul h0).mul h1).mul (h2.pow 2))).add ((((isWeightedHomogeneous_C slotGrade (2008 / 382725 : ℚ)).mul h0).mul (h1.pow 3)).mul h2)).add (((isWeightedHomogeneous_C slotGrade (32 / 10935 : ℚ)).mul h0).mul (h1.pow 5))).add ((isWeightedHomogeneous_C slotGrade (11056 / 1915538625 : ℚ)).mul h6)).add (((isWeightedHomogeneous_C slotGrade (32 / 1403325 : ℚ)).mul h1).mul h5)).add (((isWeightedHomogeneous_C slotGrade (2 / 212625 : ℚ)).mul h2).mul h4)).add (((isWeightedHomogeneous_C slotGrade (2 / 42525 : ℚ)).mul (h1.pow 2)).mul h4)).add ((isWeightedHomogeneous_C slotGrade (32 / 8037225 : ℚ)).mul (h3.pow 2))).add ((((isWeightedHomogeneous_C slotGrade (16 / 382725 : ℚ)).mul h1).mul h2).mul h3)).add (((isWeightedHomogeneous_C slotGrade (16 / 229635 : ℚ)).mul (h1.pow 3)).mul h3)).add ((isWeightedHomogeneous_C slotGrade (1 / 273375 : ℚ)).mul (h2.pow 3))).add (((isWeightedHomogeneous_C slotGrade (1 / 18225 : ℚ)).mul (h1.pow 2)).mul (h2.pow 2))).add (((isWeightedHomogeneous_C slotGrade (1 / 10935 : ℚ)).mul (h1.pow 4)).mul h2)).add ((isWeightedHomogeneous_C slotGrade (1 / 32805 : ℚ)).mul (h1.pow 6)))

theorem density_weighted (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14) :
    IsWeightedHomogeneous slotGrade (density n) n := by
  rcases hn with ⟨hlo, hhi⟩
  interval_cases n
  · exact (h0.pow 2).mul reduced2_weighted
  · exact (h0.pow 2).mul reduced3_weighted
  · exact (h0.pow 3).mul reduced4_weighted
  · exact (h0.pow 3).mul reduced5_weighted
  · exact (h0.pow 4).mul reduced6_weighted
  · exact (h0.pow 4).mul reduced7_weighted
  · exact (h0.pow 5).mul reduced8_weighted
  · exact (h0.pow 5).mul reduced9_weighted
  · exact (h0.pow 6).mul reduced10_weighted
  · exact (h0.pow 6).mul reduced11_weighted
  · exact (h0.pow 7).mul reduced12_weighted
  · exact (h0.pow 7).mul reduced13_weighted
  · exact (h0.pow 8).mul reduced14_weighted

theorem squareTerm_weighted (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14) :
    IsWeightedHomogeneous slotGrade (squareTerm n) n := by
  by_cases h13 : n = 13
  · subst n
    exact ((eta_weighted.pow 2).mul (h0.pow 7)).C_mul _
  by_cases h14 : n = 14
  · subst n
    exact ((eta_weighted.pow 2).mul (h0.pow 8)).C_mul _
  simp only [squareTerm, squareCoefficient, h13, h14, if_false, map_zero, zero_mul]
  exact isWeightedHomogeneous_zero _ _ _

theorem remainder_weighted (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14) :
    IsWeightedHomogeneous slotGrade (remainder n) n := by
  have he : remainder n = density n - C (scalarCoefficient n : ℚ) * u ^ n - squareTerm n := by
    rw [full_certificate n hn]
    ring
  rw [he]
  exact (weightedHomogeneousSubmodule ℚ slotGrade n).sub_mem
    ((weightedHomogeneousSubmodule ℚ slotGrade n).sub_mem (density_weighted n hn)
      (by simpa using (h0.pow n).C_mul (scalarCoefficient n : ℚ))) (squareTerm_weighted n hn)

end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
