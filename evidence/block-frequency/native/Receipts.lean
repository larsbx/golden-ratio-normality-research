import GoldenNormality

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace GoldenNormality.Receipts
def word_0 : List ℕ := []
theorem prefix_0_0 : PrefixCertificate (2^0) 0 := by decide
theorem digits_0 : DigitsAt 2 0 word_0 := True.intro
theorem count_0_0 : Blocks.count [0] word_0 = 0 := by decide
theorem actualCount_0_0 : Blocks.enumeratedCount [0]
    (actualDigits 2 0 word_0.length) = 0 :=
  certified_count_sound digits_0 count_0_0
theorem occurrence_0_0 : occurrences 2 1 0 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_0) (pattern := [0])
    (by decide) (by decide) (by decide) digits_0 count_0_0
theorem discrepancy_0_0 :
    Nat.dist (2^1 * occurrences 2 1 0 0) 0 = 0 := by
  rw [occurrence_0_0]
  decide
theorem count_0_1 : Blocks.count [1] word_0 = 0 := by decide
theorem actualCount_0_1 : Blocks.enumeratedCount [1]
    (actualDigits 2 0 word_0.length) = 0 :=
  certified_count_sound digits_0 count_0_1
theorem occurrence_0_1 : occurrences 2 1 1 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_0) (pattern := [1])
    (by decide) (by decide) (by decide) digits_0 count_0_1
theorem discrepancy_0_1 :
    Nat.dist (2^1 * occurrences 2 1 1 0) 0 = 0 := by
  rw [occurrence_0_1]
  decide

def word_1 : List ℕ := [6]
theorem prefix_1_0 : PrefixCertificate (10^0) 0 := by decide
theorem prefix_1_1 : PrefixCertificate (10^1) 6 := by decide
theorem digit_1_0 : digit 10 0 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_1_0 prefix_1_1
theorem digits_1 : DigitsAt 10 0 word_1 := And.intro digit_1_0 (True.intro)
theorem count_1_0 : Blocks.count [0, 0] word_1 = 0 := by decide
theorem actualCount_1_0 : Blocks.enumeratedCount [0, 0]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_0
theorem occurrence_1_0 : occurrences 10 2 0 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [0, 0])
    (by decide) (by decide) (by decide) digits_1 count_1_0
theorem discrepancy_1_0 :
    Nat.dist (10^2 * occurrences 10 2 0 0) 0 = 0 := by
  rw [occurrence_1_0]
  decide
theorem count_1_1 : Blocks.count [0, 1] word_1 = 0 := by decide
theorem actualCount_1_1 : Blocks.enumeratedCount [0, 1]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_1
theorem occurrence_1_1 : occurrences 10 2 1 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [0, 1])
    (by decide) (by decide) (by decide) digits_1 count_1_1
theorem discrepancy_1_1 :
    Nat.dist (10^2 * occurrences 10 2 1 0) 0 = 0 := by
  rw [occurrence_1_1]
  decide
theorem count_1_2 : Blocks.count [0, 2] word_1 = 0 := by decide
theorem actualCount_1_2 : Blocks.enumeratedCount [0, 2]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_2
theorem occurrence_1_2 : occurrences 10 2 2 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [0, 2])
    (by decide) (by decide) (by decide) digits_1 count_1_2
theorem discrepancy_1_2 :
    Nat.dist (10^2 * occurrences 10 2 2 0) 0 = 0 := by
  rw [occurrence_1_2]
  decide
theorem count_1_3 : Blocks.count [0, 3] word_1 = 0 := by decide
theorem actualCount_1_3 : Blocks.enumeratedCount [0, 3]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_3
theorem occurrence_1_3 : occurrences 10 2 3 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [0, 3])
    (by decide) (by decide) (by decide) digits_1 count_1_3
theorem discrepancy_1_3 :
    Nat.dist (10^2 * occurrences 10 2 3 0) 0 = 0 := by
  rw [occurrence_1_3]
  decide
theorem count_1_4 : Blocks.count [0, 4] word_1 = 0 := by decide
theorem actualCount_1_4 : Blocks.enumeratedCount [0, 4]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_4
theorem occurrence_1_4 : occurrences 10 2 4 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [0, 4])
    (by decide) (by decide) (by decide) digits_1 count_1_4
theorem discrepancy_1_4 :
    Nat.dist (10^2 * occurrences 10 2 4 0) 0 = 0 := by
  rw [occurrence_1_4]
  decide
theorem count_1_5 : Blocks.count [0, 5] word_1 = 0 := by decide
theorem actualCount_1_5 : Blocks.enumeratedCount [0, 5]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_5
theorem occurrence_1_5 : occurrences 10 2 5 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [0, 5])
    (by decide) (by decide) (by decide) digits_1 count_1_5
theorem discrepancy_1_5 :
    Nat.dist (10^2 * occurrences 10 2 5 0) 0 = 0 := by
  rw [occurrence_1_5]
  decide
theorem count_1_6 : Blocks.count [0, 6] word_1 = 0 := by decide
theorem actualCount_1_6 : Blocks.enumeratedCount [0, 6]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_6
theorem occurrence_1_6 : occurrences 10 2 6 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [0, 6])
    (by decide) (by decide) (by decide) digits_1 count_1_6
theorem discrepancy_1_6 :
    Nat.dist (10^2 * occurrences 10 2 6 0) 0 = 0 := by
  rw [occurrence_1_6]
  decide
theorem count_1_7 : Blocks.count [0, 7] word_1 = 0 := by decide
theorem actualCount_1_7 : Blocks.enumeratedCount [0, 7]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_7
theorem occurrence_1_7 : occurrences 10 2 7 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [0, 7])
    (by decide) (by decide) (by decide) digits_1 count_1_7
theorem discrepancy_1_7 :
    Nat.dist (10^2 * occurrences 10 2 7 0) 0 = 0 := by
  rw [occurrence_1_7]
  decide
theorem count_1_8 : Blocks.count [0, 8] word_1 = 0 := by decide
theorem actualCount_1_8 : Blocks.enumeratedCount [0, 8]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_8
theorem occurrence_1_8 : occurrences 10 2 8 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [0, 8])
    (by decide) (by decide) (by decide) digits_1 count_1_8
theorem discrepancy_1_8 :
    Nat.dist (10^2 * occurrences 10 2 8 0) 0 = 0 := by
  rw [occurrence_1_8]
  decide
theorem count_1_9 : Blocks.count [0, 9] word_1 = 0 := by decide
theorem actualCount_1_9 : Blocks.enumeratedCount [0, 9]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_9
theorem occurrence_1_9 : occurrences 10 2 9 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [0, 9])
    (by decide) (by decide) (by decide) digits_1 count_1_9
theorem discrepancy_1_9 :
    Nat.dist (10^2 * occurrences 10 2 9 0) 0 = 0 := by
  rw [occurrence_1_9]
  decide
theorem count_1_10 : Blocks.count [1, 0] word_1 = 0 := by decide
theorem actualCount_1_10 : Blocks.enumeratedCount [1, 0]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_10
theorem occurrence_1_10 : occurrences 10 2 10 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [1, 0])
    (by decide) (by decide) (by decide) digits_1 count_1_10
theorem discrepancy_1_10 :
    Nat.dist (10^2 * occurrences 10 2 10 0) 0 = 0 := by
  rw [occurrence_1_10]
  decide
theorem count_1_11 : Blocks.count [1, 1] word_1 = 0 := by decide
theorem actualCount_1_11 : Blocks.enumeratedCount [1, 1]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_11
theorem occurrence_1_11 : occurrences 10 2 11 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [1, 1])
    (by decide) (by decide) (by decide) digits_1 count_1_11
theorem discrepancy_1_11 :
    Nat.dist (10^2 * occurrences 10 2 11 0) 0 = 0 := by
  rw [occurrence_1_11]
  decide
theorem count_1_12 : Blocks.count [1, 2] word_1 = 0 := by decide
theorem actualCount_1_12 : Blocks.enumeratedCount [1, 2]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_12
theorem occurrence_1_12 : occurrences 10 2 12 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [1, 2])
    (by decide) (by decide) (by decide) digits_1 count_1_12
theorem discrepancy_1_12 :
    Nat.dist (10^2 * occurrences 10 2 12 0) 0 = 0 := by
  rw [occurrence_1_12]
  decide
theorem count_1_13 : Blocks.count [1, 3] word_1 = 0 := by decide
theorem actualCount_1_13 : Blocks.enumeratedCount [1, 3]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_13
theorem occurrence_1_13 : occurrences 10 2 13 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [1, 3])
    (by decide) (by decide) (by decide) digits_1 count_1_13
theorem discrepancy_1_13 :
    Nat.dist (10^2 * occurrences 10 2 13 0) 0 = 0 := by
  rw [occurrence_1_13]
  decide
theorem count_1_14 : Blocks.count [1, 4] word_1 = 0 := by decide
theorem actualCount_1_14 : Blocks.enumeratedCount [1, 4]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_14
theorem occurrence_1_14 : occurrences 10 2 14 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [1, 4])
    (by decide) (by decide) (by decide) digits_1 count_1_14
theorem discrepancy_1_14 :
    Nat.dist (10^2 * occurrences 10 2 14 0) 0 = 0 := by
  rw [occurrence_1_14]
  decide
theorem count_1_15 : Blocks.count [1, 5] word_1 = 0 := by decide
theorem actualCount_1_15 : Blocks.enumeratedCount [1, 5]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_15
theorem occurrence_1_15 : occurrences 10 2 15 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [1, 5])
    (by decide) (by decide) (by decide) digits_1 count_1_15
theorem discrepancy_1_15 :
    Nat.dist (10^2 * occurrences 10 2 15 0) 0 = 0 := by
  rw [occurrence_1_15]
  decide
theorem count_1_16 : Blocks.count [1, 6] word_1 = 0 := by decide
theorem actualCount_1_16 : Blocks.enumeratedCount [1, 6]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_16
theorem occurrence_1_16 : occurrences 10 2 16 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [1, 6])
    (by decide) (by decide) (by decide) digits_1 count_1_16
theorem discrepancy_1_16 :
    Nat.dist (10^2 * occurrences 10 2 16 0) 0 = 0 := by
  rw [occurrence_1_16]
  decide
theorem count_1_17 : Blocks.count [1, 7] word_1 = 0 := by decide
theorem actualCount_1_17 : Blocks.enumeratedCount [1, 7]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_17
theorem occurrence_1_17 : occurrences 10 2 17 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [1, 7])
    (by decide) (by decide) (by decide) digits_1 count_1_17
theorem discrepancy_1_17 :
    Nat.dist (10^2 * occurrences 10 2 17 0) 0 = 0 := by
  rw [occurrence_1_17]
  decide
theorem count_1_18 : Blocks.count [1, 8] word_1 = 0 := by decide
theorem actualCount_1_18 : Blocks.enumeratedCount [1, 8]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_18
theorem occurrence_1_18 : occurrences 10 2 18 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [1, 8])
    (by decide) (by decide) (by decide) digits_1 count_1_18
theorem discrepancy_1_18 :
    Nat.dist (10^2 * occurrences 10 2 18 0) 0 = 0 := by
  rw [occurrence_1_18]
  decide
theorem count_1_19 : Blocks.count [1, 9] word_1 = 0 := by decide
theorem actualCount_1_19 : Blocks.enumeratedCount [1, 9]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_19
theorem occurrence_1_19 : occurrences 10 2 19 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [1, 9])
    (by decide) (by decide) (by decide) digits_1 count_1_19
theorem discrepancy_1_19 :
    Nat.dist (10^2 * occurrences 10 2 19 0) 0 = 0 := by
  rw [occurrence_1_19]
  decide
theorem count_1_20 : Blocks.count [2, 0] word_1 = 0 := by decide
theorem actualCount_1_20 : Blocks.enumeratedCount [2, 0]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_20
theorem occurrence_1_20 : occurrences 10 2 20 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [2, 0])
    (by decide) (by decide) (by decide) digits_1 count_1_20
theorem discrepancy_1_20 :
    Nat.dist (10^2 * occurrences 10 2 20 0) 0 = 0 := by
  rw [occurrence_1_20]
  decide
theorem count_1_21 : Blocks.count [2, 1] word_1 = 0 := by decide
theorem actualCount_1_21 : Blocks.enumeratedCount [2, 1]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_21
theorem occurrence_1_21 : occurrences 10 2 21 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [2, 1])
    (by decide) (by decide) (by decide) digits_1 count_1_21
theorem discrepancy_1_21 :
    Nat.dist (10^2 * occurrences 10 2 21 0) 0 = 0 := by
  rw [occurrence_1_21]
  decide
theorem count_1_22 : Blocks.count [2, 2] word_1 = 0 := by decide
theorem actualCount_1_22 : Blocks.enumeratedCount [2, 2]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_22
theorem occurrence_1_22 : occurrences 10 2 22 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [2, 2])
    (by decide) (by decide) (by decide) digits_1 count_1_22
theorem discrepancy_1_22 :
    Nat.dist (10^2 * occurrences 10 2 22 0) 0 = 0 := by
  rw [occurrence_1_22]
  decide
theorem count_1_23 : Blocks.count [2, 3] word_1 = 0 := by decide
theorem actualCount_1_23 : Blocks.enumeratedCount [2, 3]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_23
theorem occurrence_1_23 : occurrences 10 2 23 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [2, 3])
    (by decide) (by decide) (by decide) digits_1 count_1_23
theorem discrepancy_1_23 :
    Nat.dist (10^2 * occurrences 10 2 23 0) 0 = 0 := by
  rw [occurrence_1_23]
  decide
theorem count_1_24 : Blocks.count [2, 4] word_1 = 0 := by decide
theorem actualCount_1_24 : Blocks.enumeratedCount [2, 4]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_24
theorem occurrence_1_24 : occurrences 10 2 24 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [2, 4])
    (by decide) (by decide) (by decide) digits_1 count_1_24
theorem discrepancy_1_24 :
    Nat.dist (10^2 * occurrences 10 2 24 0) 0 = 0 := by
  rw [occurrence_1_24]
  decide
theorem count_1_25 : Blocks.count [2, 5] word_1 = 0 := by decide
theorem actualCount_1_25 : Blocks.enumeratedCount [2, 5]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_25
theorem occurrence_1_25 : occurrences 10 2 25 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [2, 5])
    (by decide) (by decide) (by decide) digits_1 count_1_25
theorem discrepancy_1_25 :
    Nat.dist (10^2 * occurrences 10 2 25 0) 0 = 0 := by
  rw [occurrence_1_25]
  decide
theorem count_1_26 : Blocks.count [2, 6] word_1 = 0 := by decide
theorem actualCount_1_26 : Blocks.enumeratedCount [2, 6]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_26
theorem occurrence_1_26 : occurrences 10 2 26 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [2, 6])
    (by decide) (by decide) (by decide) digits_1 count_1_26
theorem discrepancy_1_26 :
    Nat.dist (10^2 * occurrences 10 2 26 0) 0 = 0 := by
  rw [occurrence_1_26]
  decide
theorem count_1_27 : Blocks.count [2, 7] word_1 = 0 := by decide
theorem actualCount_1_27 : Blocks.enumeratedCount [2, 7]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_27
theorem occurrence_1_27 : occurrences 10 2 27 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [2, 7])
    (by decide) (by decide) (by decide) digits_1 count_1_27
theorem discrepancy_1_27 :
    Nat.dist (10^2 * occurrences 10 2 27 0) 0 = 0 := by
  rw [occurrence_1_27]
  decide
theorem count_1_28 : Blocks.count [2, 8] word_1 = 0 := by decide
theorem actualCount_1_28 : Blocks.enumeratedCount [2, 8]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_28
theorem occurrence_1_28 : occurrences 10 2 28 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [2, 8])
    (by decide) (by decide) (by decide) digits_1 count_1_28
theorem discrepancy_1_28 :
    Nat.dist (10^2 * occurrences 10 2 28 0) 0 = 0 := by
  rw [occurrence_1_28]
  decide
theorem count_1_29 : Blocks.count [2, 9] word_1 = 0 := by decide
theorem actualCount_1_29 : Blocks.enumeratedCount [2, 9]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_29
theorem occurrence_1_29 : occurrences 10 2 29 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [2, 9])
    (by decide) (by decide) (by decide) digits_1 count_1_29
theorem discrepancy_1_29 :
    Nat.dist (10^2 * occurrences 10 2 29 0) 0 = 0 := by
  rw [occurrence_1_29]
  decide
theorem count_1_30 : Blocks.count [3, 0] word_1 = 0 := by decide
theorem actualCount_1_30 : Blocks.enumeratedCount [3, 0]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_30
theorem occurrence_1_30 : occurrences 10 2 30 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [3, 0])
    (by decide) (by decide) (by decide) digits_1 count_1_30
theorem discrepancy_1_30 :
    Nat.dist (10^2 * occurrences 10 2 30 0) 0 = 0 := by
  rw [occurrence_1_30]
  decide
theorem count_1_31 : Blocks.count [3, 1] word_1 = 0 := by decide
theorem actualCount_1_31 : Blocks.enumeratedCount [3, 1]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_31
theorem occurrence_1_31 : occurrences 10 2 31 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [3, 1])
    (by decide) (by decide) (by decide) digits_1 count_1_31
theorem discrepancy_1_31 :
    Nat.dist (10^2 * occurrences 10 2 31 0) 0 = 0 := by
  rw [occurrence_1_31]
  decide
theorem count_1_32 : Blocks.count [3, 2] word_1 = 0 := by decide
theorem actualCount_1_32 : Blocks.enumeratedCount [3, 2]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_32
theorem occurrence_1_32 : occurrences 10 2 32 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [3, 2])
    (by decide) (by decide) (by decide) digits_1 count_1_32
theorem discrepancy_1_32 :
    Nat.dist (10^2 * occurrences 10 2 32 0) 0 = 0 := by
  rw [occurrence_1_32]
  decide
theorem count_1_33 : Blocks.count [3, 3] word_1 = 0 := by decide
theorem actualCount_1_33 : Blocks.enumeratedCount [3, 3]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_33
theorem occurrence_1_33 : occurrences 10 2 33 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [3, 3])
    (by decide) (by decide) (by decide) digits_1 count_1_33
theorem discrepancy_1_33 :
    Nat.dist (10^2 * occurrences 10 2 33 0) 0 = 0 := by
  rw [occurrence_1_33]
  decide
theorem count_1_34 : Blocks.count [3, 4] word_1 = 0 := by decide
theorem actualCount_1_34 : Blocks.enumeratedCount [3, 4]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_34
theorem occurrence_1_34 : occurrences 10 2 34 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [3, 4])
    (by decide) (by decide) (by decide) digits_1 count_1_34
theorem discrepancy_1_34 :
    Nat.dist (10^2 * occurrences 10 2 34 0) 0 = 0 := by
  rw [occurrence_1_34]
  decide
theorem count_1_35 : Blocks.count [3, 5] word_1 = 0 := by decide
theorem actualCount_1_35 : Blocks.enumeratedCount [3, 5]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_35
theorem occurrence_1_35 : occurrences 10 2 35 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [3, 5])
    (by decide) (by decide) (by decide) digits_1 count_1_35
theorem discrepancy_1_35 :
    Nat.dist (10^2 * occurrences 10 2 35 0) 0 = 0 := by
  rw [occurrence_1_35]
  decide
theorem count_1_36 : Blocks.count [3, 6] word_1 = 0 := by decide
theorem actualCount_1_36 : Blocks.enumeratedCount [3, 6]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_36
theorem occurrence_1_36 : occurrences 10 2 36 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [3, 6])
    (by decide) (by decide) (by decide) digits_1 count_1_36
theorem discrepancy_1_36 :
    Nat.dist (10^2 * occurrences 10 2 36 0) 0 = 0 := by
  rw [occurrence_1_36]
  decide
theorem count_1_37 : Blocks.count [3, 7] word_1 = 0 := by decide
theorem actualCount_1_37 : Blocks.enumeratedCount [3, 7]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_37
theorem occurrence_1_37 : occurrences 10 2 37 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [3, 7])
    (by decide) (by decide) (by decide) digits_1 count_1_37
theorem discrepancy_1_37 :
    Nat.dist (10^2 * occurrences 10 2 37 0) 0 = 0 := by
  rw [occurrence_1_37]
  decide
theorem count_1_38 : Blocks.count [3, 8] word_1 = 0 := by decide
theorem actualCount_1_38 : Blocks.enumeratedCount [3, 8]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_38
theorem occurrence_1_38 : occurrences 10 2 38 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [3, 8])
    (by decide) (by decide) (by decide) digits_1 count_1_38
theorem discrepancy_1_38 :
    Nat.dist (10^2 * occurrences 10 2 38 0) 0 = 0 := by
  rw [occurrence_1_38]
  decide
theorem count_1_39 : Blocks.count [3, 9] word_1 = 0 := by decide
theorem actualCount_1_39 : Blocks.enumeratedCount [3, 9]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_39
theorem occurrence_1_39 : occurrences 10 2 39 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [3, 9])
    (by decide) (by decide) (by decide) digits_1 count_1_39
theorem discrepancy_1_39 :
    Nat.dist (10^2 * occurrences 10 2 39 0) 0 = 0 := by
  rw [occurrence_1_39]
  decide
theorem count_1_40 : Blocks.count [4, 0] word_1 = 0 := by decide
theorem actualCount_1_40 : Blocks.enumeratedCount [4, 0]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_40
theorem occurrence_1_40 : occurrences 10 2 40 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [4, 0])
    (by decide) (by decide) (by decide) digits_1 count_1_40
theorem discrepancy_1_40 :
    Nat.dist (10^2 * occurrences 10 2 40 0) 0 = 0 := by
  rw [occurrence_1_40]
  decide
theorem count_1_41 : Blocks.count [4, 1] word_1 = 0 := by decide
theorem actualCount_1_41 : Blocks.enumeratedCount [4, 1]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_41
theorem occurrence_1_41 : occurrences 10 2 41 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [4, 1])
    (by decide) (by decide) (by decide) digits_1 count_1_41
theorem discrepancy_1_41 :
    Nat.dist (10^2 * occurrences 10 2 41 0) 0 = 0 := by
  rw [occurrence_1_41]
  decide
theorem count_1_42 : Blocks.count [4, 2] word_1 = 0 := by decide
theorem actualCount_1_42 : Blocks.enumeratedCount [4, 2]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_42
theorem occurrence_1_42 : occurrences 10 2 42 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [4, 2])
    (by decide) (by decide) (by decide) digits_1 count_1_42
theorem discrepancy_1_42 :
    Nat.dist (10^2 * occurrences 10 2 42 0) 0 = 0 := by
  rw [occurrence_1_42]
  decide
theorem count_1_43 : Blocks.count [4, 3] word_1 = 0 := by decide
theorem actualCount_1_43 : Blocks.enumeratedCount [4, 3]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_43
theorem occurrence_1_43 : occurrences 10 2 43 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [4, 3])
    (by decide) (by decide) (by decide) digits_1 count_1_43
theorem discrepancy_1_43 :
    Nat.dist (10^2 * occurrences 10 2 43 0) 0 = 0 := by
  rw [occurrence_1_43]
  decide
theorem count_1_44 : Blocks.count [4, 4] word_1 = 0 := by decide
theorem actualCount_1_44 : Blocks.enumeratedCount [4, 4]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_44
theorem occurrence_1_44 : occurrences 10 2 44 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [4, 4])
    (by decide) (by decide) (by decide) digits_1 count_1_44
theorem discrepancy_1_44 :
    Nat.dist (10^2 * occurrences 10 2 44 0) 0 = 0 := by
  rw [occurrence_1_44]
  decide
theorem count_1_45 : Blocks.count [4, 5] word_1 = 0 := by decide
theorem actualCount_1_45 : Blocks.enumeratedCount [4, 5]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_45
theorem occurrence_1_45 : occurrences 10 2 45 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [4, 5])
    (by decide) (by decide) (by decide) digits_1 count_1_45
theorem discrepancy_1_45 :
    Nat.dist (10^2 * occurrences 10 2 45 0) 0 = 0 := by
  rw [occurrence_1_45]
  decide
theorem count_1_46 : Blocks.count [4, 6] word_1 = 0 := by decide
theorem actualCount_1_46 : Blocks.enumeratedCount [4, 6]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_46
theorem occurrence_1_46 : occurrences 10 2 46 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [4, 6])
    (by decide) (by decide) (by decide) digits_1 count_1_46
theorem discrepancy_1_46 :
    Nat.dist (10^2 * occurrences 10 2 46 0) 0 = 0 := by
  rw [occurrence_1_46]
  decide
theorem count_1_47 : Blocks.count [4, 7] word_1 = 0 := by decide
theorem actualCount_1_47 : Blocks.enumeratedCount [4, 7]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_47
theorem occurrence_1_47 : occurrences 10 2 47 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [4, 7])
    (by decide) (by decide) (by decide) digits_1 count_1_47
theorem discrepancy_1_47 :
    Nat.dist (10^2 * occurrences 10 2 47 0) 0 = 0 := by
  rw [occurrence_1_47]
  decide
theorem count_1_48 : Blocks.count [4, 8] word_1 = 0 := by decide
theorem actualCount_1_48 : Blocks.enumeratedCount [4, 8]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_48
theorem occurrence_1_48 : occurrences 10 2 48 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [4, 8])
    (by decide) (by decide) (by decide) digits_1 count_1_48
theorem discrepancy_1_48 :
    Nat.dist (10^2 * occurrences 10 2 48 0) 0 = 0 := by
  rw [occurrence_1_48]
  decide
theorem count_1_49 : Blocks.count [4, 9] word_1 = 0 := by decide
theorem actualCount_1_49 : Blocks.enumeratedCount [4, 9]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_49
theorem occurrence_1_49 : occurrences 10 2 49 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [4, 9])
    (by decide) (by decide) (by decide) digits_1 count_1_49
theorem discrepancy_1_49 :
    Nat.dist (10^2 * occurrences 10 2 49 0) 0 = 0 := by
  rw [occurrence_1_49]
  decide
theorem count_1_50 : Blocks.count [5, 0] word_1 = 0 := by decide
theorem actualCount_1_50 : Blocks.enumeratedCount [5, 0]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_50
theorem occurrence_1_50 : occurrences 10 2 50 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [5, 0])
    (by decide) (by decide) (by decide) digits_1 count_1_50
theorem discrepancy_1_50 :
    Nat.dist (10^2 * occurrences 10 2 50 0) 0 = 0 := by
  rw [occurrence_1_50]
  decide
theorem count_1_51 : Blocks.count [5, 1] word_1 = 0 := by decide
theorem actualCount_1_51 : Blocks.enumeratedCount [5, 1]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_51
theorem occurrence_1_51 : occurrences 10 2 51 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [5, 1])
    (by decide) (by decide) (by decide) digits_1 count_1_51
theorem discrepancy_1_51 :
    Nat.dist (10^2 * occurrences 10 2 51 0) 0 = 0 := by
  rw [occurrence_1_51]
  decide
theorem count_1_52 : Blocks.count [5, 2] word_1 = 0 := by decide
theorem actualCount_1_52 : Blocks.enumeratedCount [5, 2]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_52
theorem occurrence_1_52 : occurrences 10 2 52 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [5, 2])
    (by decide) (by decide) (by decide) digits_1 count_1_52
theorem discrepancy_1_52 :
    Nat.dist (10^2 * occurrences 10 2 52 0) 0 = 0 := by
  rw [occurrence_1_52]
  decide
theorem count_1_53 : Blocks.count [5, 3] word_1 = 0 := by decide
theorem actualCount_1_53 : Blocks.enumeratedCount [5, 3]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_53
theorem occurrence_1_53 : occurrences 10 2 53 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [5, 3])
    (by decide) (by decide) (by decide) digits_1 count_1_53
theorem discrepancy_1_53 :
    Nat.dist (10^2 * occurrences 10 2 53 0) 0 = 0 := by
  rw [occurrence_1_53]
  decide
theorem count_1_54 : Blocks.count [5, 4] word_1 = 0 := by decide
theorem actualCount_1_54 : Blocks.enumeratedCount [5, 4]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_54
theorem occurrence_1_54 : occurrences 10 2 54 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [5, 4])
    (by decide) (by decide) (by decide) digits_1 count_1_54
theorem discrepancy_1_54 :
    Nat.dist (10^2 * occurrences 10 2 54 0) 0 = 0 := by
  rw [occurrence_1_54]
  decide
theorem count_1_55 : Blocks.count [5, 5] word_1 = 0 := by decide
theorem actualCount_1_55 : Blocks.enumeratedCount [5, 5]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_55
theorem occurrence_1_55 : occurrences 10 2 55 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [5, 5])
    (by decide) (by decide) (by decide) digits_1 count_1_55
theorem discrepancy_1_55 :
    Nat.dist (10^2 * occurrences 10 2 55 0) 0 = 0 := by
  rw [occurrence_1_55]
  decide
theorem count_1_56 : Blocks.count [5, 6] word_1 = 0 := by decide
theorem actualCount_1_56 : Blocks.enumeratedCount [5, 6]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_56
theorem occurrence_1_56 : occurrences 10 2 56 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [5, 6])
    (by decide) (by decide) (by decide) digits_1 count_1_56
theorem discrepancy_1_56 :
    Nat.dist (10^2 * occurrences 10 2 56 0) 0 = 0 := by
  rw [occurrence_1_56]
  decide
theorem count_1_57 : Blocks.count [5, 7] word_1 = 0 := by decide
theorem actualCount_1_57 : Blocks.enumeratedCount [5, 7]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_57
theorem occurrence_1_57 : occurrences 10 2 57 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [5, 7])
    (by decide) (by decide) (by decide) digits_1 count_1_57
theorem discrepancy_1_57 :
    Nat.dist (10^2 * occurrences 10 2 57 0) 0 = 0 := by
  rw [occurrence_1_57]
  decide
theorem count_1_58 : Blocks.count [5, 8] word_1 = 0 := by decide
theorem actualCount_1_58 : Blocks.enumeratedCount [5, 8]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_58
theorem occurrence_1_58 : occurrences 10 2 58 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [5, 8])
    (by decide) (by decide) (by decide) digits_1 count_1_58
theorem discrepancy_1_58 :
    Nat.dist (10^2 * occurrences 10 2 58 0) 0 = 0 := by
  rw [occurrence_1_58]
  decide
theorem count_1_59 : Blocks.count [5, 9] word_1 = 0 := by decide
theorem actualCount_1_59 : Blocks.enumeratedCount [5, 9]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_59
theorem occurrence_1_59 : occurrences 10 2 59 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [5, 9])
    (by decide) (by decide) (by decide) digits_1 count_1_59
theorem discrepancy_1_59 :
    Nat.dist (10^2 * occurrences 10 2 59 0) 0 = 0 := by
  rw [occurrence_1_59]
  decide
theorem count_1_60 : Blocks.count [6, 0] word_1 = 0 := by decide
theorem actualCount_1_60 : Blocks.enumeratedCount [6, 0]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_60
theorem occurrence_1_60 : occurrences 10 2 60 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [6, 0])
    (by decide) (by decide) (by decide) digits_1 count_1_60
theorem discrepancy_1_60 :
    Nat.dist (10^2 * occurrences 10 2 60 0) 0 = 0 := by
  rw [occurrence_1_60]
  decide
theorem count_1_61 : Blocks.count [6, 1] word_1 = 0 := by decide
theorem actualCount_1_61 : Blocks.enumeratedCount [6, 1]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_61
theorem occurrence_1_61 : occurrences 10 2 61 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [6, 1])
    (by decide) (by decide) (by decide) digits_1 count_1_61
theorem discrepancy_1_61 :
    Nat.dist (10^2 * occurrences 10 2 61 0) 0 = 0 := by
  rw [occurrence_1_61]
  decide
theorem count_1_62 : Blocks.count [6, 2] word_1 = 0 := by decide
theorem actualCount_1_62 : Blocks.enumeratedCount [6, 2]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_62
theorem occurrence_1_62 : occurrences 10 2 62 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [6, 2])
    (by decide) (by decide) (by decide) digits_1 count_1_62
theorem discrepancy_1_62 :
    Nat.dist (10^2 * occurrences 10 2 62 0) 0 = 0 := by
  rw [occurrence_1_62]
  decide
theorem count_1_63 : Blocks.count [6, 3] word_1 = 0 := by decide
theorem actualCount_1_63 : Blocks.enumeratedCount [6, 3]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_63
theorem occurrence_1_63 : occurrences 10 2 63 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [6, 3])
    (by decide) (by decide) (by decide) digits_1 count_1_63
theorem discrepancy_1_63 :
    Nat.dist (10^2 * occurrences 10 2 63 0) 0 = 0 := by
  rw [occurrence_1_63]
  decide
theorem count_1_64 : Blocks.count [6, 4] word_1 = 0 := by decide
theorem actualCount_1_64 : Blocks.enumeratedCount [6, 4]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_64
theorem occurrence_1_64 : occurrences 10 2 64 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [6, 4])
    (by decide) (by decide) (by decide) digits_1 count_1_64
theorem discrepancy_1_64 :
    Nat.dist (10^2 * occurrences 10 2 64 0) 0 = 0 := by
  rw [occurrence_1_64]
  decide
theorem count_1_65 : Blocks.count [6, 5] word_1 = 0 := by decide
theorem actualCount_1_65 : Blocks.enumeratedCount [6, 5]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_65
theorem occurrence_1_65 : occurrences 10 2 65 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [6, 5])
    (by decide) (by decide) (by decide) digits_1 count_1_65
theorem discrepancy_1_65 :
    Nat.dist (10^2 * occurrences 10 2 65 0) 0 = 0 := by
  rw [occurrence_1_65]
  decide
theorem count_1_66 : Blocks.count [6, 6] word_1 = 0 := by decide
theorem actualCount_1_66 : Blocks.enumeratedCount [6, 6]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_66
theorem occurrence_1_66 : occurrences 10 2 66 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [6, 6])
    (by decide) (by decide) (by decide) digits_1 count_1_66
theorem discrepancy_1_66 :
    Nat.dist (10^2 * occurrences 10 2 66 0) 0 = 0 := by
  rw [occurrence_1_66]
  decide
theorem count_1_67 : Blocks.count [6, 7] word_1 = 0 := by decide
theorem actualCount_1_67 : Blocks.enumeratedCount [6, 7]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_67
theorem occurrence_1_67 : occurrences 10 2 67 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [6, 7])
    (by decide) (by decide) (by decide) digits_1 count_1_67
theorem discrepancy_1_67 :
    Nat.dist (10^2 * occurrences 10 2 67 0) 0 = 0 := by
  rw [occurrence_1_67]
  decide
theorem count_1_68 : Blocks.count [6, 8] word_1 = 0 := by decide
theorem actualCount_1_68 : Blocks.enumeratedCount [6, 8]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_68
theorem occurrence_1_68 : occurrences 10 2 68 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [6, 8])
    (by decide) (by decide) (by decide) digits_1 count_1_68
theorem discrepancy_1_68 :
    Nat.dist (10^2 * occurrences 10 2 68 0) 0 = 0 := by
  rw [occurrence_1_68]
  decide
theorem count_1_69 : Blocks.count [6, 9] word_1 = 0 := by decide
theorem actualCount_1_69 : Blocks.enumeratedCount [6, 9]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_69
theorem occurrence_1_69 : occurrences 10 2 69 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [6, 9])
    (by decide) (by decide) (by decide) digits_1 count_1_69
theorem discrepancy_1_69 :
    Nat.dist (10^2 * occurrences 10 2 69 0) 0 = 0 := by
  rw [occurrence_1_69]
  decide
theorem count_1_70 : Blocks.count [7, 0] word_1 = 0 := by decide
theorem actualCount_1_70 : Blocks.enumeratedCount [7, 0]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_70
theorem occurrence_1_70 : occurrences 10 2 70 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [7, 0])
    (by decide) (by decide) (by decide) digits_1 count_1_70
theorem discrepancy_1_70 :
    Nat.dist (10^2 * occurrences 10 2 70 0) 0 = 0 := by
  rw [occurrence_1_70]
  decide
theorem count_1_71 : Blocks.count [7, 1] word_1 = 0 := by decide
theorem actualCount_1_71 : Blocks.enumeratedCount [7, 1]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_71
theorem occurrence_1_71 : occurrences 10 2 71 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [7, 1])
    (by decide) (by decide) (by decide) digits_1 count_1_71
theorem discrepancy_1_71 :
    Nat.dist (10^2 * occurrences 10 2 71 0) 0 = 0 := by
  rw [occurrence_1_71]
  decide
theorem count_1_72 : Blocks.count [7, 2] word_1 = 0 := by decide
theorem actualCount_1_72 : Blocks.enumeratedCount [7, 2]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_72
theorem occurrence_1_72 : occurrences 10 2 72 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [7, 2])
    (by decide) (by decide) (by decide) digits_1 count_1_72
theorem discrepancy_1_72 :
    Nat.dist (10^2 * occurrences 10 2 72 0) 0 = 0 := by
  rw [occurrence_1_72]
  decide
theorem count_1_73 : Blocks.count [7, 3] word_1 = 0 := by decide
theorem actualCount_1_73 : Blocks.enumeratedCount [7, 3]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_73
theorem occurrence_1_73 : occurrences 10 2 73 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [7, 3])
    (by decide) (by decide) (by decide) digits_1 count_1_73
theorem discrepancy_1_73 :
    Nat.dist (10^2 * occurrences 10 2 73 0) 0 = 0 := by
  rw [occurrence_1_73]
  decide
theorem count_1_74 : Blocks.count [7, 4] word_1 = 0 := by decide
theorem actualCount_1_74 : Blocks.enumeratedCount [7, 4]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_74
theorem occurrence_1_74 : occurrences 10 2 74 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [7, 4])
    (by decide) (by decide) (by decide) digits_1 count_1_74
theorem discrepancy_1_74 :
    Nat.dist (10^2 * occurrences 10 2 74 0) 0 = 0 := by
  rw [occurrence_1_74]
  decide
theorem count_1_75 : Blocks.count [7, 5] word_1 = 0 := by decide
theorem actualCount_1_75 : Blocks.enumeratedCount [7, 5]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_75
theorem occurrence_1_75 : occurrences 10 2 75 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [7, 5])
    (by decide) (by decide) (by decide) digits_1 count_1_75
theorem discrepancy_1_75 :
    Nat.dist (10^2 * occurrences 10 2 75 0) 0 = 0 := by
  rw [occurrence_1_75]
  decide
theorem count_1_76 : Blocks.count [7, 6] word_1 = 0 := by decide
theorem actualCount_1_76 : Blocks.enumeratedCount [7, 6]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_76
theorem occurrence_1_76 : occurrences 10 2 76 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [7, 6])
    (by decide) (by decide) (by decide) digits_1 count_1_76
theorem discrepancy_1_76 :
    Nat.dist (10^2 * occurrences 10 2 76 0) 0 = 0 := by
  rw [occurrence_1_76]
  decide
theorem count_1_77 : Blocks.count [7, 7] word_1 = 0 := by decide
theorem actualCount_1_77 : Blocks.enumeratedCount [7, 7]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_77
theorem occurrence_1_77 : occurrences 10 2 77 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [7, 7])
    (by decide) (by decide) (by decide) digits_1 count_1_77
theorem discrepancy_1_77 :
    Nat.dist (10^2 * occurrences 10 2 77 0) 0 = 0 := by
  rw [occurrence_1_77]
  decide
theorem count_1_78 : Blocks.count [7, 8] word_1 = 0 := by decide
theorem actualCount_1_78 : Blocks.enumeratedCount [7, 8]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_78
theorem occurrence_1_78 : occurrences 10 2 78 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [7, 8])
    (by decide) (by decide) (by decide) digits_1 count_1_78
theorem discrepancy_1_78 :
    Nat.dist (10^2 * occurrences 10 2 78 0) 0 = 0 := by
  rw [occurrence_1_78]
  decide
theorem count_1_79 : Blocks.count [7, 9] word_1 = 0 := by decide
theorem actualCount_1_79 : Blocks.enumeratedCount [7, 9]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_79
theorem occurrence_1_79 : occurrences 10 2 79 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [7, 9])
    (by decide) (by decide) (by decide) digits_1 count_1_79
theorem discrepancy_1_79 :
    Nat.dist (10^2 * occurrences 10 2 79 0) 0 = 0 := by
  rw [occurrence_1_79]
  decide
theorem count_1_80 : Blocks.count [8, 0] word_1 = 0 := by decide
theorem actualCount_1_80 : Blocks.enumeratedCount [8, 0]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_80
theorem occurrence_1_80 : occurrences 10 2 80 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [8, 0])
    (by decide) (by decide) (by decide) digits_1 count_1_80
theorem discrepancy_1_80 :
    Nat.dist (10^2 * occurrences 10 2 80 0) 0 = 0 := by
  rw [occurrence_1_80]
  decide
theorem count_1_81 : Blocks.count [8, 1] word_1 = 0 := by decide
theorem actualCount_1_81 : Blocks.enumeratedCount [8, 1]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_81
theorem occurrence_1_81 : occurrences 10 2 81 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [8, 1])
    (by decide) (by decide) (by decide) digits_1 count_1_81
theorem discrepancy_1_81 :
    Nat.dist (10^2 * occurrences 10 2 81 0) 0 = 0 := by
  rw [occurrence_1_81]
  decide
theorem count_1_82 : Blocks.count [8, 2] word_1 = 0 := by decide
theorem actualCount_1_82 : Blocks.enumeratedCount [8, 2]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_82
theorem occurrence_1_82 : occurrences 10 2 82 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [8, 2])
    (by decide) (by decide) (by decide) digits_1 count_1_82
theorem discrepancy_1_82 :
    Nat.dist (10^2 * occurrences 10 2 82 0) 0 = 0 := by
  rw [occurrence_1_82]
  decide
theorem count_1_83 : Blocks.count [8, 3] word_1 = 0 := by decide
theorem actualCount_1_83 : Blocks.enumeratedCount [8, 3]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_83
theorem occurrence_1_83 : occurrences 10 2 83 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [8, 3])
    (by decide) (by decide) (by decide) digits_1 count_1_83
theorem discrepancy_1_83 :
    Nat.dist (10^2 * occurrences 10 2 83 0) 0 = 0 := by
  rw [occurrence_1_83]
  decide
theorem count_1_84 : Blocks.count [8, 4] word_1 = 0 := by decide
theorem actualCount_1_84 : Blocks.enumeratedCount [8, 4]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_84
theorem occurrence_1_84 : occurrences 10 2 84 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [8, 4])
    (by decide) (by decide) (by decide) digits_1 count_1_84
theorem discrepancy_1_84 :
    Nat.dist (10^2 * occurrences 10 2 84 0) 0 = 0 := by
  rw [occurrence_1_84]
  decide
theorem count_1_85 : Blocks.count [8, 5] word_1 = 0 := by decide
theorem actualCount_1_85 : Blocks.enumeratedCount [8, 5]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_85
theorem occurrence_1_85 : occurrences 10 2 85 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [8, 5])
    (by decide) (by decide) (by decide) digits_1 count_1_85
theorem discrepancy_1_85 :
    Nat.dist (10^2 * occurrences 10 2 85 0) 0 = 0 := by
  rw [occurrence_1_85]
  decide
theorem count_1_86 : Blocks.count [8, 6] word_1 = 0 := by decide
theorem actualCount_1_86 : Blocks.enumeratedCount [8, 6]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_86
theorem occurrence_1_86 : occurrences 10 2 86 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [8, 6])
    (by decide) (by decide) (by decide) digits_1 count_1_86
theorem discrepancy_1_86 :
    Nat.dist (10^2 * occurrences 10 2 86 0) 0 = 0 := by
  rw [occurrence_1_86]
  decide
theorem count_1_87 : Blocks.count [8, 7] word_1 = 0 := by decide
theorem actualCount_1_87 : Blocks.enumeratedCount [8, 7]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_87
theorem occurrence_1_87 : occurrences 10 2 87 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [8, 7])
    (by decide) (by decide) (by decide) digits_1 count_1_87
theorem discrepancy_1_87 :
    Nat.dist (10^2 * occurrences 10 2 87 0) 0 = 0 := by
  rw [occurrence_1_87]
  decide
theorem count_1_88 : Blocks.count [8, 8] word_1 = 0 := by decide
theorem actualCount_1_88 : Blocks.enumeratedCount [8, 8]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_88
theorem occurrence_1_88 : occurrences 10 2 88 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [8, 8])
    (by decide) (by decide) (by decide) digits_1 count_1_88
theorem discrepancy_1_88 :
    Nat.dist (10^2 * occurrences 10 2 88 0) 0 = 0 := by
  rw [occurrence_1_88]
  decide
theorem count_1_89 : Blocks.count [8, 9] word_1 = 0 := by decide
theorem actualCount_1_89 : Blocks.enumeratedCount [8, 9]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_89
theorem occurrence_1_89 : occurrences 10 2 89 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [8, 9])
    (by decide) (by decide) (by decide) digits_1 count_1_89
theorem discrepancy_1_89 :
    Nat.dist (10^2 * occurrences 10 2 89 0) 0 = 0 := by
  rw [occurrence_1_89]
  decide
theorem count_1_90 : Blocks.count [9, 0] word_1 = 0 := by decide
theorem actualCount_1_90 : Blocks.enumeratedCount [9, 0]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_90
theorem occurrence_1_90 : occurrences 10 2 90 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [9, 0])
    (by decide) (by decide) (by decide) digits_1 count_1_90
theorem discrepancy_1_90 :
    Nat.dist (10^2 * occurrences 10 2 90 0) 0 = 0 := by
  rw [occurrence_1_90]
  decide
theorem count_1_91 : Blocks.count [9, 1] word_1 = 0 := by decide
theorem actualCount_1_91 : Blocks.enumeratedCount [9, 1]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_91
theorem occurrence_1_91 : occurrences 10 2 91 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [9, 1])
    (by decide) (by decide) (by decide) digits_1 count_1_91
theorem discrepancy_1_91 :
    Nat.dist (10^2 * occurrences 10 2 91 0) 0 = 0 := by
  rw [occurrence_1_91]
  decide
theorem count_1_92 : Blocks.count [9, 2] word_1 = 0 := by decide
theorem actualCount_1_92 : Blocks.enumeratedCount [9, 2]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_92
theorem occurrence_1_92 : occurrences 10 2 92 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [9, 2])
    (by decide) (by decide) (by decide) digits_1 count_1_92
theorem discrepancy_1_92 :
    Nat.dist (10^2 * occurrences 10 2 92 0) 0 = 0 := by
  rw [occurrence_1_92]
  decide
theorem count_1_93 : Blocks.count [9, 3] word_1 = 0 := by decide
theorem actualCount_1_93 : Blocks.enumeratedCount [9, 3]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_93
theorem occurrence_1_93 : occurrences 10 2 93 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [9, 3])
    (by decide) (by decide) (by decide) digits_1 count_1_93
theorem discrepancy_1_93 :
    Nat.dist (10^2 * occurrences 10 2 93 0) 0 = 0 := by
  rw [occurrence_1_93]
  decide
theorem count_1_94 : Blocks.count [9, 4] word_1 = 0 := by decide
theorem actualCount_1_94 : Blocks.enumeratedCount [9, 4]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_94
theorem occurrence_1_94 : occurrences 10 2 94 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [9, 4])
    (by decide) (by decide) (by decide) digits_1 count_1_94
theorem discrepancy_1_94 :
    Nat.dist (10^2 * occurrences 10 2 94 0) 0 = 0 := by
  rw [occurrence_1_94]
  decide
theorem count_1_95 : Blocks.count [9, 5] word_1 = 0 := by decide
theorem actualCount_1_95 : Blocks.enumeratedCount [9, 5]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_95
theorem occurrence_1_95 : occurrences 10 2 95 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [9, 5])
    (by decide) (by decide) (by decide) digits_1 count_1_95
theorem discrepancy_1_95 :
    Nat.dist (10^2 * occurrences 10 2 95 0) 0 = 0 := by
  rw [occurrence_1_95]
  decide
theorem count_1_96 : Blocks.count [9, 6] word_1 = 0 := by decide
theorem actualCount_1_96 : Blocks.enumeratedCount [9, 6]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_96
theorem occurrence_1_96 : occurrences 10 2 96 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [9, 6])
    (by decide) (by decide) (by decide) digits_1 count_1_96
theorem discrepancy_1_96 :
    Nat.dist (10^2 * occurrences 10 2 96 0) 0 = 0 := by
  rw [occurrence_1_96]
  decide
theorem count_1_97 : Blocks.count [9, 7] word_1 = 0 := by decide
theorem actualCount_1_97 : Blocks.enumeratedCount [9, 7]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_97
theorem occurrence_1_97 : occurrences 10 2 97 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [9, 7])
    (by decide) (by decide) (by decide) digits_1 count_1_97
theorem discrepancy_1_97 :
    Nat.dist (10^2 * occurrences 10 2 97 0) 0 = 0 := by
  rw [occurrence_1_97]
  decide
theorem count_1_98 : Blocks.count [9, 8] word_1 = 0 := by decide
theorem actualCount_1_98 : Blocks.enumeratedCount [9, 8]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_98
theorem occurrence_1_98 : occurrences 10 2 98 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [9, 8])
    (by decide) (by decide) (by decide) digits_1 count_1_98
theorem discrepancy_1_98 :
    Nat.dist (10^2 * occurrences 10 2 98 0) 0 = 0 := by
  rw [occurrence_1_98]
  decide
theorem count_1_99 : Blocks.count [9, 9] word_1 = 0 := by decide
theorem actualCount_1_99 : Blocks.enumeratedCount [9, 9]
    (actualDigits 10 0 word_1.length) = 0 :=
  certified_count_sound digits_1 count_1_99
theorem occurrence_1_99 : occurrences 10 2 99 0 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_1) (pattern := [9, 9])
    (by decide) (by decide) (by decide) digits_1 count_1_99
theorem discrepancy_1_99 :
    Nat.dist (10^2 * occurrences 10 2 99 0) 0 = 0 := by
  rw [occurrence_1_99]
  decide

def word_2 : List ℕ := [1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
theorem prefix_2_0 : PrefixCertificate (2^0) 0 := by decide
theorem prefix_2_1 : PrefixCertificate (2^1) 1 := by decide
theorem prefix_2_2 : PrefixCertificate (2^2) 2 := by decide
theorem prefix_2_3 : PrefixCertificate (2^3) 4 := by decide
theorem prefix_2_4 : PrefixCertificate (2^4) 9 := by decide
theorem prefix_2_5 : PrefixCertificate (2^5) 19 := by decide
theorem prefix_2_6 : PrefixCertificate (2^6) 39 := by decide
theorem prefix_2_7 : PrefixCertificate (2^7) 79 := by decide
theorem prefix_2_8 : PrefixCertificate (2^8) 158 := by decide
theorem prefix_2_9 : PrefixCertificate (2^9) 316 := by decide
theorem prefix_2_10 : PrefixCertificate (2^10) 632 := by decide
theorem prefix_2_11 : PrefixCertificate (2^11) 1265 := by decide
theorem prefix_2_12 : PrefixCertificate (2^12) 2531 := by decide
theorem prefix_2_13 : PrefixCertificate (2^13) 5062 := by decide
theorem prefix_2_14 : PrefixCertificate (2^14) 10125 := by decide
theorem prefix_2_15 : PrefixCertificate (2^15) 20251 := by decide
theorem prefix_2_16 : PrefixCertificate (2^16) 40503 := by decide
theorem prefix_2_17 : PrefixCertificate (2^17) 81006 := by decide
theorem prefix_2_18 : PrefixCertificate (2^18) 162013 := by decide
theorem prefix_2_19 : PrefixCertificate (2^19) 324027 := by decide
theorem prefix_2_20 : PrefixCertificate (2^20) 648055 := by decide
theorem prefix_2_21 : PrefixCertificate (2^21) 1296111 := by decide
theorem prefix_2_22 : PrefixCertificate (2^22) 2592222 := by decide
theorem prefix_2_23 : PrefixCertificate (2^23) 5184444 := by decide
theorem prefix_2_24 : PrefixCertificate (2^24) 10368889 := by decide
theorem prefix_2_25 : PrefixCertificate (2^25) 20737779 := by decide
theorem prefix_2_26 : PrefixCertificate (2^26) 41475558 := by decide
theorem prefix_2_27 : PrefixCertificate (2^27) 82951117 := by decide
theorem prefix_2_28 : PrefixCertificate (2^28) 165902235 := by decide
theorem prefix_2_29 : PrefixCertificate (2^29) 331804471 := by decide
theorem prefix_2_30 : PrefixCertificate (2^30) 663608942 := by decide
theorem prefix_2_31 : PrefixCertificate (2^31) 1327217884 := by decide
theorem prefix_2_32 : PrefixCertificate (2^32) 2654435769 := by decide
theorem prefix_2_33 : PrefixCertificate (2^33) 5308871538 := by decide
theorem prefix_2_34 : PrefixCertificate (2^34) 10617743077 := by decide
theorem prefix_2_35 : PrefixCertificate (2^35) 21235486155 := by decide
theorem prefix_2_36 : PrefixCertificate (2^36) 42470972311 := by decide
theorem prefix_2_37 : PrefixCertificate (2^37) 84941944623 := by decide
theorem prefix_2_38 : PrefixCertificate (2^38) 169883889247 := by decide
theorem prefix_2_39 : PrefixCertificate (2^39) 339767778495 := by decide
theorem prefix_2_40 : PrefixCertificate (2^40) 679535556991 := by decide
theorem prefix_2_41 : PrefixCertificate (2^41) 1359071113982 := by decide
theorem prefix_2_42 : PrefixCertificate (2^42) 2718142227965 := by decide
theorem prefix_2_43 : PrefixCertificate (2^43) 5436284455930 := by decide
theorem prefix_2_44 : PrefixCertificate (2^44) 10872568911860 := by decide
theorem prefix_2_45 : PrefixCertificate (2^45) 21745137823721 := by decide
theorem prefix_2_46 : PrefixCertificate (2^46) 43490275647442 := by decide
theorem prefix_2_47 : PrefixCertificate (2^47) 86980551294885 := by decide
theorem prefix_2_48 : PrefixCertificate (2^48) 173961102589770 := by decide
theorem prefix_2_49 : PrefixCertificate (2^49) 347922205179540 := by decide
theorem prefix_2_50 : PrefixCertificate (2^50) 695844410359081 := by decide
theorem prefix_2_51 : PrefixCertificate (2^51) 1391688820718163 := by decide
theorem prefix_2_52 : PrefixCertificate (2^52) 2783377641436327 := by decide
theorem prefix_2_53 : PrefixCertificate (2^53) 5566755282872655 := by decide
theorem prefix_2_54 : PrefixCertificate (2^54) 11133510565745311 := by decide
theorem prefix_2_55 : PrefixCertificate (2^55) 22267021131490622 := by decide
theorem prefix_2_56 : PrefixCertificate (2^56) 44534042262981244 := by decide
theorem prefix_2_57 : PrefixCertificate (2^57) 89068084525962488 := by decide
theorem prefix_2_58 : PrefixCertificate (2^58) 178136169051924976 := by decide
theorem prefix_2_59 : PrefixCertificate (2^59) 356272338103849952 := by decide
theorem prefix_2_60 : PrefixCertificate (2^60) 712544676207699905 := by decide
theorem prefix_2_61 : PrefixCertificate (2^61) 1425089352415399810 := by decide
theorem prefix_2_62 : PrefixCertificate (2^62) 2850178704830799621 := by decide
theorem prefix_2_63 : PrefixCertificate (2^63) 5700357409661599242 := by decide
theorem prefix_2_64 : PrefixCertificate (2^64) 11400714819323198485 := by decide
theorem prefix_2_65 : PrefixCertificate (2^65) 22801429638646396971 := by decide
theorem prefix_2_66 : PrefixCertificate (2^66) 45602859277292793943 := by decide
theorem prefix_2_67 : PrefixCertificate (2^67) 91205718554585587887 := by decide
theorem prefix_2_68 : PrefixCertificate (2^68) 182411437109171175775 := by decide
theorem prefix_2_69 : PrefixCertificate (2^69) 364822874218342351550 := by decide
theorem prefix_2_70 : PrefixCertificate (2^70) 729645748436684703100 := by decide
theorem prefix_2_71 : PrefixCertificate (2^71) 1459291496873369406201 := by decide
theorem prefix_2_72 : PrefixCertificate (2^72) 2918582993746738812403 := by decide
theorem prefix_2_73 : PrefixCertificate (2^73) 5837165987493477624807 := by decide
theorem prefix_2_74 : PrefixCertificate (2^74) 11674331974986955249614 := by decide
theorem prefix_2_75 : PrefixCertificate (2^75) 23348663949973910499228 := by decide
theorem prefix_2_76 : PrefixCertificate (2^76) 46697327899947820998457 := by decide
theorem prefix_2_77 : PrefixCertificate (2^77) 93394655799895641996915 := by decide
theorem prefix_2_78 : PrefixCertificate (2^78) 186789311599791283993831 := by decide
theorem prefix_2_79 : PrefixCertificate (2^79) 373578623199582567987662 := by decide
theorem prefix_2_80 : PrefixCertificate (2^80) 747157246399165135975324 := by decide
theorem prefix_2_81 : PrefixCertificate (2^81) 1494314492798330271950649 := by decide
theorem prefix_2_82 : PrefixCertificate (2^82) 2988628985596660543901299 := by decide
theorem prefix_2_83 : PrefixCertificate (2^83) 5977257971193321087802598 := by decide
theorem prefix_2_84 : PrefixCertificate (2^84) 11954515942386642175605196 := by decide
theorem prefix_2_85 : PrefixCertificate (2^85) 23909031884773284351210392 := by decide
theorem prefix_2_86 : PrefixCertificate (2^86) 47818063769546568702420784 := by decide
theorem prefix_2_87 : PrefixCertificate (2^87) 95636127539093137404841568 := by decide
theorem prefix_2_88 : PrefixCertificate (2^88) 191272255078186274809683136 := by decide
theorem prefix_2_89 : PrefixCertificate (2^89) 382544510156372549619366272 := by decide
theorem prefix_2_90 : PrefixCertificate (2^90) 765089020312745099238732545 := by decide
theorem prefix_2_91 : PrefixCertificate (2^91) 1530178040625490198477465091 := by decide
theorem prefix_2_92 : PrefixCertificate (2^92) 3060356081250980396954930182 := by decide
theorem prefix_2_93 : PrefixCertificate (2^93) 6120712162501960793909860364 := by decide
theorem prefix_2_94 : PrefixCertificate (2^94) 12241424325003921587819720728 := by decide
theorem prefix_2_95 : PrefixCertificate (2^95) 24482848650007843175639441456 := by decide
theorem prefix_2_96 : PrefixCertificate (2^96) 48965697300015686351278882912 := by decide
theorem prefix_2_97 : PrefixCertificate (2^97) 97931394600031372702557765824 := by decide
theorem prefix_2_98 : PrefixCertificate (2^98) 195862789200062745405115531649 := by decide
theorem prefix_2_99 : PrefixCertificate (2^99) 391725578400125490810231063298 := by decide
theorem prefix_2_100 : PrefixCertificate (2^100) 783451156800250981620462126597 := by decide
theorem prefix_2_101 : PrefixCertificate (2^101) 1566902313600501963240924253195 := by decide
theorem prefix_2_102 : PrefixCertificate (2^102) 3133804627201003926481848506391 := by decide
theorem prefix_2_103 : PrefixCertificate (2^103) 6267609254402007852963697012782 := by decide
theorem prefix_2_104 : PrefixCertificate (2^104) 12535218508804015705927394025564 := by decide
theorem prefix_2_105 : PrefixCertificate (2^105) 25070437017608031411854788051129 := by decide
theorem prefix_2_106 : PrefixCertificate (2^106) 50140874035216062823709576102259 := by decide
theorem prefix_2_107 : PrefixCertificate (2^107) 100281748070432125647419152204519 := by decide
theorem prefix_2_108 : PrefixCertificate (2^108) 200563496140864251294838304409038 := by decide
theorem prefix_2_109 : PrefixCertificate (2^109) 401126992281728502589676608818077 := by decide
theorem prefix_2_110 : PrefixCertificate (2^110) 802253984563457005179353217636155 := by decide
theorem prefix_2_111 : PrefixCertificate (2^111) 1604507969126914010358706435272310 := by decide
theorem prefix_2_112 : PrefixCertificate (2^112) 3209015938253828020717412870544621 := by decide
theorem prefix_2_113 : PrefixCertificate (2^113) 6418031876507656041434825741089243 := by decide
theorem prefix_2_114 : PrefixCertificate (2^114) 12836063753015312082869651482178487 := by decide
theorem prefix_2_115 : PrefixCertificate (2^115) 25672127506030624165739302964356974 := by decide
theorem prefix_2_116 : PrefixCertificate (2^116) 51344255012061248331478605928713948 := by decide
theorem prefix_2_117 : PrefixCertificate (2^117) 102688510024122496662957211857427897 := by decide
theorem prefix_2_118 : PrefixCertificate (2^118) 205377020048244993325914423714855794 := by decide
theorem prefix_2_119 : PrefixCertificate (2^119) 410754040096489986651828847429711588 := by decide
theorem prefix_2_120 : PrefixCertificate (2^120) 821508080192979973303657694859423176 := by decide
theorem prefix_2_121 : PrefixCertificate (2^121) 1643016160385959946607315389718846352 := by decide
theorem prefix_2_122 : PrefixCertificate (2^122) 3286032320771919893214630779437692704 := by decide
theorem prefix_2_123 : PrefixCertificate (2^123) 6572064641543839786429261558875385409 := by decide
theorem prefix_2_124 : PrefixCertificate (2^124) 13144129283087679572858523117750770819 := by decide
theorem prefix_2_125 : PrefixCertificate (2^125) 26288258566175359145717046235501541638 := by decide
theorem prefix_2_126 : PrefixCertificate (2^126) 52576517132350718291434092471003083277 := by decide
theorem prefix_2_127 : PrefixCertificate (2^127) 105153034264701436582868184942006166554 := by decide
theorem prefix_2_128 : PrefixCertificate (2^128) 210306068529402873165736369884012333108 := by decide
theorem prefix_2_129 : PrefixCertificate (2^129) 420612137058805746331472739768024666216 := by decide
theorem prefix_2_130 : PrefixCertificate (2^130) 841224274117611492662945479536049332432 := by decide
theorem prefix_2_131 : PrefixCertificate (2^131) 1682448548235222985325890959072098664864 := by decide
theorem prefix_2_132 : PrefixCertificate (2^132) 3364897096470445970651781918144197329729 := by decide
theorem prefix_2_133 : PrefixCertificate (2^133) 6729794192940891941303563836288394659458 := by decide
theorem prefix_2_134 : PrefixCertificate (2^134) 13459588385881783882607127672576789318916 := by decide
theorem prefix_2_135 : PrefixCertificate (2^135) 26919176771763567765214255345153578637832 := by decide
theorem prefix_2_136 : PrefixCertificate (2^136) 53838353543527135530428510690307157275664 := by decide
theorem prefix_2_137 : PrefixCertificate (2^137) 107676707087054271060857021380614314551329 := by decide
theorem prefix_2_138 : PrefixCertificate (2^138) 215353414174108542121714042761228629102658 := by decide
theorem prefix_2_139 : PrefixCertificate (2^139) 430706828348217084243428085522457258205316 := by decide
theorem prefix_2_140 : PrefixCertificate (2^140) 861413656696434168486856171044914516410632 := by decide
theorem prefix_2_141 : PrefixCertificate (2^141) 1722827313392868336973712342089829032821264 := by decide
theorem prefix_2_142 : PrefixCertificate (2^142) 3445654626785736673947424684179658065642528 := by decide
theorem prefix_2_143 : PrefixCertificate (2^143) 6891309253571473347894849368359316131285057 := by decide
theorem prefix_2_144 : PrefixCertificate (2^144) 13782618507142946695789698736718632262570114 := by decide
theorem prefix_2_145 : PrefixCertificate (2^145) 27565237014285893391579397473437264525140228 := by decide
theorem prefix_2_146 : PrefixCertificate (2^146) 55130474028571786783158794946874529050280456 := by decide
theorem prefix_2_147 : PrefixCertificate (2^147) 110260948057143573566317589893749058100560913 := by decide
theorem prefix_2_148 : PrefixCertificate (2^148) 220521896114287147132635179787498116201121826 := by decide
theorem prefix_2_149 : PrefixCertificate (2^149) 441043792228574294265270359574996232402243652 := by decide
theorem prefix_2_150 : PrefixCertificate (2^150) 882087584457148588530540719149992464804487305 := by decide
theorem prefix_2_151 : PrefixCertificate (2^151) 1764175168914297177061081438299984929608974611 := by decide
theorem prefix_2_152 : PrefixCertificate (2^152) 3528350337828594354122162876599969859217949223 := by decide
theorem prefix_2_153 : PrefixCertificate (2^153) 7056700675657188708244325753199939718435898446 := by decide
theorem prefix_2_154 : PrefixCertificate (2^154) 14113401351314377416488651506399879436871796893 := by decide
theorem prefix_2_155 : PrefixCertificate (2^155) 28226802702628754832977303012799758873743593787 := by decide
theorem prefix_2_156 : PrefixCertificate (2^156) 56453605405257509665954606025599517747487187574 := by decide
theorem prefix_2_157 : PrefixCertificate (2^157) 112907210810515019331909212051199035494974375149 := by decide
theorem prefix_2_158 : PrefixCertificate (2^158) 225814421621030038663818424102398070989948750298 := by decide
theorem prefix_2_159 : PrefixCertificate (2^159) 451628843242060077327636848204796141979897500597 := by decide
theorem prefix_2_160 : PrefixCertificate (2^160) 903257686484120154655273696409592283959795001195 := by decide
theorem prefix_2_161 : PrefixCertificate (2^161) 1806515372968240309310547392819184567919590002391 := by decide
theorem prefix_2_162 : PrefixCertificate (2^162) 3613030745936480618621094785638369135839180004783 := by decide
theorem prefix_2_163 : PrefixCertificate (2^163) 7226061491872961237242189571276738271678360009567 := by decide
theorem prefix_2_164 : PrefixCertificate (2^164) 14452122983745922474484379142553476543356720019135 := by decide
theorem prefix_2_165 : PrefixCertificate (2^165) 28904245967491844948968758285106953086713440038270 := by decide
theorem prefix_2_166 : PrefixCertificate (2^166) 57808491934983689897937516570213906173426880076540 := by decide
theorem prefix_2_167 : PrefixCertificate (2^167) 115616983869967379795875033140427812346853760153081 := by decide
theorem prefix_2_168 : PrefixCertificate (2^168) 231233967739934759591750066280855624693707520306163 := by decide
theorem prefix_2_169 : PrefixCertificate (2^169) 462467935479869519183500132561711249387415040612327 := by decide
theorem prefix_2_170 : PrefixCertificate (2^170) 924935870959739038367000265123422498774830081224654 := by decide
theorem prefix_2_171 : PrefixCertificate (2^171) 1849871741919478076734000530246844997549660162449309 := by decide
theorem prefix_2_172 : PrefixCertificate (2^172) 3699743483838956153468001060493689995099320324898618 := by decide
theorem prefix_2_173 : PrefixCertificate (2^173) 7399486967677912306936002120987379990198640649797236 := by decide
theorem prefix_2_174 : PrefixCertificate (2^174) 14798973935355824613872004241974759980397281299594472 := by decide
theorem prefix_2_175 : PrefixCertificate (2^175) 29597947870711649227744008483949519960794562599188945 := by decide
theorem prefix_2_176 : PrefixCertificate (2^176) 59195895741423298455488016967899039921589125198377890 := by decide
theorem prefix_2_177 : PrefixCertificate (2^177) 118391791482846596910976033935798079843178250396755780 := by decide
theorem prefix_2_178 : PrefixCertificate (2^178) 236783582965693193821952067871596159686356500793511561 := by decide
theorem prefix_2_179 : PrefixCertificate (2^179) 473567165931386387643904135743192319372713001587023123 := by decide
theorem prefix_2_180 : PrefixCertificate (2^180) 947134331862772775287808271486384638745426003174046247 := by decide
theorem prefix_2_181 : PrefixCertificate (2^181) 1894268663725545550575616542972769277490852006348092494 := by decide
theorem prefix_2_182 : PrefixCertificate (2^182) 3788537327451091101151233085945538554981704012696184988 := by decide
theorem prefix_2_183 : PrefixCertificate (2^183) 7577074654902182202302466171891077109963408025392369977 := by decide
theorem prefix_2_184 : PrefixCertificate (2^184) 15154149309804364404604932343782154219926816050784739954 := by decide
theorem prefix_2_185 : PrefixCertificate (2^185) 30308298619608728809209864687564308439853632101569479908 := by decide
theorem prefix_2_186 : PrefixCertificate (2^186) 60616597239217457618419729375128616879707264203138959817 := by decide
theorem prefix_2_187 : PrefixCertificate (2^187) 121233194478434915236839458750257233759414528406277919634 := by decide
theorem prefix_2_188 : PrefixCertificate (2^188) 242466388956869830473678917500514467518829056812555839269 := by decide
theorem prefix_2_189 : PrefixCertificate (2^189) 484932777913739660947357835001028935037658113625111678538 := by decide
theorem prefix_2_190 : PrefixCertificate (2^190) 969865555827479321894715670002057870075316227250223357076 := by decide
theorem prefix_2_191 : PrefixCertificate (2^191) 1939731111654958643789431340004115740150632454500446714152 := by decide
theorem prefix_2_192 : PrefixCertificate (2^192) 3879462223309917287578862680008231480301264909000893428305 := by decide
theorem prefix_2_193 : PrefixCertificate (2^193) 7758924446619834575157725360016462960602529818001786856611 := by decide
theorem prefix_2_194 : PrefixCertificate (2^194) 15517848893239669150315450720032925921205059636003573713223 := by decide
theorem prefix_2_195 : PrefixCertificate (2^195) 31035697786479338300630901440065851842410119272007147426447 := by decide
theorem prefix_2_196 : PrefixCertificate (2^196) 62071395572958676601261802880131703684820238544014294852895 := by decide
theorem prefix_2_197 : PrefixCertificate (2^197) 124142791145917353202523605760263407369640477088028589705791 := by decide
theorem prefix_2_198 : PrefixCertificate (2^198) 248285582291834706405047211520526814739280954176057179411582 := by decide
theorem prefix_2_199 : PrefixCertificate (2^199) 496571164583669412810094423041053629478561908352114358823164 := by decide
theorem prefix_2_200 : PrefixCertificate (2^200) 993142329167338825620188846082107258957123816704228717646328 := by decide
theorem prefix_2_201 : PrefixCertificate (2^201) 1986284658334677651240377692164214517914247633408457435292656 := by decide
theorem prefix_2_202 : PrefixCertificate (2^202) 3972569316669355302480755384328429035828495266816914870585313 := by decide
theorem prefix_2_203 : PrefixCertificate (2^203) 7945138633338710604961510768656858071656990533633829741170627 := by decide
theorem prefix_2_204 : PrefixCertificate (2^204) 15890277266677421209923021537313716143313981067267659482341254 := by decide
theorem prefix_2_205 : PrefixCertificate (2^205) 31780554533354842419846043074627432286627962134535318964682509 := by decide
theorem prefix_2_206 : PrefixCertificate (2^206) 63561109066709684839692086149254864573255924269070637929365019 := by decide
theorem prefix_2_207 : PrefixCertificate (2^207) 127122218133419369679384172298509729146511848538141275858730038 := by decide
theorem prefix_2_208 : PrefixCertificate (2^208) 254244436266838739358768344597019458293023697076282551717460076 := by decide
theorem prefix_2_209 : PrefixCertificate (2^209) 508488872533677478717536689194038916586047394152565103434920152 := by decide
theorem prefix_2_210 : PrefixCertificate (2^210) 1016977745067354957435073378388077833172094788305130206869840305 := by decide
theorem prefix_2_211 : PrefixCertificate (2^211) 2033955490134709914870146756776155666344189576610260413739680611 := by decide
theorem prefix_2_212 : PrefixCertificate (2^212) 4067910980269419829740293513552311332688379153220520827479361222 := by decide
theorem prefix_2_213 : PrefixCertificate (2^213) 8135821960538839659480587027104622665376758306441041654958722445 := by decide
theorem prefix_2_214 : PrefixCertificate (2^214) 16271643921077679318961174054209245330753516612882083309917444890 := by decide
theorem prefix_2_215 : PrefixCertificate (2^215) 32543287842155358637922348108418490661507033225764166619834889781 := by decide
theorem prefix_2_216 : PrefixCertificate (2^216) 65086575684310717275844696216836981323014066451528333239669779562 := by decide
theorem prefix_2_217 : PrefixCertificate (2^217) 130173151368621434551689392433673962646028132903056666479339559124 := by decide
theorem prefix_2_218 : PrefixCertificate (2^218) 260346302737242869103378784867347925292056265806113332958679118248 := by decide
theorem prefix_2_219 : PrefixCertificate (2^219) 520692605474485738206757569734695850584112531612226665917358236496 := by decide
theorem prefix_2_220 : PrefixCertificate (2^220) 1041385210948971476413515139469391701168225063224453331834716472993 := by decide
theorem prefix_2_221 : PrefixCertificate (2^221) 2082770421897942952827030278938783402336450126448906663669432945986 := by decide
theorem prefix_2_222 : PrefixCertificate (2^222) 4165540843795885905654060557877566804672900252897813327338865891972 := by decide
theorem prefix_2_223 : PrefixCertificate (2^223) 8331081687591771811308121115755133609345800505795626654677731783944 := by decide
theorem prefix_2_224 : PrefixCertificate (2^224) 16662163375183543622616242231510267218691601011591253309355463567889 := by decide
theorem prefix_2_225 : PrefixCertificate (2^225) 33324326750367087245232484463020534437383202023182506618710927135779 := by decide
theorem prefix_2_226 : PrefixCertificate (2^226) 66648653500734174490464968926041068874766404046365013237421854271559 := by decide
theorem prefix_2_227 : PrefixCertificate (2^227) 133297307001468348980929937852082137749532808092730026474843708543118 := by decide
theorem prefix_2_228 : PrefixCertificate (2^228) 266594614002936697961859875704164275499065616185460052949687417086237 := by decide
theorem prefix_2_229 : PrefixCertificate (2^229) 533189228005873395923719751408328550998131232370920105899374834172474 := by decide
theorem prefix_2_230 : PrefixCertificate (2^230) 1066378456011746791847439502816657101996262464741840211798749668344948 := by decide
theorem prefix_2_231 : PrefixCertificate (2^231) 2132756912023493583694879005633314203992524929483680423597499336689896 := by decide
theorem prefix_2_232 : PrefixCertificate (2^232) 4265513824046987167389758011266628407985049858967360847194998673379792 := by decide
theorem prefix_2_233 : PrefixCertificate (2^233) 8531027648093974334779516022533256815970099717934721694389997346759585 := by decide
theorem prefix_2_234 : PrefixCertificate (2^234) 17062055296187948669559032045066513631940199435869443388779994693519171 := by decide
theorem prefix_2_235 : PrefixCertificate (2^235) 34124110592375897339118064090133027263880398871738886777559989387038342 := by decide
theorem prefix_2_236 : PrefixCertificate (2^236) 68248221184751794678236128180266054527760797743477773555119978774076684 := by decide
theorem prefix_2_237 : PrefixCertificate (2^237) 136496442369503589356472256360532109055521595486955547110239957548153368 := by decide
theorem prefix_2_238 : PrefixCertificate (2^238) 272992884739007178712944512721064218111043190973911094220479915096306736 := by decide
theorem prefix_2_239 : PrefixCertificate (2^239) 545985769478014357425889025442128436222086381947822188440959830192613472 := by decide
theorem prefix_2_240 : PrefixCertificate (2^240) 1091971538956028714851778050884256872444172763895644376881919660385226945 := by decide
theorem prefix_2_241 : PrefixCertificate (2^241) 2183943077912057429703556101768513744888345527791288753763839320770453891 := by decide
theorem prefix_2_242 : PrefixCertificate (2^242) 4367886155824114859407112203537027489776691055582577507527678641540907782 := by decide
theorem prefix_2_243 : PrefixCertificate (2^243) 8735772311648229718814224407074054979553382111165155015055357283081815564 := by decide
theorem prefix_2_244 : PrefixCertificate (2^244) 17471544623296459437628448814148109959106764222330310030110714566163631128 := by decide
theorem prefix_2_245 : PrefixCertificate (2^245) 34943089246592918875256897628296219918213528444660620060221429132327262257 := by decide
theorem prefix_2_246 : PrefixCertificate (2^246) 69886178493185837750513795256592439836427056889321240120442858264654524515 := by decide
theorem prefix_2_247 : PrefixCertificate (2^247) 139772356986371675501027590513184879672854113778642480240885716529309049031 := by decide
theorem prefix_2_248 : PrefixCertificate (2^248) 279544713972743351002055181026369759345708227557284960481771433058618098062 := by decide
theorem prefix_2_249 : PrefixCertificate (2^249) 559089427945486702004110362052739518691416455114569920963542866117236196125 := by decide
theorem prefix_2_250 : PrefixCertificate (2^250) 1118178855890973404008220724105479037382832910229139841927085732234472392250 := by decide
theorem prefix_2_251 : PrefixCertificate (2^251) 2236357711781946808016441448210958074765665820458279683854171464468944784500 := by decide
theorem prefix_2_252 : PrefixCertificate (2^252) 4472715423563893616032882896421916149531331640916559367708342928937889569001 := by decide
theorem prefix_2_253 : PrefixCertificate (2^253) 8945430847127787232065765792843832299062663281833118735416685857875779138002 := by decide
theorem prefix_2_254 : PrefixCertificate (2^254) 17890861694255574464131531585687664598125326563666237470833371715751558276005 := by decide
theorem prefix_2_255 : PrefixCertificate (2^255) 35781723388511148928263063171375329196250653127332474941666743431503116552010 := by decide
theorem prefix_2_256 : PrefixCertificate (2^256) 71563446777022297856526126342750658392501306254664949883333486863006233104021 := by decide
theorem digit_2_0 : digit 2 0 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_0 prefix_2_1
theorem digit_2_1 : digit 2 1 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_1 prefix_2_2
theorem digit_2_2 : digit 2 2 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_2 prefix_2_3
theorem digit_2_3 : digit 2 3 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_3 prefix_2_4
theorem digit_2_4 : digit 2 4 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_4 prefix_2_5
theorem digit_2_5 : digit 2 5 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_5 prefix_2_6
theorem digit_2_6 : digit 2 6 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_6 prefix_2_7
theorem digit_2_7 : digit 2 7 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_7 prefix_2_8
theorem digit_2_8 : digit 2 8 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_8 prefix_2_9
theorem digit_2_9 : digit 2 9 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_9 prefix_2_10
theorem digit_2_10 : digit 2 10 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_10 prefix_2_11
theorem digit_2_11 : digit 2 11 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_11 prefix_2_12
theorem digit_2_12 : digit 2 12 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_12 prefix_2_13
theorem digit_2_13 : digit 2 13 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_13 prefix_2_14
theorem digit_2_14 : digit 2 14 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_14 prefix_2_15
theorem digit_2_15 : digit 2 15 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_15 prefix_2_16
theorem digit_2_16 : digit 2 16 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_16 prefix_2_17
theorem digit_2_17 : digit 2 17 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_17 prefix_2_18
theorem digit_2_18 : digit 2 18 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_18 prefix_2_19
theorem digit_2_19 : digit 2 19 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_19 prefix_2_20
theorem digit_2_20 : digit 2 20 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_20 prefix_2_21
theorem digit_2_21 : digit 2 21 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_21 prefix_2_22
theorem digit_2_22 : digit 2 22 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_22 prefix_2_23
theorem digit_2_23 : digit 2 23 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_23 prefix_2_24
theorem digit_2_24 : digit 2 24 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_24 prefix_2_25
theorem digit_2_25 : digit 2 25 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_25 prefix_2_26
theorem digit_2_26 : digit 2 26 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_26 prefix_2_27
theorem digit_2_27 : digit 2 27 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_27 prefix_2_28
theorem digit_2_28 : digit 2 28 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_28 prefix_2_29
theorem digit_2_29 : digit 2 29 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_29 prefix_2_30
theorem digit_2_30 : digit 2 30 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_30 prefix_2_31
theorem digit_2_31 : digit 2 31 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_31 prefix_2_32
theorem digit_2_32 : digit 2 32 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_32 prefix_2_33
theorem digit_2_33 : digit 2 33 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_33 prefix_2_34
theorem digit_2_34 : digit 2 34 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_34 prefix_2_35
theorem digit_2_35 : digit 2 35 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_35 prefix_2_36
theorem digit_2_36 : digit 2 36 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_36 prefix_2_37
theorem digit_2_37 : digit 2 37 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_37 prefix_2_38
theorem digit_2_38 : digit 2 38 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_38 prefix_2_39
theorem digit_2_39 : digit 2 39 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_39 prefix_2_40
theorem digit_2_40 : digit 2 40 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_40 prefix_2_41
theorem digit_2_41 : digit 2 41 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_41 prefix_2_42
theorem digit_2_42 : digit 2 42 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_42 prefix_2_43
theorem digit_2_43 : digit 2 43 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_43 prefix_2_44
theorem digit_2_44 : digit 2 44 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_44 prefix_2_45
theorem digit_2_45 : digit 2 45 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_45 prefix_2_46
theorem digit_2_46 : digit 2 46 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_46 prefix_2_47
theorem digit_2_47 : digit 2 47 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_47 prefix_2_48
theorem digit_2_48 : digit 2 48 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_48 prefix_2_49
theorem digit_2_49 : digit 2 49 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_49 prefix_2_50
theorem digit_2_50 : digit 2 50 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_50 prefix_2_51
theorem digit_2_51 : digit 2 51 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_51 prefix_2_52
theorem digit_2_52 : digit 2 52 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_52 prefix_2_53
theorem digit_2_53 : digit 2 53 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_53 prefix_2_54
theorem digit_2_54 : digit 2 54 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_54 prefix_2_55
theorem digit_2_55 : digit 2 55 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_55 prefix_2_56
theorem digit_2_56 : digit 2 56 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_56 prefix_2_57
theorem digit_2_57 : digit 2 57 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_57 prefix_2_58
theorem digit_2_58 : digit 2 58 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_58 prefix_2_59
theorem digit_2_59 : digit 2 59 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_59 prefix_2_60
theorem digit_2_60 : digit 2 60 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_60 prefix_2_61
theorem digit_2_61 : digit 2 61 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_61 prefix_2_62
theorem digit_2_62 : digit 2 62 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_62 prefix_2_63
theorem digit_2_63 : digit 2 63 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_63 prefix_2_64
theorem digit_2_64 : digit 2 64 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_64 prefix_2_65
theorem digit_2_65 : digit 2 65 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_65 prefix_2_66
theorem digit_2_66 : digit 2 66 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_66 prefix_2_67
theorem digit_2_67 : digit 2 67 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_67 prefix_2_68
theorem digit_2_68 : digit 2 68 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_68 prefix_2_69
theorem digit_2_69 : digit 2 69 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_69 prefix_2_70
theorem digit_2_70 : digit 2 70 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_70 prefix_2_71
theorem digit_2_71 : digit 2 71 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_71 prefix_2_72
theorem digit_2_72 : digit 2 72 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_72 prefix_2_73
theorem digit_2_73 : digit 2 73 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_73 prefix_2_74
theorem digit_2_74 : digit 2 74 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_74 prefix_2_75
theorem digit_2_75 : digit 2 75 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_75 prefix_2_76
theorem digit_2_76 : digit 2 76 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_76 prefix_2_77
theorem digit_2_77 : digit 2 77 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_77 prefix_2_78
theorem digit_2_78 : digit 2 78 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_78 prefix_2_79
theorem digit_2_79 : digit 2 79 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_79 prefix_2_80
theorem digit_2_80 : digit 2 80 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_80 prefix_2_81
theorem digit_2_81 : digit 2 81 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_81 prefix_2_82
theorem digit_2_82 : digit 2 82 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_82 prefix_2_83
theorem digit_2_83 : digit 2 83 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_83 prefix_2_84
theorem digit_2_84 : digit 2 84 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_84 prefix_2_85
theorem digit_2_85 : digit 2 85 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_85 prefix_2_86
theorem digit_2_86 : digit 2 86 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_86 prefix_2_87
theorem digit_2_87 : digit 2 87 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_87 prefix_2_88
theorem digit_2_88 : digit 2 88 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_88 prefix_2_89
theorem digit_2_89 : digit 2 89 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_89 prefix_2_90
theorem digit_2_90 : digit 2 90 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_90 prefix_2_91
theorem digit_2_91 : digit 2 91 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_91 prefix_2_92
theorem digit_2_92 : digit 2 92 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_92 prefix_2_93
theorem digit_2_93 : digit 2 93 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_93 prefix_2_94
theorem digit_2_94 : digit 2 94 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_94 prefix_2_95
theorem digit_2_95 : digit 2 95 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_95 prefix_2_96
theorem digit_2_96 : digit 2 96 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_96 prefix_2_97
theorem digit_2_97 : digit 2 97 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_97 prefix_2_98
theorem digit_2_98 : digit 2 98 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_98 prefix_2_99
theorem digit_2_99 : digit 2 99 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_99 prefix_2_100
theorem digit_2_100 : digit 2 100 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_100 prefix_2_101
theorem digit_2_101 : digit 2 101 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_101 prefix_2_102
theorem digit_2_102 : digit 2 102 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_102 prefix_2_103
theorem digit_2_103 : digit 2 103 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_103 prefix_2_104
theorem digit_2_104 : digit 2 104 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_104 prefix_2_105
theorem digit_2_105 : digit 2 105 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_105 prefix_2_106
theorem digit_2_106 : digit 2 106 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_106 prefix_2_107
theorem digit_2_107 : digit 2 107 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_107 prefix_2_108
theorem digit_2_108 : digit 2 108 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_108 prefix_2_109
theorem digit_2_109 : digit 2 109 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_109 prefix_2_110
theorem digit_2_110 : digit 2 110 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_110 prefix_2_111
theorem digit_2_111 : digit 2 111 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_111 prefix_2_112
theorem digit_2_112 : digit 2 112 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_112 prefix_2_113
theorem digit_2_113 : digit 2 113 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_113 prefix_2_114
theorem digit_2_114 : digit 2 114 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_114 prefix_2_115
theorem digit_2_115 : digit 2 115 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_115 prefix_2_116
theorem digit_2_116 : digit 2 116 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_116 prefix_2_117
theorem digit_2_117 : digit 2 117 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_117 prefix_2_118
theorem digit_2_118 : digit 2 118 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_118 prefix_2_119
theorem digit_2_119 : digit 2 119 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_119 prefix_2_120
theorem digit_2_120 : digit 2 120 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_120 prefix_2_121
theorem digit_2_121 : digit 2 121 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_121 prefix_2_122
theorem digit_2_122 : digit 2 122 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_122 prefix_2_123
theorem digit_2_123 : digit 2 123 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_123 prefix_2_124
theorem digit_2_124 : digit 2 124 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_124 prefix_2_125
theorem digit_2_125 : digit 2 125 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_125 prefix_2_126
theorem digit_2_126 : digit 2 126 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_126 prefix_2_127
theorem digit_2_127 : digit 2 127 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_127 prefix_2_128
theorem digit_2_128 : digit 2 128 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_128 prefix_2_129
theorem digit_2_129 : digit 2 129 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_129 prefix_2_130
theorem digit_2_130 : digit 2 130 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_130 prefix_2_131
theorem digit_2_131 : digit 2 131 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_131 prefix_2_132
theorem digit_2_132 : digit 2 132 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_132 prefix_2_133
theorem digit_2_133 : digit 2 133 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_133 prefix_2_134
theorem digit_2_134 : digit 2 134 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_134 prefix_2_135
theorem digit_2_135 : digit 2 135 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_135 prefix_2_136
theorem digit_2_136 : digit 2 136 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_136 prefix_2_137
theorem digit_2_137 : digit 2 137 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_137 prefix_2_138
theorem digit_2_138 : digit 2 138 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_138 prefix_2_139
theorem digit_2_139 : digit 2 139 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_139 prefix_2_140
theorem digit_2_140 : digit 2 140 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_140 prefix_2_141
theorem digit_2_141 : digit 2 141 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_141 prefix_2_142
theorem digit_2_142 : digit 2 142 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_142 prefix_2_143
theorem digit_2_143 : digit 2 143 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_143 prefix_2_144
theorem digit_2_144 : digit 2 144 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_144 prefix_2_145
theorem digit_2_145 : digit 2 145 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_145 prefix_2_146
theorem digit_2_146 : digit 2 146 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_146 prefix_2_147
theorem digit_2_147 : digit 2 147 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_147 prefix_2_148
theorem digit_2_148 : digit 2 148 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_148 prefix_2_149
theorem digit_2_149 : digit 2 149 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_149 prefix_2_150
theorem digit_2_150 : digit 2 150 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_150 prefix_2_151
theorem digit_2_151 : digit 2 151 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_151 prefix_2_152
theorem digit_2_152 : digit 2 152 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_152 prefix_2_153
theorem digit_2_153 : digit 2 153 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_153 prefix_2_154
theorem digit_2_154 : digit 2 154 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_154 prefix_2_155
theorem digit_2_155 : digit 2 155 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_155 prefix_2_156
theorem digit_2_156 : digit 2 156 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_156 prefix_2_157
theorem digit_2_157 : digit 2 157 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_157 prefix_2_158
theorem digit_2_158 : digit 2 158 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_158 prefix_2_159
theorem digit_2_159 : digit 2 159 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_159 prefix_2_160
theorem digit_2_160 : digit 2 160 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_160 prefix_2_161
theorem digit_2_161 : digit 2 161 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_161 prefix_2_162
theorem digit_2_162 : digit 2 162 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_162 prefix_2_163
theorem digit_2_163 : digit 2 163 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_163 prefix_2_164
theorem digit_2_164 : digit 2 164 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_164 prefix_2_165
theorem digit_2_165 : digit 2 165 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_165 prefix_2_166
theorem digit_2_166 : digit 2 166 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_166 prefix_2_167
theorem digit_2_167 : digit 2 167 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_167 prefix_2_168
theorem digit_2_168 : digit 2 168 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_168 prefix_2_169
theorem digit_2_169 : digit 2 169 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_169 prefix_2_170
theorem digit_2_170 : digit 2 170 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_170 prefix_2_171
theorem digit_2_171 : digit 2 171 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_171 prefix_2_172
theorem digit_2_172 : digit 2 172 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_172 prefix_2_173
theorem digit_2_173 : digit 2 173 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_173 prefix_2_174
theorem digit_2_174 : digit 2 174 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_174 prefix_2_175
theorem digit_2_175 : digit 2 175 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_175 prefix_2_176
theorem digit_2_176 : digit 2 176 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_176 prefix_2_177
theorem digit_2_177 : digit 2 177 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_177 prefix_2_178
theorem digit_2_178 : digit 2 178 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_178 prefix_2_179
theorem digit_2_179 : digit 2 179 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_179 prefix_2_180
theorem digit_2_180 : digit 2 180 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_180 prefix_2_181
theorem digit_2_181 : digit 2 181 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_181 prefix_2_182
theorem digit_2_182 : digit 2 182 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_182 prefix_2_183
theorem digit_2_183 : digit 2 183 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_183 prefix_2_184
theorem digit_2_184 : digit 2 184 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_184 prefix_2_185
theorem digit_2_185 : digit 2 185 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_185 prefix_2_186
theorem digit_2_186 : digit 2 186 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_186 prefix_2_187
theorem digit_2_187 : digit 2 187 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_187 prefix_2_188
theorem digit_2_188 : digit 2 188 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_188 prefix_2_189
theorem digit_2_189 : digit 2 189 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_189 prefix_2_190
theorem digit_2_190 : digit 2 190 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_190 prefix_2_191
theorem digit_2_191 : digit 2 191 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_191 prefix_2_192
theorem digit_2_192 : digit 2 192 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_192 prefix_2_193
theorem digit_2_193 : digit 2 193 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_193 prefix_2_194
theorem digit_2_194 : digit 2 194 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_194 prefix_2_195
theorem digit_2_195 : digit 2 195 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_195 prefix_2_196
theorem digit_2_196 : digit 2 196 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_196 prefix_2_197
theorem digit_2_197 : digit 2 197 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_197 prefix_2_198
theorem digit_2_198 : digit 2 198 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_198 prefix_2_199
theorem digit_2_199 : digit 2 199 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_199 prefix_2_200
theorem digit_2_200 : digit 2 200 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_200 prefix_2_201
theorem digit_2_201 : digit 2 201 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_201 prefix_2_202
theorem digit_2_202 : digit 2 202 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_202 prefix_2_203
theorem digit_2_203 : digit 2 203 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_203 prefix_2_204
theorem digit_2_204 : digit 2 204 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_204 prefix_2_205
theorem digit_2_205 : digit 2 205 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_205 prefix_2_206
theorem digit_2_206 : digit 2 206 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_206 prefix_2_207
theorem digit_2_207 : digit 2 207 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_207 prefix_2_208
theorem digit_2_208 : digit 2 208 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_208 prefix_2_209
theorem digit_2_209 : digit 2 209 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_209 prefix_2_210
theorem digit_2_210 : digit 2 210 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_210 prefix_2_211
theorem digit_2_211 : digit 2 211 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_211 prefix_2_212
theorem digit_2_212 : digit 2 212 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_212 prefix_2_213
theorem digit_2_213 : digit 2 213 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_213 prefix_2_214
theorem digit_2_214 : digit 2 214 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_214 prefix_2_215
theorem digit_2_215 : digit 2 215 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_215 prefix_2_216
theorem digit_2_216 : digit 2 216 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_216 prefix_2_217
theorem digit_2_217 : digit 2 217 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_217 prefix_2_218
theorem digit_2_218 : digit 2 218 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_218 prefix_2_219
theorem digit_2_219 : digit 2 219 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_219 prefix_2_220
theorem digit_2_220 : digit 2 220 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_220 prefix_2_221
theorem digit_2_221 : digit 2 221 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_221 prefix_2_222
theorem digit_2_222 : digit 2 222 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_222 prefix_2_223
theorem digit_2_223 : digit 2 223 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_223 prefix_2_224
theorem digit_2_224 : digit 2 224 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_224 prefix_2_225
theorem digit_2_225 : digit 2 225 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_225 prefix_2_226
theorem digit_2_226 : digit 2 226 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_226 prefix_2_227
theorem digit_2_227 : digit 2 227 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_227 prefix_2_228
theorem digit_2_228 : digit 2 228 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_228 prefix_2_229
theorem digit_2_229 : digit 2 229 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_229 prefix_2_230
theorem digit_2_230 : digit 2 230 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_230 prefix_2_231
theorem digit_2_231 : digit 2 231 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_231 prefix_2_232
theorem digit_2_232 : digit 2 232 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_232 prefix_2_233
theorem digit_2_233 : digit 2 233 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_233 prefix_2_234
theorem digit_2_234 : digit 2 234 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_234 prefix_2_235
theorem digit_2_235 : digit 2 235 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_235 prefix_2_236
theorem digit_2_236 : digit 2 236 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_236 prefix_2_237
theorem digit_2_237 : digit 2 237 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_237 prefix_2_238
theorem digit_2_238 : digit 2 238 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_238 prefix_2_239
theorem digit_2_239 : digit 2 239 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_239 prefix_2_240
theorem digit_2_240 : digit 2 240 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_240 prefix_2_241
theorem digit_2_241 : digit 2 241 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_241 prefix_2_242
theorem digit_2_242 : digit 2 242 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_242 prefix_2_243
theorem digit_2_243 : digit 2 243 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_243 prefix_2_244
theorem digit_2_244 : digit 2 244 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_244 prefix_2_245
theorem digit_2_245 : digit 2 245 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_245 prefix_2_246
theorem digit_2_246 : digit 2 246 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_246 prefix_2_247
theorem digit_2_247 : digit 2 247 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_247 prefix_2_248
theorem digit_2_248 : digit 2 248 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_248 prefix_2_249
theorem digit_2_249 : digit 2 249 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_249 prefix_2_250
theorem digit_2_250 : digit 2 250 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_250 prefix_2_251
theorem digit_2_251 : digit 2 251 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_251 prefix_2_252
theorem digit_2_252 : digit 2 252 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_252 prefix_2_253
theorem digit_2_253 : digit 2 253 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_253 prefix_2_254
theorem digit_2_254 : digit 2 254 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_254 prefix_2_255
theorem digit_2_255 : digit 2 255 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_2_255 prefix_2_256
theorem digits_2 : DigitsAt 2 0 word_2 := And.intro digit_2_0 (And.intro digit_2_1 (And.intro digit_2_2 (And.intro digit_2_3 (And.intro digit_2_4 (And.intro digit_2_5 (And.intro digit_2_6 (And.intro digit_2_7 (And.intro digit_2_8 (And.intro digit_2_9 (And.intro digit_2_10 (And.intro digit_2_11 (And.intro digit_2_12 (And.intro digit_2_13 (And.intro digit_2_14 (And.intro digit_2_15 (And.intro digit_2_16 (And.intro digit_2_17 (And.intro digit_2_18 (And.intro digit_2_19 (And.intro digit_2_20 (And.intro digit_2_21 (And.intro digit_2_22 (And.intro digit_2_23 (And.intro digit_2_24 (And.intro digit_2_25 (And.intro digit_2_26 (And.intro digit_2_27 (And.intro digit_2_28 (And.intro digit_2_29 (And.intro digit_2_30 (And.intro digit_2_31 (And.intro digit_2_32 (And.intro digit_2_33 (And.intro digit_2_34 (And.intro digit_2_35 (And.intro digit_2_36 (And.intro digit_2_37 (And.intro digit_2_38 (And.intro digit_2_39 (And.intro digit_2_40 (And.intro digit_2_41 (And.intro digit_2_42 (And.intro digit_2_43 (And.intro digit_2_44 (And.intro digit_2_45 (And.intro digit_2_46 (And.intro digit_2_47 (And.intro digit_2_48 (And.intro digit_2_49 (And.intro digit_2_50 (And.intro digit_2_51 (And.intro digit_2_52 (And.intro digit_2_53 (And.intro digit_2_54 (And.intro digit_2_55 (And.intro digit_2_56 (And.intro digit_2_57 (And.intro digit_2_58 (And.intro digit_2_59 (And.intro digit_2_60 (And.intro digit_2_61 (And.intro digit_2_62 (And.intro digit_2_63 (And.intro digit_2_64 (And.intro digit_2_65 (And.intro digit_2_66 (And.intro digit_2_67 (And.intro digit_2_68 (And.intro digit_2_69 (And.intro digit_2_70 (And.intro digit_2_71 (And.intro digit_2_72 (And.intro digit_2_73 (And.intro digit_2_74 (And.intro digit_2_75 (And.intro digit_2_76 (And.intro digit_2_77 (And.intro digit_2_78 (And.intro digit_2_79 (And.intro digit_2_80 (And.intro digit_2_81 (And.intro digit_2_82 (And.intro digit_2_83 (And.intro digit_2_84 (And.intro digit_2_85 (And.intro digit_2_86 (And.intro digit_2_87 (And.intro digit_2_88 (And.intro digit_2_89 (And.intro digit_2_90 (And.intro digit_2_91 (And.intro digit_2_92 (And.intro digit_2_93 (And.intro digit_2_94 (And.intro digit_2_95 (And.intro digit_2_96 (And.intro digit_2_97 (And.intro digit_2_98 (And.intro digit_2_99 (And.intro digit_2_100 (And.intro digit_2_101 (And.intro digit_2_102 (And.intro digit_2_103 (And.intro digit_2_104 (And.intro digit_2_105 (And.intro digit_2_106 (And.intro digit_2_107 (And.intro digit_2_108 (And.intro digit_2_109 (And.intro digit_2_110 (And.intro digit_2_111 (And.intro digit_2_112 (And.intro digit_2_113 (And.intro digit_2_114 (And.intro digit_2_115 (And.intro digit_2_116 (And.intro digit_2_117 (And.intro digit_2_118 (And.intro digit_2_119 (And.intro digit_2_120 (And.intro digit_2_121 (And.intro digit_2_122 (And.intro digit_2_123 (And.intro digit_2_124 (And.intro digit_2_125 (And.intro digit_2_126 (And.intro digit_2_127 (And.intro digit_2_128 (And.intro digit_2_129 (And.intro digit_2_130 (And.intro digit_2_131 (And.intro digit_2_132 (And.intro digit_2_133 (And.intro digit_2_134 (And.intro digit_2_135 (And.intro digit_2_136 (And.intro digit_2_137 (And.intro digit_2_138 (And.intro digit_2_139 (And.intro digit_2_140 (And.intro digit_2_141 (And.intro digit_2_142 (And.intro digit_2_143 (And.intro digit_2_144 (And.intro digit_2_145 (And.intro digit_2_146 (And.intro digit_2_147 (And.intro digit_2_148 (And.intro digit_2_149 (And.intro digit_2_150 (And.intro digit_2_151 (And.intro digit_2_152 (And.intro digit_2_153 (And.intro digit_2_154 (And.intro digit_2_155 (And.intro digit_2_156 (And.intro digit_2_157 (And.intro digit_2_158 (And.intro digit_2_159 (And.intro digit_2_160 (And.intro digit_2_161 (And.intro digit_2_162 (And.intro digit_2_163 (And.intro digit_2_164 (And.intro digit_2_165 (And.intro digit_2_166 (And.intro digit_2_167 (And.intro digit_2_168 (And.intro digit_2_169 (And.intro digit_2_170 (And.intro digit_2_171 (And.intro digit_2_172 (And.intro digit_2_173 (And.intro digit_2_174 (And.intro digit_2_175 (And.intro digit_2_176 (And.intro digit_2_177 (And.intro digit_2_178 (And.intro digit_2_179 (And.intro digit_2_180 (And.intro digit_2_181 (And.intro digit_2_182 (And.intro digit_2_183 (And.intro digit_2_184 (And.intro digit_2_185 (And.intro digit_2_186 (And.intro digit_2_187 (And.intro digit_2_188 (And.intro digit_2_189 (And.intro digit_2_190 (And.intro digit_2_191 (And.intro digit_2_192 (And.intro digit_2_193 (And.intro digit_2_194 (And.intro digit_2_195 (And.intro digit_2_196 (And.intro digit_2_197 (And.intro digit_2_198 (And.intro digit_2_199 (And.intro digit_2_200 (And.intro digit_2_201 (And.intro digit_2_202 (And.intro digit_2_203 (And.intro digit_2_204 (And.intro digit_2_205 (And.intro digit_2_206 (And.intro digit_2_207 (And.intro digit_2_208 (And.intro digit_2_209 (And.intro digit_2_210 (And.intro digit_2_211 (And.intro digit_2_212 (And.intro digit_2_213 (And.intro digit_2_214 (And.intro digit_2_215 (And.intro digit_2_216 (And.intro digit_2_217 (And.intro digit_2_218 (And.intro digit_2_219 (And.intro digit_2_220 (And.intro digit_2_221 (And.intro digit_2_222 (And.intro digit_2_223 (And.intro digit_2_224 (And.intro digit_2_225 (And.intro digit_2_226 (And.intro digit_2_227 (And.intro digit_2_228 (And.intro digit_2_229 (And.intro digit_2_230 (And.intro digit_2_231 (And.intro digit_2_232 (And.intro digit_2_233 (And.intro digit_2_234 (And.intro digit_2_235 (And.intro digit_2_236 (And.intro digit_2_237 (And.intro digit_2_238 (And.intro digit_2_239 (And.intro digit_2_240 (And.intro digit_2_241 (And.intro digit_2_242 (And.intro digit_2_243 (And.intro digit_2_244 (And.intro digit_2_245 (And.intro digit_2_246 (And.intro digit_2_247 (And.intro digit_2_248 (And.intro digit_2_249 (And.intro digit_2_250 (And.intro digit_2_251 (And.intro digit_2_252 (And.intro digit_2_253 (And.intro digit_2_254 (And.intro digit_2_255 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem count_2_0 : Blocks.count [0, 0, 0] word_2 = 39 := by decide
theorem actualCount_2_0 : Blocks.enumeratedCount [0, 0, 0]
    (actualDigits 2 0 word_2.length) = 39 :=
  certified_count_sound digits_2 count_2_0
theorem occurrence_2_0 : occurrences 2 3 0 254 = 39 :=
  certified_occurrences_sound (b := 2) (value := 39)
    (text := word_2) (pattern := [0, 0, 0])
    (by decide) (by decide) (by decide) digits_2 count_2_0
theorem discrepancy_2_0 :
    Nat.dist (2^3 * occurrences 2 3 0 254) 254 = 58 := by
  rw [occurrence_2_0]
  decide
theorem count_2_1 : Blocks.count [0, 0, 1] word_2 = 34 := by decide
theorem actualCount_2_1 : Blocks.enumeratedCount [0, 0, 1]
    (actualDigits 2 0 word_2.length) = 34 :=
  certified_count_sound digits_2 count_2_1
theorem occurrence_2_1 : occurrences 2 3 1 254 = 34 :=
  certified_occurrences_sound (b := 2) (value := 34)
    (text := word_2) (pattern := [0, 0, 1])
    (by decide) (by decide) (by decide) digits_2 count_2_1
theorem discrepancy_2_1 :
    Nat.dist (2^3 * occurrences 2 3 1 254) 254 = 18 := by
  rw [occurrence_2_1]
  decide
theorem count_2_2 : Blocks.count [0, 1, 0] word_2 = 26 := by decide
theorem actualCount_2_2 : Blocks.enumeratedCount [0, 1, 0]
    (actualDigits 2 0 word_2.length) = 26 :=
  certified_count_sound digits_2 count_2_2
theorem occurrence_2_2 : occurrences 2 3 2 254 = 26 :=
  certified_occurrences_sound (b := 2) (value := 26)
    (text := word_2) (pattern := [0, 1, 0])
    (by decide) (by decide) (by decide) digits_2 count_2_2
theorem discrepancy_2_2 :
    Nat.dist (2^3 * occurrences 2 3 2 254) 254 = 46 := by
  rw [occurrence_2_2]
  decide
theorem count_2_3 : Blocks.count [0, 1, 1] word_2 = 31 := by decide
theorem actualCount_2_3 : Blocks.enumeratedCount [0, 1, 1]
    (actualDigits 2 0 word_2.length) = 31 :=
  certified_count_sound digits_2 count_2_3
theorem occurrence_2_3 : occurrences 2 3 3 254 = 31 :=
  certified_occurrences_sound (b := 2) (value := 31)
    (text := word_2) (pattern := [0, 1, 1])
    (by decide) (by decide) (by decide) digits_2 count_2_3
theorem discrepancy_2_3 :
    Nat.dist (2^3 * occurrences 2 3 3 254) 254 = 6 := by
  rw [occurrence_2_3]
  decide
theorem count_2_4 : Blocks.count [1, 0, 0] word_2 = 34 := by decide
theorem actualCount_2_4 : Blocks.enumeratedCount [1, 0, 0]
    (actualDigits 2 0 word_2.length) = 34 :=
  certified_count_sound digits_2 count_2_4
theorem occurrence_2_4 : occurrences 2 3 4 254 = 34 :=
  certified_occurrences_sound (b := 2) (value := 34)
    (text := word_2) (pattern := [1, 0, 0])
    (by decide) (by decide) (by decide) digits_2 count_2_4
theorem discrepancy_2_4 :
    Nat.dist (2^3 * occurrences 2 3 4 254) 254 = 18 := by
  rw [occurrence_2_4]
  decide
theorem count_2_5 : Blocks.count [1, 0, 1] word_2 = 24 := by decide
theorem actualCount_2_5 : Blocks.enumeratedCount [1, 0, 1]
    (actualDigits 2 0 word_2.length) = 24 :=
  certified_count_sound digits_2 count_2_5
theorem occurrence_2_5 : occurrences 2 3 5 254 = 24 :=
  certified_occurrences_sound (b := 2) (value := 24)
    (text := word_2) (pattern := [1, 0, 1])
    (by decide) (by decide) (by decide) digits_2 count_2_5
theorem discrepancy_2_5 :
    Nat.dist (2^3 * occurrences 2 3 5 254) 254 = 62 := by
  rw [occurrence_2_5]
  decide
theorem count_2_6 : Blocks.count [1, 1, 0] word_2 = 31 := by decide
theorem actualCount_2_6 : Blocks.enumeratedCount [1, 1, 0]
    (actualDigits 2 0 word_2.length) = 31 :=
  certified_count_sound digits_2 count_2_6
theorem occurrence_2_6 : occurrences 2 3 6 254 = 31 :=
  certified_occurrences_sound (b := 2) (value := 31)
    (text := word_2) (pattern := [1, 1, 0])
    (by decide) (by decide) (by decide) digits_2 count_2_6
theorem discrepancy_2_6 :
    Nat.dist (2^3 * occurrences 2 3 6 254) 254 = 6 := by
  rw [occurrence_2_6]
  decide
theorem count_2_7 : Blocks.count [1, 1, 1] word_2 = 35 := by decide
theorem actualCount_2_7 : Blocks.enumeratedCount [1, 1, 1]
    (actualDigits 2 0 word_2.length) = 35 :=
  certified_count_sound digits_2 count_2_7
theorem occurrence_2_7 : occurrences 2 3 7 254 = 35 :=
  certified_occurrences_sound (b := 2) (value := 35)
    (text := word_2) (pattern := [1, 1, 1])
    (by decide) (by decide) (by decide) digits_2 count_2_7
theorem discrepancy_2_7 :
    Nat.dist (2^3 * occurrences 2 3 7 254) 254 = 26 := by
  rw [occurrence_2_7]
  decide

def word_3 : List ℕ := [1, 2, 1, 2, 0, 0, 1, 1, 2, 2, 0, 2, 1, 2, 1, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 1, 1, 2, 2, 1, 0, 2, 1, 2, 0, 0, 2, 2, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 2, 2, 1, 1, 2, 0, 0, 2, 1, 0, 0, 0, 2, 1, 0, 0, 0, 1, 2, 0, 2, 1, 1, 1, 2, 2, 2, 0, 2, 2, 0, 0, 2, 0, 2, 1, 1, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 1, 0, 2, 1, 1, 1, 1, 2, 2, 0, 2, 0, 0, 1, 0, 1, 0, 2, 1, 2, 1, 2, 1]
theorem prefix_3_0 : PrefixCertificate (3^0) 0 := by decide
theorem prefix_3_1 : PrefixCertificate (3^1) 1 := by decide
theorem prefix_3_2 : PrefixCertificate (3^2) 5 := by decide
theorem prefix_3_3 : PrefixCertificate (3^3) 16 := by decide
theorem prefix_3_4 : PrefixCertificate (3^4) 50 := by decide
theorem prefix_3_5 : PrefixCertificate (3^5) 150 := by decide
theorem prefix_3_6 : PrefixCertificate (3^6) 450 := by decide
theorem prefix_3_7 : PrefixCertificate (3^7) 1351 := by decide
theorem prefix_3_8 : PrefixCertificate (3^8) 4054 := by decide
theorem prefix_3_9 : PrefixCertificate (3^9) 12164 := by decide
theorem prefix_3_10 : PrefixCertificate (3^10) 36494 := by decide
theorem prefix_3_11 : PrefixCertificate (3^11) 109482 := by decide
theorem prefix_3_12 : PrefixCertificate (3^12) 328448 := by decide
theorem prefix_3_13 : PrefixCertificate (3^13) 985345 := by decide
theorem prefix_3_14 : PrefixCertificate (3^14) 2956037 := by decide
theorem prefix_3_15 : PrefixCertificate (3^15) 8868112 := by decide
theorem prefix_3_16 : PrefixCertificate (3^16) 26604336 := by decide
theorem prefix_3_17 : PrefixCertificate (3^17) 79813010 := by decide
theorem prefix_3_18 : PrefixCertificate (3^18) 239439030 := by decide
theorem prefix_3_19 : PrefixCertificate (3^19) 718317090 := by decide
theorem prefix_3_20 : PrefixCertificate (3^20) 2154951271 := by decide
theorem prefix_3_21 : PrefixCertificate (3^21) 6464853813 := by decide
theorem prefix_3_22 : PrefixCertificate (3^22) 19394561441 := by decide
theorem prefix_3_23 : PrefixCertificate (3^23) 58183684324 := by decide
theorem prefix_3_24 : PrefixCertificate (3^24) 174551052972 := by decide
theorem prefix_3_25 : PrefixCertificate (3^25) 523653158916 := by decide
theorem prefix_3_26 : PrefixCertificate (3^26) 1570959476749 := by decide
theorem prefix_3_27 : PrefixCertificate (3^27) 4712878430247 := by decide
theorem prefix_3_28 : PrefixCertificate (3^28) 14138635290743 := by decide
theorem prefix_3_29 : PrefixCertificate (3^29) 42415905872229 := by decide
theorem prefix_3_30 : PrefixCertificate (3^30) 127247717616687 := by decide
theorem prefix_3_31 : PrefixCertificate (3^31) 381743152850062 := by decide
theorem prefix_3_32 : PrefixCertificate (3^32) 1145229458550186 := by decide
theorem prefix_3_33 : PrefixCertificate (3^33) 3435688375650560 := by decide
theorem prefix_3_34 : PrefixCertificate (3^34) 10307065126951680 := by decide
theorem prefix_3_35 : PrefixCertificate (3^35) 30921195380855041 := by decide
theorem prefix_3_36 : PrefixCertificate (3^36) 92763586142565124 := by decide
theorem prefix_3_37 : PrefixCertificate (3^37) 278290758427695374 := by decide
theorem prefix_3_38 : PrefixCertificate (3^38) 834872275283086124 := by decide
theorem prefix_3_39 : PrefixCertificate (3^39) 2504616825849258373 := by decide
theorem prefix_3_40 : PrefixCertificate (3^40) 7513850477547775119 := by decide
theorem prefix_3_41 : PrefixCertificate (3^41) 22541551432643325359 := by decide
theorem prefix_3_42 : PrefixCertificate (3^42) 67624654297929976078 := by decide
theorem prefix_3_43 : PrefixCertificate (3^43) 202873962893789928236 := by decide
theorem prefix_3_44 : PrefixCertificate (3^44) 608621888681369784708 := by decide
theorem prefix_3_45 : PrefixCertificate (3^45) 1825865666044109354124 := by decide
theorem prefix_3_46 : PrefixCertificate (3^46) 5477596998132328062374 := by decide
theorem prefix_3_47 : PrefixCertificate (3^47) 16432790994396984187124 := by decide
theorem prefix_3_48 : PrefixCertificate (3^48) 49298372983190952561373 := by decide
theorem prefix_3_49 : PrefixCertificate (3^49) 147895118949572857684120 := by decide
theorem prefix_3_50 : PrefixCertificate (3^50) 443685356848718573052361 := by decide
theorem prefix_3_51 : PrefixCertificate (3^51) 1331056070546155719157083 := by decide
theorem prefix_3_52 : PrefixCertificate (3^52) 3993168211638467157471250 := by decide
theorem prefix_3_53 : PrefixCertificate (3^53) 11979504634915401472413751 := by decide
theorem prefix_3_54 : PrefixCertificate (3^54) 35938513904746204417241253 := by decide
theorem prefix_3_55 : PrefixCertificate (3^55) 107815541714238613251723759 := by decide
theorem prefix_3_56 : PrefixCertificate (3^56) 323446625142715839755171278 := by decide
theorem prefix_3_57 : PrefixCertificate (3^57) 970339875428147519265513834 := by decide
theorem prefix_3_58 : PrefixCertificate (3^58) 2911019626284442557796541503 := by decide
theorem prefix_3_59 : PrefixCertificate (3^59) 8733058878853327673389624511 := by decide
theorem prefix_3_60 : PrefixCertificate (3^60) 26199176636559983020168873535 := by decide
theorem prefix_3_61 : PrefixCertificate (3^61) 78597529909679949060506620606 := by decide
theorem prefix_3_62 : PrefixCertificate (3^62) 235792589729039847181519861819 := by decide
theorem prefix_3_63 : PrefixCertificate (3^63) 707377769187119541544559585459 := by decide
theorem prefix_3_64 : PrefixCertificate (3^64) 2122133307561358624633678756377 := by decide
theorem prefix_3_65 : PrefixCertificate (3^65) 6366399922684075873901036269131 := by decide
theorem prefix_3_66 : PrefixCertificate (3^66) 19099199768052227621703108807395 := by decide
theorem prefix_3_67 : PrefixCertificate (3^67) 57297599304156682865109326422186 := by decide
theorem prefix_3_68 : PrefixCertificate (3^68) 171892797912470048595327979266558 := by decide
theorem prefix_3_69 : PrefixCertificate (3^69) 515678393737410145785983937799674 := by decide
theorem prefix_3_70 : PrefixCertificate (3^70) 1547035181212230437357951813399022 := by decide
theorem prefix_3_71 : PrefixCertificate (3^71) 4641105543636691312073855440197068 := by decide
theorem prefix_3_72 : PrefixCertificate (3^72) 13923316630910073936221566320591205 := by decide
theorem prefix_3_73 : PrefixCertificate (3^73) 41769949892730221808664698961773615 := by decide
theorem prefix_3_74 : PrefixCertificate (3^74) 125309849678190665425994096885320845 := by decide
theorem prefix_3_75 : PrefixCertificate (3^75) 375929549034571996277982290655962535 := by decide
theorem prefix_3_76 : PrefixCertificate (3^76) 1127788647103715988833946871967887606 := by decide
theorem prefix_3_77 : PrefixCertificate (3^77) 3383365941311147966501840615903662820 := by decide
theorem prefix_3_78 : PrefixCertificate (3^78) 10150097823933443899505521847710988460 := by decide
theorem prefix_3_79 : PrefixCertificate (3^79) 30450293471800331698516565543132965382 := by decide
theorem prefix_3_80 : PrefixCertificate (3^80) 91350880415400995095549696629398896147 := by decide
theorem prefix_3_81 : PrefixCertificate (3^81) 274052641246202985286649089888196688442 := by decide
theorem prefix_3_82 : PrefixCertificate (3^82) 822157923738608955859947269664590065327 := by decide
theorem prefix_3_83 : PrefixCertificate (3^83) 2466473771215826867579841808993770195983 := by decide
theorem prefix_3_84 : PrefixCertificate (3^84) 7399421313647480602739525426981310587951 := by decide
theorem prefix_3_85 : PrefixCertificate (3^85) 22198263940942441808218576280943931763855 := by decide
theorem prefix_3_86 : PrefixCertificate (3^86) 66594791822827325424655728842831795291565 := by decide
theorem prefix_3_87 : PrefixCertificate (3^87) 199784375468481976273967186528495385874697 := by decide
theorem prefix_3_88 : PrefixCertificate (3^88) 599353126405445928821901559585486157624093 := by decide
theorem prefix_3_89 : PrefixCertificate (3^89) 1798059379216337786465704678756458472872279 := by decide
theorem prefix_3_90 : PrefixCertificate (3^90) 5394178137649013359397114036269375418616837 := by decide
theorem prefix_3_91 : PrefixCertificate (3^91) 16182534412947040078191342108808126255850513 := by decide
theorem prefix_3_92 : PrefixCertificate (3^92) 48547603238841120234574026326424378767551539 := by decide
theorem prefix_3_93 : PrefixCertificate (3^93) 145642809716523360703722078979273136302654619 := by decide
theorem prefix_3_94 : PrefixCertificate (3^94) 436928429149570082111166236937819408907963858 := by decide
theorem prefix_3_95 : PrefixCertificate (3^95) 1310785287448710246333498710813458226723891575 := by decide
theorem prefix_3_96 : PrefixCertificate (3^96) 3932355862346130739000496132440374680171674725 := by decide
theorem prefix_3_97 : PrefixCertificate (3^97) 11797067587038392217001488397321124040515024177 := by decide
theorem prefix_3_98 : PrefixCertificate (3^98) 35391202761115176651004465191963372121545072533 := by decide
theorem prefix_3_99 : PrefixCertificate (3^99) 106173608283345529953013395575890116364635217600 := by decide
theorem prefix_3_100 : PrefixCertificate (3^100) 318520824850036589859040186727670349093905652800 := by decide
theorem prefix_3_101 : PrefixCertificate (3^101) 955562474550109769577120560183011047281716958400 := by decide
theorem prefix_3_102 : PrefixCertificate (3^102) 2866687423650329308731361680549033141845150875200 := by decide
theorem prefix_3_103 : PrefixCertificate (3^103) 8600062270950987926194085041647099425535452625601 := by decide
theorem prefix_3_104 : PrefixCertificate (3^104) 25800186812852963778582255124941298276606357876803 := by decide
theorem prefix_3_105 : PrefixCertificate (3^105) 77400560438558891335746765374823894829819073630409 := by decide
theorem prefix_3_106 : PrefixCertificate (3^106) 232201681315676674007240296124471684489457220891228 := by decide
theorem prefix_3_107 : PrefixCertificate (3^107) 696605043947030022021720888373415053468371662673684 := by decide
theorem prefix_3_108 : PrefixCertificate (3^108) 2089815131841090066065162665120245160405114988021054 := by decide
theorem prefix_3_109 : PrefixCertificate (3^109) 6269445395523270198195487995360735481215344964063163 := by decide
theorem prefix_3_110 : PrefixCertificate (3^110) 18808336186569810594586463986082206443646034892189490 := by decide
theorem prefix_3_111 : PrefixCertificate (3^111) 56425008559709431783759391958246619330938104676568471 := by decide
theorem prefix_3_112 : PrefixCertificate (3^112) 169275025679128295351278175874739857992814314029705414 := by decide
theorem prefix_3_113 : PrefixCertificate (3^113) 507825077037384886053834527624219573978442942089116244 := by decide
theorem prefix_3_114 : PrefixCertificate (3^114) 1523475231112154658161503582872658721935328826267348734 := by decide
theorem prefix_3_115 : PrefixCertificate (3^115) 4570425693336463974484510748617976165805986478802046202 := by decide
theorem prefix_3_116 : PrefixCertificate (3^116) 13711277080009391923453532245853928497417959436406138608 := by decide
theorem prefix_3_117 : PrefixCertificate (3^117) 41133831240028175770360596737561785492253878309218415824 := by decide
theorem prefix_3_118 : PrefixCertificate (3^118) 123401493720084527311081790212685356476761634927655247472 := by decide
theorem prefix_3_119 : PrefixCertificate (3^119) 370204481160253581933245370638056069430284904782965742417 := by decide
theorem prefix_3_120 : PrefixCertificate (3^120) 1110613443480760745799736111914168208290854714348897227251 := by decide
theorem prefix_3_121 : PrefixCertificate (3^121) 3331840330442282237399208335742504624872564143046691681754 := by decide
theorem prefix_3_122 : PrefixCertificate (3^122) 9995520991326846712197625007227513874617692429140075045262 := by decide
theorem prefix_3_123 : PrefixCertificate (3^123) 29986562973980540136592875021682541623853077287420225135788 := by decide
theorem prefix_3_124 : PrefixCertificate (3^124) 89959688921941620409778625065047624871559231862260675407365 := by decide
theorem prefix_3_125 : PrefixCertificate (3^125) 269879066765824861229335875195142874614677695586782026222097 := by decide
theorem prefix_3_126 : PrefixCertificate (3^126) 809637200297474583688007625585428623844033086760346078666292 := by decide
theorem prefix_3_127 : PrefixCertificate (3^127) 2428911600892423751064022876756285871532099260281038235998878 := by decide
theorem prefix_3_128 : PrefixCertificate (3^128) 7286734802677271253192068630268857614596297780843114707996635 := by decide
theorem digit_3_0 : digit 3 0 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_0 prefix_3_1
theorem digit_3_1 : digit 3 1 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_1 prefix_3_2
theorem digit_3_2 : digit 3 2 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_2 prefix_3_3
theorem digit_3_3 : digit 3 3 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_3 prefix_3_4
theorem digit_3_4 : digit 3 4 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_4 prefix_3_5
theorem digit_3_5 : digit 3 5 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_5 prefix_3_6
theorem digit_3_6 : digit 3 6 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_6 prefix_3_7
theorem digit_3_7 : digit 3 7 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_7 prefix_3_8
theorem digit_3_8 : digit 3 8 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_8 prefix_3_9
theorem digit_3_9 : digit 3 9 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_9 prefix_3_10
theorem digit_3_10 : digit 3 10 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_10 prefix_3_11
theorem digit_3_11 : digit 3 11 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_11 prefix_3_12
theorem digit_3_12 : digit 3 12 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_12 prefix_3_13
theorem digit_3_13 : digit 3 13 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_13 prefix_3_14
theorem digit_3_14 : digit 3 14 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_14 prefix_3_15
theorem digit_3_15 : digit 3 15 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_15 prefix_3_16
theorem digit_3_16 : digit 3 16 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_16 prefix_3_17
theorem digit_3_17 : digit 3 17 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_17 prefix_3_18
theorem digit_3_18 : digit 3 18 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_18 prefix_3_19
theorem digit_3_19 : digit 3 19 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_19 prefix_3_20
theorem digit_3_20 : digit 3 20 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_20 prefix_3_21
theorem digit_3_21 : digit 3 21 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_21 prefix_3_22
theorem digit_3_22 : digit 3 22 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_22 prefix_3_23
theorem digit_3_23 : digit 3 23 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_23 prefix_3_24
theorem digit_3_24 : digit 3 24 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_24 prefix_3_25
theorem digit_3_25 : digit 3 25 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_25 prefix_3_26
theorem digit_3_26 : digit 3 26 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_26 prefix_3_27
theorem digit_3_27 : digit 3 27 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_27 prefix_3_28
theorem digit_3_28 : digit 3 28 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_28 prefix_3_29
theorem digit_3_29 : digit 3 29 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_29 prefix_3_30
theorem digit_3_30 : digit 3 30 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_30 prefix_3_31
theorem digit_3_31 : digit 3 31 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_31 prefix_3_32
theorem digit_3_32 : digit 3 32 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_32 prefix_3_33
theorem digit_3_33 : digit 3 33 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_33 prefix_3_34
theorem digit_3_34 : digit 3 34 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_34 prefix_3_35
theorem digit_3_35 : digit 3 35 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_35 prefix_3_36
theorem digit_3_36 : digit 3 36 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_36 prefix_3_37
theorem digit_3_37 : digit 3 37 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_37 prefix_3_38
theorem digit_3_38 : digit 3 38 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_38 prefix_3_39
theorem digit_3_39 : digit 3 39 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_39 prefix_3_40
theorem digit_3_40 : digit 3 40 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_40 prefix_3_41
theorem digit_3_41 : digit 3 41 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_41 prefix_3_42
theorem digit_3_42 : digit 3 42 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_42 prefix_3_43
theorem digit_3_43 : digit 3 43 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_43 prefix_3_44
theorem digit_3_44 : digit 3 44 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_44 prefix_3_45
theorem digit_3_45 : digit 3 45 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_45 prefix_3_46
theorem digit_3_46 : digit 3 46 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_46 prefix_3_47
theorem digit_3_47 : digit 3 47 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_47 prefix_3_48
theorem digit_3_48 : digit 3 48 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_48 prefix_3_49
theorem digit_3_49 : digit 3 49 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_49 prefix_3_50
theorem digit_3_50 : digit 3 50 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_50 prefix_3_51
theorem digit_3_51 : digit 3 51 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_51 prefix_3_52
theorem digit_3_52 : digit 3 52 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_52 prefix_3_53
theorem digit_3_53 : digit 3 53 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_53 prefix_3_54
theorem digit_3_54 : digit 3 54 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_54 prefix_3_55
theorem digit_3_55 : digit 3 55 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_55 prefix_3_56
theorem digit_3_56 : digit 3 56 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_56 prefix_3_57
theorem digit_3_57 : digit 3 57 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_57 prefix_3_58
theorem digit_3_58 : digit 3 58 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_58 prefix_3_59
theorem digit_3_59 : digit 3 59 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_59 prefix_3_60
theorem digit_3_60 : digit 3 60 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_60 prefix_3_61
theorem digit_3_61 : digit 3 61 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_61 prefix_3_62
theorem digit_3_62 : digit 3 62 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_62 prefix_3_63
theorem digit_3_63 : digit 3 63 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_63 prefix_3_64
theorem digit_3_64 : digit 3 64 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_64 prefix_3_65
theorem digit_3_65 : digit 3 65 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_65 prefix_3_66
theorem digit_3_66 : digit 3 66 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_66 prefix_3_67
theorem digit_3_67 : digit 3 67 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_67 prefix_3_68
theorem digit_3_68 : digit 3 68 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_68 prefix_3_69
theorem digit_3_69 : digit 3 69 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_69 prefix_3_70
theorem digit_3_70 : digit 3 70 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_70 prefix_3_71
theorem digit_3_71 : digit 3 71 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_71 prefix_3_72
theorem digit_3_72 : digit 3 72 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_72 prefix_3_73
theorem digit_3_73 : digit 3 73 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_73 prefix_3_74
theorem digit_3_74 : digit 3 74 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_74 prefix_3_75
theorem digit_3_75 : digit 3 75 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_75 prefix_3_76
theorem digit_3_76 : digit 3 76 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_76 prefix_3_77
theorem digit_3_77 : digit 3 77 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_77 prefix_3_78
theorem digit_3_78 : digit 3 78 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_78 prefix_3_79
theorem digit_3_79 : digit 3 79 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_79 prefix_3_80
theorem digit_3_80 : digit 3 80 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_80 prefix_3_81
theorem digit_3_81 : digit 3 81 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_81 prefix_3_82
theorem digit_3_82 : digit 3 82 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_82 prefix_3_83
theorem digit_3_83 : digit 3 83 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_83 prefix_3_84
theorem digit_3_84 : digit 3 84 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_84 prefix_3_85
theorem digit_3_85 : digit 3 85 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_85 prefix_3_86
theorem digit_3_86 : digit 3 86 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_86 prefix_3_87
theorem digit_3_87 : digit 3 87 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_87 prefix_3_88
theorem digit_3_88 : digit 3 88 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_88 prefix_3_89
theorem digit_3_89 : digit 3 89 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_89 prefix_3_90
theorem digit_3_90 : digit 3 90 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_90 prefix_3_91
theorem digit_3_91 : digit 3 91 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_91 prefix_3_92
theorem digit_3_92 : digit 3 92 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_92 prefix_3_93
theorem digit_3_93 : digit 3 93 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_93 prefix_3_94
theorem digit_3_94 : digit 3 94 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_94 prefix_3_95
theorem digit_3_95 : digit 3 95 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_95 prefix_3_96
theorem digit_3_96 : digit 3 96 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_96 prefix_3_97
theorem digit_3_97 : digit 3 97 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_97 prefix_3_98
theorem digit_3_98 : digit 3 98 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_98 prefix_3_99
theorem digit_3_99 : digit 3 99 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_99 prefix_3_100
theorem digit_3_100 : digit 3 100 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_100 prefix_3_101
theorem digit_3_101 : digit 3 101 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_101 prefix_3_102
theorem digit_3_102 : digit 3 102 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_102 prefix_3_103
theorem digit_3_103 : digit 3 103 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_103 prefix_3_104
theorem digit_3_104 : digit 3 104 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_104 prefix_3_105
theorem digit_3_105 : digit 3 105 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_105 prefix_3_106
theorem digit_3_106 : digit 3 106 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_106 prefix_3_107
theorem digit_3_107 : digit 3 107 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_107 prefix_3_108
theorem digit_3_108 : digit 3 108 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_108 prefix_3_109
theorem digit_3_109 : digit 3 109 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_109 prefix_3_110
theorem digit_3_110 : digit 3 110 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_110 prefix_3_111
theorem digit_3_111 : digit 3 111 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_111 prefix_3_112
theorem digit_3_112 : digit 3 112 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_112 prefix_3_113
theorem digit_3_113 : digit 3 113 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_113 prefix_3_114
theorem digit_3_114 : digit 3 114 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_114 prefix_3_115
theorem digit_3_115 : digit 3 115 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_115 prefix_3_116
theorem digit_3_116 : digit 3 116 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_116 prefix_3_117
theorem digit_3_117 : digit 3 117 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_117 prefix_3_118
theorem digit_3_118 : digit 3 118 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_118 prefix_3_119
theorem digit_3_119 : digit 3 119 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_119 prefix_3_120
theorem digit_3_120 : digit 3 120 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_120 prefix_3_121
theorem digit_3_121 : digit 3 121 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_121 prefix_3_122
theorem digit_3_122 : digit 3 122 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_122 prefix_3_123
theorem digit_3_123 : digit 3 123 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_123 prefix_3_124
theorem digit_3_124 : digit 3 124 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_124 prefix_3_125
theorem digit_3_125 : digit 3 125 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_125 prefix_3_126
theorem digit_3_126 : digit 3 126 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_126 prefix_3_127
theorem digit_3_127 : digit 3 127 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_3_127 prefix_3_128
theorem digits_3 : DigitsAt 3 0 word_3 := And.intro digit_3_0 (And.intro digit_3_1 (And.intro digit_3_2 (And.intro digit_3_3 (And.intro digit_3_4 (And.intro digit_3_5 (And.intro digit_3_6 (And.intro digit_3_7 (And.intro digit_3_8 (And.intro digit_3_9 (And.intro digit_3_10 (And.intro digit_3_11 (And.intro digit_3_12 (And.intro digit_3_13 (And.intro digit_3_14 (And.intro digit_3_15 (And.intro digit_3_16 (And.intro digit_3_17 (And.intro digit_3_18 (And.intro digit_3_19 (And.intro digit_3_20 (And.intro digit_3_21 (And.intro digit_3_22 (And.intro digit_3_23 (And.intro digit_3_24 (And.intro digit_3_25 (And.intro digit_3_26 (And.intro digit_3_27 (And.intro digit_3_28 (And.intro digit_3_29 (And.intro digit_3_30 (And.intro digit_3_31 (And.intro digit_3_32 (And.intro digit_3_33 (And.intro digit_3_34 (And.intro digit_3_35 (And.intro digit_3_36 (And.intro digit_3_37 (And.intro digit_3_38 (And.intro digit_3_39 (And.intro digit_3_40 (And.intro digit_3_41 (And.intro digit_3_42 (And.intro digit_3_43 (And.intro digit_3_44 (And.intro digit_3_45 (And.intro digit_3_46 (And.intro digit_3_47 (And.intro digit_3_48 (And.intro digit_3_49 (And.intro digit_3_50 (And.intro digit_3_51 (And.intro digit_3_52 (And.intro digit_3_53 (And.intro digit_3_54 (And.intro digit_3_55 (And.intro digit_3_56 (And.intro digit_3_57 (And.intro digit_3_58 (And.intro digit_3_59 (And.intro digit_3_60 (And.intro digit_3_61 (And.intro digit_3_62 (And.intro digit_3_63 (And.intro digit_3_64 (And.intro digit_3_65 (And.intro digit_3_66 (And.intro digit_3_67 (And.intro digit_3_68 (And.intro digit_3_69 (And.intro digit_3_70 (And.intro digit_3_71 (And.intro digit_3_72 (And.intro digit_3_73 (And.intro digit_3_74 (And.intro digit_3_75 (And.intro digit_3_76 (And.intro digit_3_77 (And.intro digit_3_78 (And.intro digit_3_79 (And.intro digit_3_80 (And.intro digit_3_81 (And.intro digit_3_82 (And.intro digit_3_83 (And.intro digit_3_84 (And.intro digit_3_85 (And.intro digit_3_86 (And.intro digit_3_87 (And.intro digit_3_88 (And.intro digit_3_89 (And.intro digit_3_90 (And.intro digit_3_91 (And.intro digit_3_92 (And.intro digit_3_93 (And.intro digit_3_94 (And.intro digit_3_95 (And.intro digit_3_96 (And.intro digit_3_97 (And.intro digit_3_98 (And.intro digit_3_99 (And.intro digit_3_100 (And.intro digit_3_101 (And.intro digit_3_102 (And.intro digit_3_103 (And.intro digit_3_104 (And.intro digit_3_105 (And.intro digit_3_106 (And.intro digit_3_107 (And.intro digit_3_108 (And.intro digit_3_109 (And.intro digit_3_110 (And.intro digit_3_111 (And.intro digit_3_112 (And.intro digit_3_113 (And.intro digit_3_114 (And.intro digit_3_115 (And.intro digit_3_116 (And.intro digit_3_117 (And.intro digit_3_118 (And.intro digit_3_119 (And.intro digit_3_120 (And.intro digit_3_121 (And.intro digit_3_122 (And.intro digit_3_123 (And.intro digit_3_124 (And.intro digit_3_125 (And.intro digit_3_126 (And.intro digit_3_127 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem count_3_0 : Blocks.count [0, 0, 0] word_3 = 3 := by decide
theorem actualCount_3_0 : Blocks.enumeratedCount [0, 0, 0]
    (actualDigits 3 0 word_3.length) = 3 :=
  certified_count_sound digits_3 count_3_0
theorem occurrence_3_0 : occurrences 3 3 0 126 = 3 :=
  certified_occurrences_sound (b := 3) (value := 3)
    (text := word_3) (pattern := [0, 0, 0])
    (by decide) (by decide) (by decide) digits_3 count_3_0
theorem discrepancy_3_0 :
    Nat.dist (3^3 * occurrences 3 3 0 126) 126 = 45 := by
  rw [occurrence_3_0]
  decide
theorem count_3_1 : Blocks.count [0, 0, 1] word_3 = 9 := by decide
theorem actualCount_3_1 : Blocks.enumeratedCount [0, 0, 1]
    (actualDigits 3 0 word_3.length) = 9 :=
  certified_count_sound digits_3 count_3_1
theorem occurrence_3_1 : occurrences 3 3 1 126 = 9 :=
  certified_occurrences_sound (b := 3) (value := 9)
    (text := word_3) (pattern := [0, 0, 1])
    (by decide) (by decide) (by decide) digits_3 count_3_1
theorem discrepancy_3_1 :
    Nat.dist (3^3 * occurrences 3 3 1 126) 126 = 117 := by
  rw [occurrence_3_1]
  decide
theorem count_3_2 : Blocks.count [0, 0, 2] word_3 = 4 := by decide
theorem actualCount_3_2 : Blocks.enumeratedCount [0, 0, 2]
    (actualDigits 3 0 word_3.length) = 4 :=
  certified_count_sound digits_3 count_3_2
theorem occurrence_3_2 : occurrences 3 3 2 126 = 4 :=
  certified_occurrences_sound (b := 3) (value := 4)
    (text := word_3) (pattern := [0, 0, 2])
    (by decide) (by decide) (by decide) digits_3 count_3_2
theorem discrepancy_3_2 :
    Nat.dist (3^3 * occurrences 3 3 2 126) 126 = 18 := by
  rw [occurrence_3_2]
  decide
theorem count_3_3 : Blocks.count [0, 1, 0] word_3 = 8 := by decide
theorem actualCount_3_3 : Blocks.enumeratedCount [0, 1, 0]
    (actualDigits 3 0 word_3.length) = 8 :=
  certified_count_sound digits_3 count_3_3
theorem occurrence_3_3 : occurrences 3 3 3 126 = 8 :=
  certified_occurrences_sound (b := 3) (value := 8)
    (text := word_3) (pattern := [0, 1, 0])
    (by decide) (by decide) (by decide) digits_3 count_3_3
theorem discrepancy_3_3 :
    Nat.dist (3^3 * occurrences 3 3 3 126) 126 = 90 := by
  rw [occurrence_3_3]
  decide
theorem count_3_4 : Blocks.count [0, 1, 1] word_3 = 3 := by decide
theorem actualCount_3_4 : Blocks.enumeratedCount [0, 1, 1]
    (actualDigits 3 0 word_3.length) = 3 :=
  certified_count_sound digits_3 count_3_4
theorem occurrence_3_4 : occurrences 3 3 4 126 = 3 :=
  certified_occurrences_sound (b := 3) (value := 3)
    (text := word_3) (pattern := [0, 1, 1])
    (by decide) (by decide) (by decide) digits_3 count_3_4
theorem discrepancy_3_4 :
    Nat.dist (3^3 * occurrences 3 3 4 126) 126 = 45 := by
  rw [occurrence_3_4]
  decide
theorem count_3_5 : Blocks.count [0, 1, 2] word_3 = 2 := by decide
theorem actualCount_3_5 : Blocks.enumeratedCount [0, 1, 2]
    (actualDigits 3 0 word_3.length) = 2 :=
  certified_count_sound digits_3 count_3_5
theorem occurrence_3_5 : occurrences 3 3 5 126 = 2 :=
  certified_occurrences_sound (b := 3) (value := 2)
    (text := word_3) (pattern := [0, 1, 2])
    (by decide) (by decide) (by decide) digits_3 count_3_5
theorem discrepancy_3_5 :
    Nat.dist (3^3 * occurrences 3 3 5 126) 126 = 72 := by
  rw [occurrence_3_5]
  decide
theorem count_3_6 : Blocks.count [0, 2, 0] word_3 = 5 := by decide
theorem actualCount_3_6 : Blocks.enumeratedCount [0, 2, 0]
    (actualDigits 3 0 word_3.length) = 5 :=
  certified_count_sound digits_3 count_3_6
theorem occurrence_3_6 : occurrences 3 3 6 126 = 5 :=
  certified_occurrences_sound (b := 3) (value := 5)
    (text := word_3) (pattern := [0, 2, 0])
    (by decide) (by decide) (by decide) digits_3 count_3_6
theorem discrepancy_3_6 :
    Nat.dist (3^3 * occurrences 3 3 6 126) 126 = 9 := by
  rw [occurrence_3_6]
  decide
theorem count_3_7 : Blocks.count [0, 2, 1] word_3 = 9 := by decide
theorem actualCount_3_7 : Blocks.enumeratedCount [0, 2, 1]
    (actualDigits 3 0 word_3.length) = 9 :=
  certified_count_sound digits_3 count_3_7
theorem occurrence_3_7 : occurrences 3 3 7 126 = 9 :=
  certified_occurrences_sound (b := 3) (value := 9)
    (text := word_3) (pattern := [0, 2, 1])
    (by decide) (by decide) (by decide) digits_3 count_3_7
theorem discrepancy_3_7 :
    Nat.dist (3^3 * occurrences 3 3 7 126) 126 = 117 := by
  rw [occurrence_3_7]
  decide
theorem count_3_8 : Blocks.count [0, 2, 2] word_3 = 3 := by decide
theorem actualCount_3_8 : Blocks.enumeratedCount [0, 2, 2]
    (actualDigits 3 0 word_3.length) = 3 :=
  certified_count_sound digits_3 count_3_8
theorem occurrence_3_8 : occurrences 3 3 8 126 = 3 :=
  certified_occurrences_sound (b := 3) (value := 3)
    (text := word_3) (pattern := [0, 2, 2])
    (by decide) (by decide) (by decide) digits_3 count_3_8
theorem discrepancy_3_8 :
    Nat.dist (3^3 * occurrences 3 3 8 126) 126 = 45 := by
  rw [occurrence_3_8]
  decide
theorem count_3_9 : Blocks.count [1, 0, 0] word_3 = 6 := by decide
theorem actualCount_3_9 : Blocks.enumeratedCount [1, 0, 0]
    (actualDigits 3 0 word_3.length) = 6 :=
  certified_count_sound digits_3 count_3_9
theorem occurrence_3_9 : occurrences 3 3 9 126 = 6 :=
  certified_occurrences_sound (b := 3) (value := 6)
    (text := word_3) (pattern := [1, 0, 0])
    (by decide) (by decide) (by decide) digits_3 count_3_9
theorem discrepancy_3_9 :
    Nat.dist (3^3 * occurrences 3 3 9 126) 126 = 36 := by
  rw [occurrence_3_9]
  decide
theorem count_3_10 : Blocks.count [1, 0, 1] word_3 = 3 := by decide
theorem actualCount_3_10 : Blocks.enumeratedCount [1, 0, 1]
    (actualDigits 3 0 word_3.length) = 3 :=
  certified_count_sound digits_3 count_3_10
theorem occurrence_3_10 : occurrences 3 3 10 126 = 3 :=
  certified_occurrences_sound (b := 3) (value := 3)
    (text := word_3) (pattern := [1, 0, 1])
    (by decide) (by decide) (by decide) digits_3 count_3_10
theorem discrepancy_3_10 :
    Nat.dist (3^3 * occurrences 3 3 10 126) 126 = 45 := by
  rw [occurrence_3_10]
  decide
theorem count_3_11 : Blocks.count [1, 0, 2] word_3 = 8 := by decide
theorem actualCount_3_11 : Blocks.enumeratedCount [1, 0, 2]
    (actualDigits 3 0 word_3.length) = 8 :=
  certified_count_sound digits_3 count_3_11
theorem occurrence_3_11 : occurrences 3 3 11 126 = 8 :=
  certified_occurrences_sound (b := 3) (value := 8)
    (text := word_3) (pattern := [1, 0, 2])
    (by decide) (by decide) (by decide) digits_3 count_3_11
theorem discrepancy_3_11 :
    Nat.dist (3^3 * occurrences 3 3 11 126) 126 = 90 := by
  rw [occurrence_3_11]
  decide
theorem count_3_12 : Blocks.count [1, 1, 0] word_3 = 3 := by decide
theorem actualCount_3_12 : Blocks.enumeratedCount [1, 1, 0]
    (actualDigits 3 0 word_3.length) = 3 :=
  certified_count_sound digits_3 count_3_12
theorem occurrence_3_12 : occurrences 3 3 12 126 = 3 :=
  certified_occurrences_sound (b := 3) (value := 3)
    (text := word_3) (pattern := [1, 1, 0])
    (by decide) (by decide) (by decide) digits_3 count_3_12
theorem discrepancy_3_12 :
    Nat.dist (3^3 * occurrences 3 3 12 126) 126 = 45 := by
  rw [occurrence_3_12]
  decide
theorem count_3_13 : Blocks.count [1, 1, 1] word_3 = 4 := by decide
theorem actualCount_3_13 : Blocks.enumeratedCount [1, 1, 1]
    (actualDigits 3 0 word_3.length) = 4 :=
  certified_count_sound digits_3 count_3_13
theorem occurrence_3_13 : occurrences 3 3 13 126 = 4 :=
  certified_occurrences_sound (b := 3) (value := 4)
    (text := word_3) (pattern := [1, 1, 1])
    (by decide) (by decide) (by decide) digits_3 count_3_13
theorem discrepancy_3_13 :
    Nat.dist (3^3 * occurrences 3 3 13 126) 126 = 18 := by
  rw [occurrence_3_13]
  decide
theorem count_3_14 : Blocks.count [1, 1, 2] word_3 = 5 := by decide
theorem actualCount_3_14 : Blocks.enumeratedCount [1, 1, 2]
    (actualDigits 3 0 word_3.length) = 5 :=
  certified_count_sound digits_3 count_3_14
theorem occurrence_3_14 : occurrences 3 3 14 126 = 5 :=
  certified_occurrences_sound (b := 3) (value := 5)
    (text := word_3) (pattern := [1, 1, 2])
    (by decide) (by decide) (by decide) digits_3 count_3_14
theorem discrepancy_3_14 :
    Nat.dist (3^3 * occurrences 3 3 14 126) 126 = 9 := by
  rw [occurrence_3_14]
  decide
theorem count_3_15 : Blocks.count [1, 2, 0] word_3 = 4 := by decide
theorem actualCount_3_15 : Blocks.enumeratedCount [1, 2, 0]
    (actualDigits 3 0 word_3.length) = 4 :=
  certified_count_sound digits_3 count_3_15
theorem occurrence_3_15 : occurrences 3 3 15 126 = 4 :=
  certified_occurrences_sound (b := 3) (value := 4)
    (text := word_3) (pattern := [1, 2, 0])
    (by decide) (by decide) (by decide) digits_3 count_3_15
theorem discrepancy_3_15 :
    Nat.dist (3^3 * occurrences 3 3 15 126) 126 = 18 := by
  rw [occurrence_3_15]
  decide
theorem count_3_16 : Blocks.count [1, 2, 1] word_3 = 4 := by decide
theorem actualCount_3_16 : Blocks.enumeratedCount [1, 2, 1]
    (actualDigits 3 0 word_3.length) = 4 :=
  certified_count_sound digits_3 count_3_16
theorem occurrence_3_16 : occurrences 3 3 16 126 = 4 :=
  certified_occurrences_sound (b := 3) (value := 4)
    (text := word_3) (pattern := [1, 2, 1])
    (by decide) (by decide) (by decide) digits_3 count_3_16
theorem discrepancy_3_16 :
    Nat.dist (3^3 * occurrences 3 3 16 126) 126 = 18 := by
  rw [occurrence_3_16]
  decide
theorem count_3_17 : Blocks.count [1, 2, 2] word_3 = 5 := by decide
theorem actualCount_3_17 : Blocks.enumeratedCount [1, 2, 2]
    (actualDigits 3 0 word_3.length) = 5 :=
  certified_count_sound digits_3 count_3_17
theorem occurrence_3_17 : occurrences 3 3 17 126 = 5 :=
  certified_occurrences_sound (b := 3) (value := 5)
    (text := word_3) (pattern := [1, 2, 2])
    (by decide) (by decide) (by decide) digits_3 count_3_17
theorem discrepancy_3_17 :
    Nat.dist (3^3 * occurrences 3 3 17 126) 126 = 9 := by
  rw [occurrence_3_17]
  decide
theorem count_3_18 : Blocks.count [2, 0, 0] word_3 = 7 := by decide
theorem actualCount_3_18 : Blocks.enumeratedCount [2, 0, 0]
    (actualDigits 3 0 word_3.length) = 7 :=
  certified_count_sound digits_3 count_3_18
theorem occurrence_3_18 : occurrences 3 3 18 126 = 7 :=
  certified_occurrences_sound (b := 3) (value := 7)
    (text := word_3) (pattern := [2, 0, 0])
    (by decide) (by decide) (by decide) digits_3 count_3_18
theorem discrepancy_3_18 :
    Nat.dist (3^3 * occurrences 3 3 18 126) 126 = 63 := by
  rw [occurrence_3_18]
  decide
theorem count_3_19 : Blocks.count [2, 0, 1] word_3 = 1 := by decide
theorem actualCount_3_19 : Blocks.enumeratedCount [2, 0, 1]
    (actualDigits 3 0 word_3.length) = 1 :=
  certified_count_sound digits_3 count_3_19
theorem occurrence_3_19 : occurrences 3 3 19 126 = 1 :=
  certified_occurrences_sound (b := 3) (value := 1)
    (text := word_3) (pattern := [2, 0, 1])
    (by decide) (by decide) (by decide) digits_3 count_3_19
theorem discrepancy_3_19 :
    Nat.dist (3^3 * occurrences 3 3 19 126) 126 = 99 := by
  rw [occurrence_3_19]
  decide
theorem count_3_20 : Blocks.count [2, 0, 2] word_3 = 5 := by decide
theorem actualCount_3_20 : Blocks.enumeratedCount [2, 0, 2]
    (actualDigits 3 0 word_3.length) = 5 :=
  certified_count_sound digits_3 count_3_20
theorem occurrence_3_20 : occurrences 3 3 20 126 = 5 :=
  certified_occurrences_sound (b := 3) (value := 5)
    (text := word_3) (pattern := [2, 0, 2])
    (by decide) (by decide) (by decide) digits_3 count_3_20
theorem discrepancy_3_20 :
    Nat.dist (3^3 * occurrences 3 3 20 126) 126 = 9 := by
  rw [occurrence_3_20]
  decide
theorem count_3_21 : Blocks.count [2, 1, 0] word_3 = 6 := by decide
theorem actualCount_3_21 : Blocks.enumeratedCount [2, 1, 0]
    (actualDigits 3 0 word_3.length) = 6 :=
  certified_count_sound digits_3 count_3_21
theorem occurrence_3_21 : occurrences 3 3 21 126 = 6 :=
  certified_occurrences_sound (b := 3) (value := 6)
    (text := word_3) (pattern := [2, 1, 0])
    (by decide) (by decide) (by decide) digits_3 count_3_21
theorem discrepancy_3_21 :
    Nat.dist (3^3 * occurrences 3 3 21 126) 126 = 36 := by
  rw [occurrence_3_21]
  decide
theorem count_3_22 : Blocks.count [2, 1, 1] word_3 = 5 := by decide
theorem actualCount_3_22 : Blocks.enumeratedCount [2, 1, 1]
    (actualDigits 3 0 word_3.length) = 5 :=
  certified_count_sound digits_3 count_3_22
theorem occurrence_3_22 : occurrences 3 3 22 126 = 5 :=
  certified_occurrences_sound (b := 3) (value := 5)
    (text := word_3) (pattern := [2, 1, 1])
    (by decide) (by decide) (by decide) digits_3 count_3_22
theorem discrepancy_3_22 :
    Nat.dist (3^3 * occurrences 3 3 22 126) 126 = 9 := by
  rw [occurrence_3_22]
  decide
theorem count_3_23 : Blocks.count [2, 1, 2] word_3 = 5 := by decide
theorem actualCount_3_23 : Blocks.enumeratedCount [2, 1, 2]
    (actualDigits 3 0 word_3.length) = 5 :=
  certified_count_sound digits_3 count_3_23
theorem occurrence_3_23 : occurrences 3 3 23 126 = 5 :=
  certified_occurrences_sound (b := 3) (value := 5)
    (text := word_3) (pattern := [2, 1, 2])
    (by decide) (by decide) (by decide) digits_3 count_3_23
theorem discrepancy_3_23 :
    Nat.dist (3^3 * occurrences 3 3 23 126) 126 = 9 := by
  rw [occurrence_3_23]
  decide
theorem count_3_24 : Blocks.count [2, 2, 0] word_3 = 4 := by decide
theorem actualCount_3_24 : Blocks.enumeratedCount [2, 2, 0]
    (actualDigits 3 0 word_3.length) = 4 :=
  certified_count_sound digits_3 count_3_24
theorem occurrence_3_24 : occurrences 3 3 24 126 = 4 :=
  certified_occurrences_sound (b := 3) (value := 4)
    (text := word_3) (pattern := [2, 2, 0])
    (by decide) (by decide) (by decide) digits_3 count_3_24
theorem discrepancy_3_24 :
    Nat.dist (3^3 * occurrences 3 3 24 126) 126 = 18 := by
  rw [occurrence_3_24]
  decide
theorem count_3_25 : Blocks.count [2, 2, 1] word_3 = 4 := by decide
theorem actualCount_3_25 : Blocks.enumeratedCount [2, 2, 1]
    (actualDigits 3 0 word_3.length) = 4 :=
  certified_count_sound digits_3 count_3_25
theorem occurrence_3_25 : occurrences 3 3 25 126 = 4 :=
  certified_occurrences_sound (b := 3) (value := 4)
    (text := word_3) (pattern := [2, 2, 1])
    (by decide) (by decide) (by decide) digits_3 count_3_25
theorem discrepancy_3_25 :
    Nat.dist (3^3 * occurrences 3 3 25 126) 126 = 18 := by
  rw [occurrence_3_25]
  decide
theorem count_3_26 : Blocks.count [2, 2, 2] word_3 = 1 := by decide
theorem actualCount_3_26 : Blocks.enumeratedCount [2, 2, 2]
    (actualDigits 3 0 word_3.length) = 1 :=
  certified_count_sound digits_3 count_3_26
theorem occurrence_3_26 : occurrences 3 3 26 126 = 1 :=
  certified_occurrences_sound (b := 3) (value := 1)
    (text := word_3) (pattern := [2, 2, 2])
    (by decide) (by decide) (by decide) digits_3 count_3_26
theorem discrepancy_3_26 :
    Nat.dist (3^3 * occurrences 3 3 26 126) 126 = 99 := by
  rw [occurrence_3_26]
  decide

def word_4 : List ℕ := [4, 2, 1, 6, 6, 2, 0, 3, 6, 4, 6, 0, 1, 6, 0, 3, 5, 5, 1, 4, 1, 6, 4, 2, 0, 4, 2, 2, 0, 5, 1, 0]
theorem prefix_4_0 : PrefixCertificate (7^0) 0 := by decide
theorem prefix_4_1 : PrefixCertificate (7^1) 4 := by decide
theorem prefix_4_2 : PrefixCertificate (7^2) 30 := by decide
theorem prefix_4_3 : PrefixCertificate (7^3) 211 := by decide
theorem prefix_4_4 : PrefixCertificate (7^4) 1483 := by decide
theorem prefix_4_5 : PrefixCertificate (7^5) 10387 := by decide
theorem prefix_4_6 : PrefixCertificate (7^6) 72711 := by decide
theorem prefix_4_7 : PrefixCertificate (7^7) 508977 := by decide
theorem prefix_4_8 : PrefixCertificate (7^8) 3562842 := by decide
theorem prefix_4_9 : PrefixCertificate (7^9) 24939900 := by decide
theorem prefix_4_10 : PrefixCertificate (7^10) 174579304 := by decide
theorem prefix_4_11 : PrefixCertificate (7^11) 1222055134 := by decide
theorem prefix_4_12 : PrefixCertificate (7^12) 8554385938 := by decide
theorem prefix_4_13 : PrefixCertificate (7^13) 59880701567 := by decide
theorem prefix_4_14 : PrefixCertificate (7^14) 419164910975 := by decide
theorem prefix_4_15 : PrefixCertificate (7^15) 2934154376825 := by decide
theorem prefix_4_16 : PrefixCertificate (7^16) 20539080637778 := by decide
theorem prefix_4_17 : PrefixCertificate (7^17) 143773564464451 := by decide
theorem prefix_4_18 : PrefixCertificate (7^18) 1006414951251162 := by decide
theorem prefix_4_19 : PrefixCertificate (7^19) 7044904658758135 := by decide
theorem prefix_4_20 : PrefixCertificate (7^20) 49314332611306949 := by decide
theorem prefix_4_21 : PrefixCertificate (7^21) 345200328279148644 := by decide
theorem prefix_4_22 : PrefixCertificate (7^22) 2416402297954040514 := by decide
theorem prefix_4_23 : PrefixCertificate (7^23) 16914816085678283602 := by decide
theorem prefix_4_24 : PrefixCertificate (7^24) 118403712599747985216 := by decide
theorem prefix_4_25 : PrefixCertificate (7^25) 828825988198235896512 := by decide
theorem prefix_4_26 : PrefixCertificate (7^26) 5801781917387651275588 := by decide
theorem prefix_4_27 : PrefixCertificate (7^27) 40612473421713558929118 := by decide
theorem prefix_4_28 : PrefixCertificate (7^28) 284287313951994912503828 := by decide
theorem prefix_4_29 : PrefixCertificate (7^29) 1990011197663964387526796 := by decide
theorem prefix_4_30 : PrefixCertificate (7^30) 13930078383647750712687577 := by decide
theorem prefix_4_31 : PrefixCertificate (7^31) 97510548685534254988813040 := by decide
theorem prefix_4_32 : PrefixCertificate (7^32) 682573840798739784921691280 := by decide
theorem digit_4_0 : digit 7 0 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_0 prefix_4_1
theorem digit_4_1 : digit 7 1 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_1 prefix_4_2
theorem digit_4_2 : digit 7 2 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_2 prefix_4_3
theorem digit_4_3 : digit 7 3 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_3 prefix_4_4
theorem digit_4_4 : digit 7 4 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_4 prefix_4_5
theorem digit_4_5 : digit 7 5 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_5 prefix_4_6
theorem digit_4_6 : digit 7 6 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_6 prefix_4_7
theorem digit_4_7 : digit 7 7 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_7 prefix_4_8
theorem digit_4_8 : digit 7 8 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_8 prefix_4_9
theorem digit_4_9 : digit 7 9 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_9 prefix_4_10
theorem digit_4_10 : digit 7 10 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_10 prefix_4_11
theorem digit_4_11 : digit 7 11 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_11 prefix_4_12
theorem digit_4_12 : digit 7 12 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_12 prefix_4_13
theorem digit_4_13 : digit 7 13 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_13 prefix_4_14
theorem digit_4_14 : digit 7 14 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_14 prefix_4_15
theorem digit_4_15 : digit 7 15 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_15 prefix_4_16
theorem digit_4_16 : digit 7 16 = (5 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_16 prefix_4_17
theorem digit_4_17 : digit 7 17 = (5 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_17 prefix_4_18
theorem digit_4_18 : digit 7 18 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_18 prefix_4_19
theorem digit_4_19 : digit 7 19 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_19 prefix_4_20
theorem digit_4_20 : digit 7 20 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_20 prefix_4_21
theorem digit_4_21 : digit 7 21 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_21 prefix_4_22
theorem digit_4_22 : digit 7 22 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_22 prefix_4_23
theorem digit_4_23 : digit 7 23 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_23 prefix_4_24
theorem digit_4_24 : digit 7 24 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_24 prefix_4_25
theorem digit_4_25 : digit 7 25 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_25 prefix_4_26
theorem digit_4_26 : digit 7 26 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_26 prefix_4_27
theorem digit_4_27 : digit 7 27 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_27 prefix_4_28
theorem digit_4_28 : digit 7 28 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_28 prefix_4_29
theorem digit_4_29 : digit 7 29 = (5 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_29 prefix_4_30
theorem digit_4_30 : digit 7 30 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_30 prefix_4_31
theorem digit_4_31 : digit 7 31 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_4_31 prefix_4_32
theorem digits_4 : DigitsAt 7 0 word_4 := And.intro digit_4_0 (And.intro digit_4_1 (And.intro digit_4_2 (And.intro digit_4_3 (And.intro digit_4_4 (And.intro digit_4_5 (And.intro digit_4_6 (And.intro digit_4_7 (And.intro digit_4_8 (And.intro digit_4_9 (And.intro digit_4_10 (And.intro digit_4_11 (And.intro digit_4_12 (And.intro digit_4_13 (And.intro digit_4_14 (And.intro digit_4_15 (And.intro digit_4_16 (And.intro digit_4_17 (And.intro digit_4_18 (And.intro digit_4_19 (And.intro digit_4_20 (And.intro digit_4_21 (And.intro digit_4_22 (And.intro digit_4_23 (And.intro digit_4_24 (And.intro digit_4_25 (And.intro digit_4_26 (And.intro digit_4_27 (And.intro digit_4_28 (And.intro digit_4_29 (And.intro digit_4_30 (And.intro digit_4_31 (True.intro))))))))))))))))))))))))))))))))
theorem count_4_0 : Blocks.count [0, 0] word_4 = 0 := by decide
theorem actualCount_4_0 : Blocks.enumeratedCount [0, 0]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_0
theorem occurrence_4_0 : occurrences 7 2 0 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [0, 0])
    (by decide) (by decide) (by decide) digits_4 count_4_0
theorem discrepancy_4_0 :
    Nat.dist (7^2 * occurrences 7 2 0 31) 31 = 31 := by
  rw [occurrence_4_0]
  decide
theorem count_4_1 : Blocks.count [0, 1] word_4 = 1 := by decide
theorem actualCount_4_1 : Blocks.enumeratedCount [0, 1]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_1
theorem occurrence_4_1 : occurrences 7 2 1 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [0, 1])
    (by decide) (by decide) (by decide) digits_4 count_4_1
theorem discrepancy_4_1 :
    Nat.dist (7^2 * occurrences 7 2 1 31) 31 = 18 := by
  rw [occurrence_4_1]
  decide
theorem count_4_2 : Blocks.count [0, 2] word_4 = 0 := by decide
theorem actualCount_4_2 : Blocks.enumeratedCount [0, 2]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_2
theorem occurrence_4_2 : occurrences 7 2 2 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [0, 2])
    (by decide) (by decide) (by decide) digits_4 count_4_2
theorem discrepancy_4_2 :
    Nat.dist (7^2 * occurrences 7 2 2 31) 31 = 31 := by
  rw [occurrence_4_2]
  decide
theorem count_4_3 : Blocks.count [0, 3] word_4 = 2 := by decide
theorem actualCount_4_3 : Blocks.enumeratedCount [0, 3]
    (actualDigits 7 0 word_4.length) = 2 :=
  certified_count_sound digits_4 count_4_3
theorem occurrence_4_3 : occurrences 7 2 3 31 = 2 :=
  certified_occurrences_sound (b := 7) (value := 2)
    (text := word_4) (pattern := [0, 3])
    (by decide) (by decide) (by decide) digits_4 count_4_3
theorem discrepancy_4_3 :
    Nat.dist (7^2 * occurrences 7 2 3 31) 31 = 67 := by
  rw [occurrence_4_3]
  decide
theorem count_4_4 : Blocks.count [0, 4] word_4 = 1 := by decide
theorem actualCount_4_4 : Blocks.enumeratedCount [0, 4]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_4
theorem occurrence_4_4 : occurrences 7 2 4 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [0, 4])
    (by decide) (by decide) (by decide) digits_4 count_4_4
theorem discrepancy_4_4 :
    Nat.dist (7^2 * occurrences 7 2 4 31) 31 = 18 := by
  rw [occurrence_4_4]
  decide
theorem count_4_5 : Blocks.count [0, 5] word_4 = 1 := by decide
theorem actualCount_4_5 : Blocks.enumeratedCount [0, 5]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_5
theorem occurrence_4_5 : occurrences 7 2 5 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [0, 5])
    (by decide) (by decide) (by decide) digits_4 count_4_5
theorem discrepancy_4_5 :
    Nat.dist (7^2 * occurrences 7 2 5 31) 31 = 18 := by
  rw [occurrence_4_5]
  decide
theorem count_4_6 : Blocks.count [0, 6] word_4 = 0 := by decide
theorem actualCount_4_6 : Blocks.enumeratedCount [0, 6]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_6
theorem occurrence_4_6 : occurrences 7 2 6 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [0, 6])
    (by decide) (by decide) (by decide) digits_4 count_4_6
theorem discrepancy_4_6 :
    Nat.dist (7^2 * occurrences 7 2 6 31) 31 = 31 := by
  rw [occurrence_4_6]
  decide
theorem count_4_7 : Blocks.count [1, 0] word_4 = 1 := by decide
theorem actualCount_4_7 : Blocks.enumeratedCount [1, 0]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_7
theorem occurrence_4_7 : occurrences 7 2 7 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [1, 0])
    (by decide) (by decide) (by decide) digits_4 count_4_7
theorem discrepancy_4_7 :
    Nat.dist (7^2 * occurrences 7 2 7 31) 31 = 18 := by
  rw [occurrence_4_7]
  decide
theorem count_4_8 : Blocks.count [1, 1] word_4 = 0 := by decide
theorem actualCount_4_8 : Blocks.enumeratedCount [1, 1]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_8
theorem occurrence_4_8 : occurrences 7 2 8 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [1, 1])
    (by decide) (by decide) (by decide) digits_4 count_4_8
theorem discrepancy_4_8 :
    Nat.dist (7^2 * occurrences 7 2 8 31) 31 = 31 := by
  rw [occurrence_4_8]
  decide
theorem count_4_9 : Blocks.count [1, 2] word_4 = 0 := by decide
theorem actualCount_4_9 : Blocks.enumeratedCount [1, 2]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_9
theorem occurrence_4_9 : occurrences 7 2 9 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [1, 2])
    (by decide) (by decide) (by decide) digits_4 count_4_9
theorem discrepancy_4_9 :
    Nat.dist (7^2 * occurrences 7 2 9 31) 31 = 31 := by
  rw [occurrence_4_9]
  decide
theorem count_4_10 : Blocks.count [1, 3] word_4 = 0 := by decide
theorem actualCount_4_10 : Blocks.enumeratedCount [1, 3]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_10
theorem occurrence_4_10 : occurrences 7 2 10 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [1, 3])
    (by decide) (by decide) (by decide) digits_4 count_4_10
theorem discrepancy_4_10 :
    Nat.dist (7^2 * occurrences 7 2 10 31) 31 = 31 := by
  rw [occurrence_4_10]
  decide
theorem count_4_11 : Blocks.count [1, 4] word_4 = 1 := by decide
theorem actualCount_4_11 : Blocks.enumeratedCount [1, 4]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_11
theorem occurrence_4_11 : occurrences 7 2 11 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [1, 4])
    (by decide) (by decide) (by decide) digits_4 count_4_11
theorem discrepancy_4_11 :
    Nat.dist (7^2 * occurrences 7 2 11 31) 31 = 18 := by
  rw [occurrence_4_11]
  decide
theorem count_4_12 : Blocks.count [1, 5] word_4 = 0 := by decide
theorem actualCount_4_12 : Blocks.enumeratedCount [1, 5]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_12
theorem occurrence_4_12 : occurrences 7 2 12 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [1, 5])
    (by decide) (by decide) (by decide) digits_4 count_4_12
theorem discrepancy_4_12 :
    Nat.dist (7^2 * occurrences 7 2 12 31) 31 = 31 := by
  rw [occurrence_4_12]
  decide
theorem count_4_13 : Blocks.count [1, 6] word_4 = 3 := by decide
theorem actualCount_4_13 : Blocks.enumeratedCount [1, 6]
    (actualDigits 7 0 word_4.length) = 3 :=
  certified_count_sound digits_4 count_4_13
theorem occurrence_4_13 : occurrences 7 2 13 31 = 3 :=
  certified_occurrences_sound (b := 7) (value := 3)
    (text := word_4) (pattern := [1, 6])
    (by decide) (by decide) (by decide) digits_4 count_4_13
theorem discrepancy_4_13 :
    Nat.dist (7^2 * occurrences 7 2 13 31) 31 = 116 := by
  rw [occurrence_4_13]
  decide
theorem count_4_14 : Blocks.count [2, 0] word_4 = 3 := by decide
theorem actualCount_4_14 : Blocks.enumeratedCount [2, 0]
    (actualDigits 7 0 word_4.length) = 3 :=
  certified_count_sound digits_4 count_4_14
theorem occurrence_4_14 : occurrences 7 2 14 31 = 3 :=
  certified_occurrences_sound (b := 7) (value := 3)
    (text := word_4) (pattern := [2, 0])
    (by decide) (by decide) (by decide) digits_4 count_4_14
theorem discrepancy_4_14 :
    Nat.dist (7^2 * occurrences 7 2 14 31) 31 = 116 := by
  rw [occurrence_4_14]
  decide
theorem count_4_15 : Blocks.count [2, 1] word_4 = 1 := by decide
theorem actualCount_4_15 : Blocks.enumeratedCount [2, 1]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_15
theorem occurrence_4_15 : occurrences 7 2 15 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [2, 1])
    (by decide) (by decide) (by decide) digits_4 count_4_15
theorem discrepancy_4_15 :
    Nat.dist (7^2 * occurrences 7 2 15 31) 31 = 18 := by
  rw [occurrence_4_15]
  decide
theorem count_4_16 : Blocks.count [2, 2] word_4 = 1 := by decide
theorem actualCount_4_16 : Blocks.enumeratedCount [2, 2]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_16
theorem occurrence_4_16 : occurrences 7 2 16 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [2, 2])
    (by decide) (by decide) (by decide) digits_4 count_4_16
theorem discrepancy_4_16 :
    Nat.dist (7^2 * occurrences 7 2 16 31) 31 = 18 := by
  rw [occurrence_4_16]
  decide
theorem count_4_17 : Blocks.count [2, 3] word_4 = 0 := by decide
theorem actualCount_4_17 : Blocks.enumeratedCount [2, 3]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_17
theorem occurrence_4_17 : occurrences 7 2 17 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [2, 3])
    (by decide) (by decide) (by decide) digits_4 count_4_17
theorem discrepancy_4_17 :
    Nat.dist (7^2 * occurrences 7 2 17 31) 31 = 31 := by
  rw [occurrence_4_17]
  decide
theorem count_4_18 : Blocks.count [2, 4] word_4 = 0 := by decide
theorem actualCount_4_18 : Blocks.enumeratedCount [2, 4]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_18
theorem occurrence_4_18 : occurrences 7 2 18 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [2, 4])
    (by decide) (by decide) (by decide) digits_4 count_4_18
theorem discrepancy_4_18 :
    Nat.dist (7^2 * occurrences 7 2 18 31) 31 = 31 := by
  rw [occurrence_4_18]
  decide
theorem count_4_19 : Blocks.count [2, 5] word_4 = 0 := by decide
theorem actualCount_4_19 : Blocks.enumeratedCount [2, 5]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_19
theorem occurrence_4_19 : occurrences 7 2 19 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [2, 5])
    (by decide) (by decide) (by decide) digits_4 count_4_19
theorem discrepancy_4_19 :
    Nat.dist (7^2 * occurrences 7 2 19 31) 31 = 31 := by
  rw [occurrence_4_19]
  decide
theorem count_4_20 : Blocks.count [2, 6] word_4 = 0 := by decide
theorem actualCount_4_20 : Blocks.enumeratedCount [2, 6]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_20
theorem occurrence_4_20 : occurrences 7 2 20 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [2, 6])
    (by decide) (by decide) (by decide) digits_4 count_4_20
theorem discrepancy_4_20 :
    Nat.dist (7^2 * occurrences 7 2 20 31) 31 = 31 := by
  rw [occurrence_4_20]
  decide
theorem count_4_21 : Blocks.count [3, 0] word_4 = 0 := by decide
theorem actualCount_4_21 : Blocks.enumeratedCount [3, 0]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_21
theorem occurrence_4_21 : occurrences 7 2 21 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [3, 0])
    (by decide) (by decide) (by decide) digits_4 count_4_21
theorem discrepancy_4_21 :
    Nat.dist (7^2 * occurrences 7 2 21 31) 31 = 31 := by
  rw [occurrence_4_21]
  decide
theorem count_4_22 : Blocks.count [3, 1] word_4 = 0 := by decide
theorem actualCount_4_22 : Blocks.enumeratedCount [3, 1]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_22
theorem occurrence_4_22 : occurrences 7 2 22 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [3, 1])
    (by decide) (by decide) (by decide) digits_4 count_4_22
theorem discrepancy_4_22 :
    Nat.dist (7^2 * occurrences 7 2 22 31) 31 = 31 := by
  rw [occurrence_4_22]
  decide
theorem count_4_23 : Blocks.count [3, 2] word_4 = 0 := by decide
theorem actualCount_4_23 : Blocks.enumeratedCount [3, 2]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_23
theorem occurrence_4_23 : occurrences 7 2 23 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [3, 2])
    (by decide) (by decide) (by decide) digits_4 count_4_23
theorem discrepancy_4_23 :
    Nat.dist (7^2 * occurrences 7 2 23 31) 31 = 31 := by
  rw [occurrence_4_23]
  decide
theorem count_4_24 : Blocks.count [3, 3] word_4 = 0 := by decide
theorem actualCount_4_24 : Blocks.enumeratedCount [3, 3]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_24
theorem occurrence_4_24 : occurrences 7 2 24 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [3, 3])
    (by decide) (by decide) (by decide) digits_4 count_4_24
theorem discrepancy_4_24 :
    Nat.dist (7^2 * occurrences 7 2 24 31) 31 = 31 := by
  rw [occurrence_4_24]
  decide
theorem count_4_25 : Blocks.count [3, 4] word_4 = 0 := by decide
theorem actualCount_4_25 : Blocks.enumeratedCount [3, 4]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_25
theorem occurrence_4_25 : occurrences 7 2 25 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [3, 4])
    (by decide) (by decide) (by decide) digits_4 count_4_25
theorem discrepancy_4_25 :
    Nat.dist (7^2 * occurrences 7 2 25 31) 31 = 31 := by
  rw [occurrence_4_25]
  decide
theorem count_4_26 : Blocks.count [3, 5] word_4 = 1 := by decide
theorem actualCount_4_26 : Blocks.enumeratedCount [3, 5]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_26
theorem occurrence_4_26 : occurrences 7 2 26 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [3, 5])
    (by decide) (by decide) (by decide) digits_4 count_4_26
theorem discrepancy_4_26 :
    Nat.dist (7^2 * occurrences 7 2 26 31) 31 = 18 := by
  rw [occurrence_4_26]
  decide
theorem count_4_27 : Blocks.count [3, 6] word_4 = 1 := by decide
theorem actualCount_4_27 : Blocks.enumeratedCount [3, 6]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_27
theorem occurrence_4_27 : occurrences 7 2 27 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [3, 6])
    (by decide) (by decide) (by decide) digits_4 count_4_27
theorem discrepancy_4_27 :
    Nat.dist (7^2 * occurrences 7 2 27 31) 31 = 18 := by
  rw [occurrence_4_27]
  decide
theorem count_4_28 : Blocks.count [4, 0] word_4 = 0 := by decide
theorem actualCount_4_28 : Blocks.enumeratedCount [4, 0]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_28
theorem occurrence_4_28 : occurrences 7 2 28 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [4, 0])
    (by decide) (by decide) (by decide) digits_4 count_4_28
theorem discrepancy_4_28 :
    Nat.dist (7^2 * occurrences 7 2 28 31) 31 = 31 := by
  rw [occurrence_4_28]
  decide
theorem count_4_29 : Blocks.count [4, 1] word_4 = 1 := by decide
theorem actualCount_4_29 : Blocks.enumeratedCount [4, 1]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_29
theorem occurrence_4_29 : occurrences 7 2 29 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [4, 1])
    (by decide) (by decide) (by decide) digits_4 count_4_29
theorem discrepancy_4_29 :
    Nat.dist (7^2 * occurrences 7 2 29 31) 31 = 18 := by
  rw [occurrence_4_29]
  decide
theorem count_4_30 : Blocks.count [4, 2] word_4 = 3 := by decide
theorem actualCount_4_30 : Blocks.enumeratedCount [4, 2]
    (actualDigits 7 0 word_4.length) = 3 :=
  certified_count_sound digits_4 count_4_30
theorem occurrence_4_30 : occurrences 7 2 30 31 = 3 :=
  certified_occurrences_sound (b := 7) (value := 3)
    (text := word_4) (pattern := [4, 2])
    (by decide) (by decide) (by decide) digits_4 count_4_30
theorem discrepancy_4_30 :
    Nat.dist (7^2 * occurrences 7 2 30 31) 31 = 116 := by
  rw [occurrence_4_30]
  decide
theorem count_4_31 : Blocks.count [4, 3] word_4 = 0 := by decide
theorem actualCount_4_31 : Blocks.enumeratedCount [4, 3]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_31
theorem occurrence_4_31 : occurrences 7 2 31 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [4, 3])
    (by decide) (by decide) (by decide) digits_4 count_4_31
theorem discrepancy_4_31 :
    Nat.dist (7^2 * occurrences 7 2 31 31) 31 = 31 := by
  rw [occurrence_4_31]
  decide
theorem count_4_32 : Blocks.count [4, 4] word_4 = 0 := by decide
theorem actualCount_4_32 : Blocks.enumeratedCount [4, 4]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_32
theorem occurrence_4_32 : occurrences 7 2 32 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [4, 4])
    (by decide) (by decide) (by decide) digits_4 count_4_32
theorem discrepancy_4_32 :
    Nat.dist (7^2 * occurrences 7 2 32 31) 31 = 31 := by
  rw [occurrence_4_32]
  decide
theorem count_4_33 : Blocks.count [4, 5] word_4 = 0 := by decide
theorem actualCount_4_33 : Blocks.enumeratedCount [4, 5]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_33
theorem occurrence_4_33 : occurrences 7 2 33 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [4, 5])
    (by decide) (by decide) (by decide) digits_4 count_4_33
theorem discrepancy_4_33 :
    Nat.dist (7^2 * occurrences 7 2 33 31) 31 = 31 := by
  rw [occurrence_4_33]
  decide
theorem count_4_34 : Blocks.count [4, 6] word_4 = 1 := by decide
theorem actualCount_4_34 : Blocks.enumeratedCount [4, 6]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_34
theorem occurrence_4_34 : occurrences 7 2 34 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [4, 6])
    (by decide) (by decide) (by decide) digits_4 count_4_34
theorem discrepancy_4_34 :
    Nat.dist (7^2 * occurrences 7 2 34 31) 31 = 18 := by
  rw [occurrence_4_34]
  decide
theorem count_4_35 : Blocks.count [5, 0] word_4 = 0 := by decide
theorem actualCount_4_35 : Blocks.enumeratedCount [5, 0]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_35
theorem occurrence_4_35 : occurrences 7 2 35 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [5, 0])
    (by decide) (by decide) (by decide) digits_4 count_4_35
theorem discrepancy_4_35 :
    Nat.dist (7^2 * occurrences 7 2 35 31) 31 = 31 := by
  rw [occurrence_4_35]
  decide
theorem count_4_36 : Blocks.count [5, 1] word_4 = 2 := by decide
theorem actualCount_4_36 : Blocks.enumeratedCount [5, 1]
    (actualDigits 7 0 word_4.length) = 2 :=
  certified_count_sound digits_4 count_4_36
theorem occurrence_4_36 : occurrences 7 2 36 31 = 2 :=
  certified_occurrences_sound (b := 7) (value := 2)
    (text := word_4) (pattern := [5, 1])
    (by decide) (by decide) (by decide) digits_4 count_4_36
theorem discrepancy_4_36 :
    Nat.dist (7^2 * occurrences 7 2 36 31) 31 = 67 := by
  rw [occurrence_4_36]
  decide
theorem count_4_37 : Blocks.count [5, 2] word_4 = 0 := by decide
theorem actualCount_4_37 : Blocks.enumeratedCount [5, 2]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_37
theorem occurrence_4_37 : occurrences 7 2 37 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [5, 2])
    (by decide) (by decide) (by decide) digits_4 count_4_37
theorem discrepancy_4_37 :
    Nat.dist (7^2 * occurrences 7 2 37 31) 31 = 31 := by
  rw [occurrence_4_37]
  decide
theorem count_4_38 : Blocks.count [5, 3] word_4 = 0 := by decide
theorem actualCount_4_38 : Blocks.enumeratedCount [5, 3]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_38
theorem occurrence_4_38 : occurrences 7 2 38 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [5, 3])
    (by decide) (by decide) (by decide) digits_4 count_4_38
theorem discrepancy_4_38 :
    Nat.dist (7^2 * occurrences 7 2 38 31) 31 = 31 := by
  rw [occurrence_4_38]
  decide
theorem count_4_39 : Blocks.count [5, 4] word_4 = 0 := by decide
theorem actualCount_4_39 : Blocks.enumeratedCount [5, 4]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_39
theorem occurrence_4_39 : occurrences 7 2 39 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [5, 4])
    (by decide) (by decide) (by decide) digits_4 count_4_39
theorem discrepancy_4_39 :
    Nat.dist (7^2 * occurrences 7 2 39 31) 31 = 31 := by
  rw [occurrence_4_39]
  decide
theorem count_4_40 : Blocks.count [5, 5] word_4 = 1 := by decide
theorem actualCount_4_40 : Blocks.enumeratedCount [5, 5]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_40
theorem occurrence_4_40 : occurrences 7 2 40 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [5, 5])
    (by decide) (by decide) (by decide) digits_4 count_4_40
theorem discrepancy_4_40 :
    Nat.dist (7^2 * occurrences 7 2 40 31) 31 = 18 := by
  rw [occurrence_4_40]
  decide
theorem count_4_41 : Blocks.count [5, 6] word_4 = 0 := by decide
theorem actualCount_4_41 : Blocks.enumeratedCount [5, 6]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_41
theorem occurrence_4_41 : occurrences 7 2 41 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [5, 6])
    (by decide) (by decide) (by decide) digits_4 count_4_41
theorem discrepancy_4_41 :
    Nat.dist (7^2 * occurrences 7 2 41 31) 31 = 31 := by
  rw [occurrence_4_41]
  decide
theorem count_4_42 : Blocks.count [6, 0] word_4 = 2 := by decide
theorem actualCount_4_42 : Blocks.enumeratedCount [6, 0]
    (actualDigits 7 0 word_4.length) = 2 :=
  certified_count_sound digits_4 count_4_42
theorem occurrence_4_42 : occurrences 7 2 42 31 = 2 :=
  certified_occurrences_sound (b := 7) (value := 2)
    (text := word_4) (pattern := [6, 0])
    (by decide) (by decide) (by decide) digits_4 count_4_42
theorem discrepancy_4_42 :
    Nat.dist (7^2 * occurrences 7 2 42 31) 31 = 67 := by
  rw [occurrence_4_42]
  decide
theorem count_4_43 : Blocks.count [6, 1] word_4 = 0 := by decide
theorem actualCount_4_43 : Blocks.enumeratedCount [6, 1]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_43
theorem occurrence_4_43 : occurrences 7 2 43 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [6, 1])
    (by decide) (by decide) (by decide) digits_4 count_4_43
theorem discrepancy_4_43 :
    Nat.dist (7^2 * occurrences 7 2 43 31) 31 = 31 := by
  rw [occurrence_4_43]
  decide
theorem count_4_44 : Blocks.count [6, 2] word_4 = 1 := by decide
theorem actualCount_4_44 : Blocks.enumeratedCount [6, 2]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_44
theorem occurrence_4_44 : occurrences 7 2 44 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [6, 2])
    (by decide) (by decide) (by decide) digits_4 count_4_44
theorem discrepancy_4_44 :
    Nat.dist (7^2 * occurrences 7 2 44 31) 31 = 18 := by
  rw [occurrence_4_44]
  decide
theorem count_4_45 : Blocks.count [6, 3] word_4 = 0 := by decide
theorem actualCount_4_45 : Blocks.enumeratedCount [6, 3]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_45
theorem occurrence_4_45 : occurrences 7 2 45 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [6, 3])
    (by decide) (by decide) (by decide) digits_4 count_4_45
theorem discrepancy_4_45 :
    Nat.dist (7^2 * occurrences 7 2 45 31) 31 = 31 := by
  rw [occurrence_4_45]
  decide
theorem count_4_46 : Blocks.count [6, 4] word_4 = 2 := by decide
theorem actualCount_4_46 : Blocks.enumeratedCount [6, 4]
    (actualDigits 7 0 word_4.length) = 2 :=
  certified_count_sound digits_4 count_4_46
theorem occurrence_4_46 : occurrences 7 2 46 31 = 2 :=
  certified_occurrences_sound (b := 7) (value := 2)
    (text := word_4) (pattern := [6, 4])
    (by decide) (by decide) (by decide) digits_4 count_4_46
theorem discrepancy_4_46 :
    Nat.dist (7^2 * occurrences 7 2 46 31) 31 = 67 := by
  rw [occurrence_4_46]
  decide
theorem count_4_47 : Blocks.count [6, 5] word_4 = 0 := by decide
theorem actualCount_4_47 : Blocks.enumeratedCount [6, 5]
    (actualDigits 7 0 word_4.length) = 0 :=
  certified_count_sound digits_4 count_4_47
theorem occurrence_4_47 : occurrences 7 2 47 31 = 0 :=
  certified_occurrences_sound (b := 7) (value := 0)
    (text := word_4) (pattern := [6, 5])
    (by decide) (by decide) (by decide) digits_4 count_4_47
theorem discrepancy_4_47 :
    Nat.dist (7^2 * occurrences 7 2 47 31) 31 = 31 := by
  rw [occurrence_4_47]
  decide
theorem count_4_48 : Blocks.count [6, 6] word_4 = 1 := by decide
theorem actualCount_4_48 : Blocks.enumeratedCount [6, 6]
    (actualDigits 7 0 word_4.length) = 1 :=
  certified_count_sound digits_4 count_4_48
theorem occurrence_4_48 : occurrences 7 2 48 31 = 1 :=
  certified_occurrences_sound (b := 7) (value := 1)
    (text := word_4) (pattern := [6, 6])
    (by decide) (by decide) (by decide) digits_4 count_4_48
theorem discrepancy_4_48 :
    Nat.dist (7^2 * occurrences 7 2 48 31) 31 = 18 := by
  rw [occurrence_4_48]
  decide

def word_5 : List ℕ := [6, 1, 8, 0, 3, 3, 9, 8, 8, 7, 4, 9, 8, 9, 4, 8, 4, 8, 2, 0, 4, 5, 8, 6, 8, 3, 4, 3, 6, 5, 6, 3, 8, 1, 1, 7, 7, 2, 0, 3, 0, 9, 1, 7, 9, 8, 0, 5, 7, 6, 2, 8, 6, 2, 1, 3, 5, 4, 4, 8, 6, 2, 2, 7, 0, 5, 2, 6, 0, 4, 6, 2, 8, 1, 8, 9, 0, 2, 4, 4, 9, 7, 0, 7, 2, 0, 7, 2, 0, 4, 1, 8, 9, 3, 9, 1, 1, 3, 7, 4, 8, 4, 7, 5, 4, 0, 8, 8, 0, 7, 5, 3, 8, 6, 8, 9, 1, 7, 5, 2, 1, 2, 6, 6, 3, 3, 8, 6]
theorem prefix_5_0 : PrefixCertificate (10^0) 0 := by decide
theorem prefix_5_1 : PrefixCertificate (10^1) 6 := by decide
theorem prefix_5_2 : PrefixCertificate (10^2) 61 := by decide
theorem prefix_5_3 : PrefixCertificate (10^3) 618 := by decide
theorem prefix_5_4 : PrefixCertificate (10^4) 6180 := by decide
theorem prefix_5_5 : PrefixCertificate (10^5) 61803 := by decide
theorem prefix_5_6 : PrefixCertificate (10^6) 618033 := by decide
theorem prefix_5_7 : PrefixCertificate (10^7) 6180339 := by decide
theorem prefix_5_8 : PrefixCertificate (10^8) 61803398 := by decide
theorem prefix_5_9 : PrefixCertificate (10^9) 618033988 := by decide
theorem prefix_5_10 : PrefixCertificate (10^10) 6180339887 := by decide
theorem prefix_5_11 : PrefixCertificate (10^11) 61803398874 := by decide
theorem prefix_5_12 : PrefixCertificate (10^12) 618033988749 := by decide
theorem prefix_5_13 : PrefixCertificate (10^13) 6180339887498 := by decide
theorem prefix_5_14 : PrefixCertificate (10^14) 61803398874989 := by decide
theorem prefix_5_15 : PrefixCertificate (10^15) 618033988749894 := by decide
theorem prefix_5_16 : PrefixCertificate (10^16) 6180339887498948 := by decide
theorem prefix_5_17 : PrefixCertificate (10^17) 61803398874989484 := by decide
theorem prefix_5_18 : PrefixCertificate (10^18) 618033988749894848 := by decide
theorem prefix_5_19 : PrefixCertificate (10^19) 6180339887498948482 := by decide
theorem prefix_5_20 : PrefixCertificate (10^20) 61803398874989484820 := by decide
theorem prefix_5_21 : PrefixCertificate (10^21) 618033988749894848204 := by decide
theorem prefix_5_22 : PrefixCertificate (10^22) 6180339887498948482045 := by decide
theorem prefix_5_23 : PrefixCertificate (10^23) 61803398874989484820458 := by decide
theorem prefix_5_24 : PrefixCertificate (10^24) 618033988749894848204586 := by decide
theorem prefix_5_25 : PrefixCertificate (10^25) 6180339887498948482045868 := by decide
theorem prefix_5_26 : PrefixCertificate (10^26) 61803398874989484820458683 := by decide
theorem prefix_5_27 : PrefixCertificate (10^27) 618033988749894848204586834 := by decide
theorem prefix_5_28 : PrefixCertificate (10^28) 6180339887498948482045868343 := by decide
theorem prefix_5_29 : PrefixCertificate (10^29) 61803398874989484820458683436 := by decide
theorem prefix_5_30 : PrefixCertificate (10^30) 618033988749894848204586834365 := by decide
theorem prefix_5_31 : PrefixCertificate (10^31) 6180339887498948482045868343656 := by decide
theorem prefix_5_32 : PrefixCertificate (10^32) 61803398874989484820458683436563 := by decide
theorem prefix_5_33 : PrefixCertificate (10^33) 618033988749894848204586834365638 := by decide
theorem prefix_5_34 : PrefixCertificate (10^34) 6180339887498948482045868343656381 := by decide
theorem prefix_5_35 : PrefixCertificate (10^35) 61803398874989484820458683436563811 := by decide
theorem prefix_5_36 : PrefixCertificate (10^36) 618033988749894848204586834365638117 := by decide
theorem prefix_5_37 : PrefixCertificate (10^37) 6180339887498948482045868343656381177 := by decide
theorem prefix_5_38 : PrefixCertificate (10^38) 61803398874989484820458683436563811772 := by decide
theorem prefix_5_39 : PrefixCertificate (10^39) 618033988749894848204586834365638117720 := by decide
theorem prefix_5_40 : PrefixCertificate (10^40) 6180339887498948482045868343656381177203 := by decide
theorem prefix_5_41 : PrefixCertificate (10^41) 61803398874989484820458683436563811772030 := by decide
theorem prefix_5_42 : PrefixCertificate (10^42) 618033988749894848204586834365638117720309 := by decide
theorem prefix_5_43 : PrefixCertificate (10^43) 6180339887498948482045868343656381177203091 := by decide
theorem prefix_5_44 : PrefixCertificate (10^44) 61803398874989484820458683436563811772030917 := by decide
theorem prefix_5_45 : PrefixCertificate (10^45) 618033988749894848204586834365638117720309179 := by decide
theorem prefix_5_46 : PrefixCertificate (10^46) 6180339887498948482045868343656381177203091798 := by decide
theorem prefix_5_47 : PrefixCertificate (10^47) 61803398874989484820458683436563811772030917980 := by decide
theorem prefix_5_48 : PrefixCertificate (10^48) 618033988749894848204586834365638117720309179805 := by decide
theorem prefix_5_49 : PrefixCertificate (10^49) 6180339887498948482045868343656381177203091798057 := by decide
theorem prefix_5_50 : PrefixCertificate (10^50) 61803398874989484820458683436563811772030917980576 := by decide
theorem prefix_5_51 : PrefixCertificate (10^51) 618033988749894848204586834365638117720309179805762 := by decide
theorem prefix_5_52 : PrefixCertificate (10^52) 6180339887498948482045868343656381177203091798057628 := by decide
theorem prefix_5_53 : PrefixCertificate (10^53) 61803398874989484820458683436563811772030917980576286 := by decide
theorem prefix_5_54 : PrefixCertificate (10^54) 618033988749894848204586834365638117720309179805762862 := by decide
theorem prefix_5_55 : PrefixCertificate (10^55) 6180339887498948482045868343656381177203091798057628621 := by decide
theorem prefix_5_56 : PrefixCertificate (10^56) 61803398874989484820458683436563811772030917980576286213 := by decide
theorem prefix_5_57 : PrefixCertificate (10^57) 618033988749894848204586834365638117720309179805762862135 := by decide
theorem prefix_5_58 : PrefixCertificate (10^58) 6180339887498948482045868343656381177203091798057628621354 := by decide
theorem prefix_5_59 : PrefixCertificate (10^59) 61803398874989484820458683436563811772030917980576286213544 := by decide
theorem prefix_5_60 : PrefixCertificate (10^60) 618033988749894848204586834365638117720309179805762862135448 := by decide
theorem prefix_5_61 : PrefixCertificate (10^61) 6180339887498948482045868343656381177203091798057628621354486 := by decide
theorem prefix_5_62 : PrefixCertificate (10^62) 61803398874989484820458683436563811772030917980576286213544862 := by decide
theorem prefix_5_63 : PrefixCertificate (10^63) 618033988749894848204586834365638117720309179805762862135448622 := by decide
theorem prefix_5_64 : PrefixCertificate (10^64) 6180339887498948482045868343656381177203091798057628621354486227 := by decide
theorem prefix_5_65 : PrefixCertificate (10^65) 61803398874989484820458683436563811772030917980576286213544862270 := by decide
theorem prefix_5_66 : PrefixCertificate (10^66) 618033988749894848204586834365638117720309179805762862135448622705 := by decide
theorem prefix_5_67 : PrefixCertificate (10^67) 6180339887498948482045868343656381177203091798057628621354486227052 := by decide
theorem prefix_5_68 : PrefixCertificate (10^68) 61803398874989484820458683436563811772030917980576286213544862270526 := by decide
theorem prefix_5_69 : PrefixCertificate (10^69) 618033988749894848204586834365638117720309179805762862135448622705260 := by decide
theorem prefix_5_70 : PrefixCertificate (10^70) 6180339887498948482045868343656381177203091798057628621354486227052604 := by decide
theorem prefix_5_71 : PrefixCertificate (10^71) 61803398874989484820458683436563811772030917980576286213544862270526046 := by decide
theorem prefix_5_72 : PrefixCertificate (10^72) 618033988749894848204586834365638117720309179805762862135448622705260462 := by decide
theorem prefix_5_73 : PrefixCertificate (10^73) 6180339887498948482045868343656381177203091798057628621354486227052604628 := by decide
theorem prefix_5_74 : PrefixCertificate (10^74) 61803398874989484820458683436563811772030917980576286213544862270526046281 := by decide
theorem prefix_5_75 : PrefixCertificate (10^75) 618033988749894848204586834365638117720309179805762862135448622705260462818 := by decide
theorem prefix_5_76 : PrefixCertificate (10^76) 6180339887498948482045868343656381177203091798057628621354486227052604628189 := by decide
theorem prefix_5_77 : PrefixCertificate (10^77) 61803398874989484820458683436563811772030917980576286213544862270526046281890 := by decide
theorem prefix_5_78 : PrefixCertificate (10^78) 618033988749894848204586834365638117720309179805762862135448622705260462818902 := by decide
theorem prefix_5_79 : PrefixCertificate (10^79) 6180339887498948482045868343656381177203091798057628621354486227052604628189024 := by decide
theorem prefix_5_80 : PrefixCertificate (10^80) 61803398874989484820458683436563811772030917980576286213544862270526046281890244 := by decide
theorem prefix_5_81 : PrefixCertificate (10^81) 618033988749894848204586834365638117720309179805762862135448622705260462818902449 := by decide
theorem prefix_5_82 : PrefixCertificate (10^82) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497 := by decide
theorem prefix_5_83 : PrefixCertificate (10^83) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970 := by decide
theorem prefix_5_84 : PrefixCertificate (10^84) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707 := by decide
theorem prefix_5_85 : PrefixCertificate (10^85) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072 := by decide
theorem prefix_5_86 : PrefixCertificate (10^86) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720 := by decide
theorem prefix_5_87 : PrefixCertificate (10^87) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207 := by decide
theorem prefix_5_88 : PrefixCertificate (10^88) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072 := by decide
theorem prefix_5_89 : PrefixCertificate (10^89) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720 := by decide
theorem prefix_5_90 : PrefixCertificate (10^90) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204 := by decide
theorem prefix_5_91 : PrefixCertificate (10^91) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041 := by decide
theorem prefix_5_92 : PrefixCertificate (10^92) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418 := by decide
theorem prefix_5_93 : PrefixCertificate (10^93) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189 := by decide
theorem prefix_5_94 : PrefixCertificate (10^94) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893 := by decide
theorem prefix_5_95 : PrefixCertificate (10^95) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939 := by decide
theorem prefix_5_96 : PrefixCertificate (10^96) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391 := by decide
theorem prefix_5_97 : PrefixCertificate (10^97) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911 := by decide
theorem prefix_5_98 : PrefixCertificate (10^98) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939113 := by decide
theorem prefix_5_99 : PrefixCertificate (10^99) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137 := by decide
theorem prefix_5_100 : PrefixCertificate (10^100) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374 := by decide
theorem prefix_5_101 : PrefixCertificate (10^101) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939113748 := by decide
theorem prefix_5_102 : PrefixCertificate (10^102) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137484 := by decide
theorem prefix_5_103 : PrefixCertificate (10^103) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847 := by decide
theorem prefix_5_104 : PrefixCertificate (10^104) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939113748475 := by decide
theorem prefix_5_105 : PrefixCertificate (10^105) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137484754 := by decide
theorem prefix_5_106 : PrefixCertificate (10^106) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540 := by decide
theorem prefix_5_107 : PrefixCertificate (10^107) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939113748475408 := by decide
theorem prefix_5_108 : PrefixCertificate (10^108) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137484754088 := by decide
theorem prefix_5_109 : PrefixCertificate (10^109) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540880 := by decide
theorem prefix_5_110 : PrefixCertificate (10^110) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939113748475408807 := by decide
theorem prefix_5_111 : PrefixCertificate (10^111) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137484754088075 := by decide
theorem prefix_5_112 : PrefixCertificate (10^112) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540880753 := by decide
theorem prefix_5_113 : PrefixCertificate (10^113) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939113748475408807538 := by decide
theorem prefix_5_114 : PrefixCertificate (10^114) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137484754088075386 := by decide
theorem prefix_5_115 : PrefixCertificate (10^115) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540880753868 := by decide
theorem prefix_5_116 : PrefixCertificate (10^116) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939113748475408807538689 := by decide
theorem prefix_5_117 : PrefixCertificate (10^117) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137484754088075386891 := by decide
theorem prefix_5_118 : PrefixCertificate (10^118) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540880753868917 := by decide
theorem prefix_5_119 : PrefixCertificate (10^119) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939113748475408807538689175 := by decide
theorem prefix_5_120 : PrefixCertificate (10^120) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137484754088075386891752 := by decide
theorem prefix_5_121 : PrefixCertificate (10^121) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540880753868917521 := by decide
theorem prefix_5_122 : PrefixCertificate (10^122) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939113748475408807538689175212 := by decide
theorem prefix_5_123 : PrefixCertificate (10^123) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137484754088075386891752126 := by decide
theorem prefix_5_124 : PrefixCertificate (10^124) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540880753868917521266 := by decide
theorem prefix_5_125 : PrefixCertificate (10^125) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939113748475408807538689175212663 := by decide
theorem prefix_5_126 : PrefixCertificate (10^126) 618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137484754088075386891752126633 := by decide
theorem prefix_5_127 : PrefixCertificate (10^127) 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540880753868917521266338 := by decide
theorem prefix_5_128 : PrefixCertificate (10^128) 61803398874989484820458683436563811772030917980576286213544862270526046281890244970720720418939113748475408807538689175212663386 := by decide
theorem digit_5_0 : digit 10 0 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_0 prefix_5_1
theorem digit_5_1 : digit 10 1 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_1 prefix_5_2
theorem digit_5_2 : digit 10 2 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_2 prefix_5_3
theorem digit_5_3 : digit 10 3 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_3 prefix_5_4
theorem digit_5_4 : digit 10 4 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_4 prefix_5_5
theorem digit_5_5 : digit 10 5 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_5 prefix_5_6
theorem digit_5_6 : digit 10 6 = (9 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_6 prefix_5_7
theorem digit_5_7 : digit 10 7 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_7 prefix_5_8
theorem digit_5_8 : digit 10 8 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_8 prefix_5_9
theorem digit_5_9 : digit 10 9 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_9 prefix_5_10
theorem digit_5_10 : digit 10 10 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_10 prefix_5_11
theorem digit_5_11 : digit 10 11 = (9 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_11 prefix_5_12
theorem digit_5_12 : digit 10 12 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_12 prefix_5_13
theorem digit_5_13 : digit 10 13 = (9 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_13 prefix_5_14
theorem digit_5_14 : digit 10 14 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_14 prefix_5_15
theorem digit_5_15 : digit 10 15 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_15 prefix_5_16
theorem digit_5_16 : digit 10 16 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_16 prefix_5_17
theorem digit_5_17 : digit 10 17 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_17 prefix_5_18
theorem digit_5_18 : digit 10 18 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_18 prefix_5_19
theorem digit_5_19 : digit 10 19 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_19 prefix_5_20
theorem digit_5_20 : digit 10 20 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_20 prefix_5_21
theorem digit_5_21 : digit 10 21 = (5 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_21 prefix_5_22
theorem digit_5_22 : digit 10 22 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_22 prefix_5_23
theorem digit_5_23 : digit 10 23 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_23 prefix_5_24
theorem digit_5_24 : digit 10 24 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_24 prefix_5_25
theorem digit_5_25 : digit 10 25 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_25 prefix_5_26
theorem digit_5_26 : digit 10 26 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_26 prefix_5_27
theorem digit_5_27 : digit 10 27 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_27 prefix_5_28
theorem digit_5_28 : digit 10 28 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_28 prefix_5_29
theorem digit_5_29 : digit 10 29 = (5 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_29 prefix_5_30
theorem digit_5_30 : digit 10 30 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_30 prefix_5_31
theorem digit_5_31 : digit 10 31 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_31 prefix_5_32
theorem digit_5_32 : digit 10 32 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_32 prefix_5_33
theorem digit_5_33 : digit 10 33 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_33 prefix_5_34
theorem digit_5_34 : digit 10 34 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_34 prefix_5_35
theorem digit_5_35 : digit 10 35 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_35 prefix_5_36
theorem digit_5_36 : digit 10 36 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_36 prefix_5_37
theorem digit_5_37 : digit 10 37 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_37 prefix_5_38
theorem digit_5_38 : digit 10 38 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_38 prefix_5_39
theorem digit_5_39 : digit 10 39 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_39 prefix_5_40
theorem digit_5_40 : digit 10 40 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_40 prefix_5_41
theorem digit_5_41 : digit 10 41 = (9 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_41 prefix_5_42
theorem digit_5_42 : digit 10 42 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_42 prefix_5_43
theorem digit_5_43 : digit 10 43 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_43 prefix_5_44
theorem digit_5_44 : digit 10 44 = (9 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_44 prefix_5_45
theorem digit_5_45 : digit 10 45 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_45 prefix_5_46
theorem digit_5_46 : digit 10 46 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_46 prefix_5_47
theorem digit_5_47 : digit 10 47 = (5 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_47 prefix_5_48
theorem digit_5_48 : digit 10 48 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_48 prefix_5_49
theorem digit_5_49 : digit 10 49 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_49 prefix_5_50
theorem digit_5_50 : digit 10 50 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_50 prefix_5_51
theorem digit_5_51 : digit 10 51 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_51 prefix_5_52
theorem digit_5_52 : digit 10 52 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_52 prefix_5_53
theorem digit_5_53 : digit 10 53 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_53 prefix_5_54
theorem digit_5_54 : digit 10 54 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_54 prefix_5_55
theorem digit_5_55 : digit 10 55 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_55 prefix_5_56
theorem digit_5_56 : digit 10 56 = (5 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_56 prefix_5_57
theorem digit_5_57 : digit 10 57 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_57 prefix_5_58
theorem digit_5_58 : digit 10 58 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_58 prefix_5_59
theorem digit_5_59 : digit 10 59 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_59 prefix_5_60
theorem digit_5_60 : digit 10 60 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_60 prefix_5_61
theorem digit_5_61 : digit 10 61 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_61 prefix_5_62
theorem digit_5_62 : digit 10 62 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_62 prefix_5_63
theorem digit_5_63 : digit 10 63 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_63 prefix_5_64
theorem digit_5_64 : digit 10 64 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_64 prefix_5_65
theorem digit_5_65 : digit 10 65 = (5 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_65 prefix_5_66
theorem digit_5_66 : digit 10 66 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_66 prefix_5_67
theorem digit_5_67 : digit 10 67 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_67 prefix_5_68
theorem digit_5_68 : digit 10 68 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_68 prefix_5_69
theorem digit_5_69 : digit 10 69 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_69 prefix_5_70
theorem digit_5_70 : digit 10 70 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_70 prefix_5_71
theorem digit_5_71 : digit 10 71 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_71 prefix_5_72
theorem digit_5_72 : digit 10 72 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_72 prefix_5_73
theorem digit_5_73 : digit 10 73 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_73 prefix_5_74
theorem digit_5_74 : digit 10 74 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_74 prefix_5_75
theorem digit_5_75 : digit 10 75 = (9 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_75 prefix_5_76
theorem digit_5_76 : digit 10 76 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_76 prefix_5_77
theorem digit_5_77 : digit 10 77 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_77 prefix_5_78
theorem digit_5_78 : digit 10 78 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_78 prefix_5_79
theorem digit_5_79 : digit 10 79 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_79 prefix_5_80
theorem digit_5_80 : digit 10 80 = (9 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_80 prefix_5_81
theorem digit_5_81 : digit 10 81 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_81 prefix_5_82
theorem digit_5_82 : digit 10 82 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_82 prefix_5_83
theorem digit_5_83 : digit 10 83 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_83 prefix_5_84
theorem digit_5_84 : digit 10 84 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_84 prefix_5_85
theorem digit_5_85 : digit 10 85 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_85 prefix_5_86
theorem digit_5_86 : digit 10 86 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_86 prefix_5_87
theorem digit_5_87 : digit 10 87 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_87 prefix_5_88
theorem digit_5_88 : digit 10 88 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_88 prefix_5_89
theorem digit_5_89 : digit 10 89 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_89 prefix_5_90
theorem digit_5_90 : digit 10 90 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_90 prefix_5_91
theorem digit_5_91 : digit 10 91 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_91 prefix_5_92
theorem digit_5_92 : digit 10 92 = (9 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_92 prefix_5_93
theorem digit_5_93 : digit 10 93 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_93 prefix_5_94
theorem digit_5_94 : digit 10 94 = (9 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_94 prefix_5_95
theorem digit_5_95 : digit 10 95 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_95 prefix_5_96
theorem digit_5_96 : digit 10 96 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_96 prefix_5_97
theorem digit_5_97 : digit 10 97 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_97 prefix_5_98
theorem digit_5_98 : digit 10 98 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_98 prefix_5_99
theorem digit_5_99 : digit 10 99 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_99 prefix_5_100
theorem digit_5_100 : digit 10 100 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_100 prefix_5_101
theorem digit_5_101 : digit 10 101 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_101 prefix_5_102
theorem digit_5_102 : digit 10 102 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_102 prefix_5_103
theorem digit_5_103 : digit 10 103 = (5 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_103 prefix_5_104
theorem digit_5_104 : digit 10 104 = (4 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_104 prefix_5_105
theorem digit_5_105 : digit 10 105 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_105 prefix_5_106
theorem digit_5_106 : digit 10 106 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_106 prefix_5_107
theorem digit_5_107 : digit 10 107 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_107 prefix_5_108
theorem digit_5_108 : digit 10 108 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_108 prefix_5_109
theorem digit_5_109 : digit 10 109 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_109 prefix_5_110
theorem digit_5_110 : digit 10 110 = (5 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_110 prefix_5_111
theorem digit_5_111 : digit 10 111 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_111 prefix_5_112
theorem digit_5_112 : digit 10 112 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_112 prefix_5_113
theorem digit_5_113 : digit 10 113 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_113 prefix_5_114
theorem digit_5_114 : digit 10 114 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_114 prefix_5_115
theorem digit_5_115 : digit 10 115 = (9 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_115 prefix_5_116
theorem digit_5_116 : digit 10 116 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_116 prefix_5_117
theorem digit_5_117 : digit 10 117 = (7 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_117 prefix_5_118
theorem digit_5_118 : digit 10 118 = (5 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_118 prefix_5_119
theorem digit_5_119 : digit 10 119 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_119 prefix_5_120
theorem digit_5_120 : digit 10 120 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_120 prefix_5_121
theorem digit_5_121 : digit 10 121 = (2 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_121 prefix_5_122
theorem digit_5_122 : digit 10 122 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_122 prefix_5_123
theorem digit_5_123 : digit 10 123 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_123 prefix_5_124
theorem digit_5_124 : digit 10 124 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_124 prefix_5_125
theorem digit_5_125 : digit 10 125 = (3 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_125 prefix_5_126
theorem digit_5_126 : digit 10 126 = (8 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_126 prefix_5_127
theorem digit_5_127 : digit 10 127 = (6 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_5_127 prefix_5_128
theorem digits_5 : DigitsAt 10 0 word_5 := And.intro digit_5_0 (And.intro digit_5_1 (And.intro digit_5_2 (And.intro digit_5_3 (And.intro digit_5_4 (And.intro digit_5_5 (And.intro digit_5_6 (And.intro digit_5_7 (And.intro digit_5_8 (And.intro digit_5_9 (And.intro digit_5_10 (And.intro digit_5_11 (And.intro digit_5_12 (And.intro digit_5_13 (And.intro digit_5_14 (And.intro digit_5_15 (And.intro digit_5_16 (And.intro digit_5_17 (And.intro digit_5_18 (And.intro digit_5_19 (And.intro digit_5_20 (And.intro digit_5_21 (And.intro digit_5_22 (And.intro digit_5_23 (And.intro digit_5_24 (And.intro digit_5_25 (And.intro digit_5_26 (And.intro digit_5_27 (And.intro digit_5_28 (And.intro digit_5_29 (And.intro digit_5_30 (And.intro digit_5_31 (And.intro digit_5_32 (And.intro digit_5_33 (And.intro digit_5_34 (And.intro digit_5_35 (And.intro digit_5_36 (And.intro digit_5_37 (And.intro digit_5_38 (And.intro digit_5_39 (And.intro digit_5_40 (And.intro digit_5_41 (And.intro digit_5_42 (And.intro digit_5_43 (And.intro digit_5_44 (And.intro digit_5_45 (And.intro digit_5_46 (And.intro digit_5_47 (And.intro digit_5_48 (And.intro digit_5_49 (And.intro digit_5_50 (And.intro digit_5_51 (And.intro digit_5_52 (And.intro digit_5_53 (And.intro digit_5_54 (And.intro digit_5_55 (And.intro digit_5_56 (And.intro digit_5_57 (And.intro digit_5_58 (And.intro digit_5_59 (And.intro digit_5_60 (And.intro digit_5_61 (And.intro digit_5_62 (And.intro digit_5_63 (And.intro digit_5_64 (And.intro digit_5_65 (And.intro digit_5_66 (And.intro digit_5_67 (And.intro digit_5_68 (And.intro digit_5_69 (And.intro digit_5_70 (And.intro digit_5_71 (And.intro digit_5_72 (And.intro digit_5_73 (And.intro digit_5_74 (And.intro digit_5_75 (And.intro digit_5_76 (And.intro digit_5_77 (And.intro digit_5_78 (And.intro digit_5_79 (And.intro digit_5_80 (And.intro digit_5_81 (And.intro digit_5_82 (And.intro digit_5_83 (And.intro digit_5_84 (And.intro digit_5_85 (And.intro digit_5_86 (And.intro digit_5_87 (And.intro digit_5_88 (And.intro digit_5_89 (And.intro digit_5_90 (And.intro digit_5_91 (And.intro digit_5_92 (And.intro digit_5_93 (And.intro digit_5_94 (And.intro digit_5_95 (And.intro digit_5_96 (And.intro digit_5_97 (And.intro digit_5_98 (And.intro digit_5_99 (And.intro digit_5_100 (And.intro digit_5_101 (And.intro digit_5_102 (And.intro digit_5_103 (And.intro digit_5_104 (And.intro digit_5_105 (And.intro digit_5_106 (And.intro digit_5_107 (And.intro digit_5_108 (And.intro digit_5_109 (And.intro digit_5_110 (And.intro digit_5_111 (And.intro digit_5_112 (And.intro digit_5_113 (And.intro digit_5_114 (And.intro digit_5_115 (And.intro digit_5_116 (And.intro digit_5_117 (And.intro digit_5_118 (And.intro digit_5_119 (And.intro digit_5_120 (And.intro digit_5_121 (And.intro digit_5_122 (And.intro digit_5_123 (And.intro digit_5_124 (And.intro digit_5_125 (And.intro digit_5_126 (And.intro digit_5_127 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem count_5_0 : Blocks.count [0, 0] word_5 = 0 := by decide
theorem actualCount_5_0 : Blocks.enumeratedCount [0, 0]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_0
theorem occurrence_5_0 : occurrences 10 2 0 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [0, 0])
    (by decide) (by decide) (by decide) digits_5 count_5_0
theorem discrepancy_5_0 :
    Nat.dist (10^2 * occurrences 10 2 0 127) 127 = 127 := by
  rw [occurrence_5_0]
  decide
theorem count_5_1 : Blocks.count [0, 1] word_5 = 0 := by decide
theorem actualCount_5_1 : Blocks.enumeratedCount [0, 1]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_1
theorem occurrence_5_1 : occurrences 10 2 1 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [0, 1])
    (by decide) (by decide) (by decide) digits_5 count_5_1
theorem discrepancy_5_1 :
    Nat.dist (10^2 * occurrences 10 2 1 127) 127 = 127 := by
  rw [occurrence_5_1]
  decide
theorem count_5_2 : Blocks.count [0, 2] word_5 = 1 := by decide
theorem actualCount_5_2 : Blocks.enumeratedCount [0, 2]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_2
theorem occurrence_5_2 : occurrences 10 2 2 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [0, 2])
    (by decide) (by decide) (by decide) digits_5 count_5_2
theorem discrepancy_5_2 :
    Nat.dist (10^2 * occurrences 10 2 2 127) 127 = 27 := by
  rw [occurrence_5_2]
  decide
theorem count_5_3 : Blocks.count [0, 3] word_5 = 2 := by decide
theorem actualCount_5_3 : Blocks.enumeratedCount [0, 3]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_3
theorem occurrence_5_3 : occurrences 10 2 3 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [0, 3])
    (by decide) (by decide) (by decide) digits_5 count_5_3
theorem discrepancy_5_3 :
    Nat.dist (10^2 * occurrences 10 2 3 127) 127 = 73 := by
  rw [occurrence_5_3]
  decide
theorem count_5_4 : Blocks.count [0, 4] word_5 = 3 := by decide
theorem actualCount_5_4 : Blocks.enumeratedCount [0, 4]
    (actualDigits 10 0 word_5.length) = 3 :=
  certified_count_sound digits_5 count_5_4
theorem occurrence_5_4 : occurrences 10 2 4 127 = 3 :=
  certified_occurrences_sound (b := 10) (value := 3)
    (text := word_5) (pattern := [0, 4])
    (by decide) (by decide) (by decide) digits_5 count_5_4
theorem discrepancy_5_4 :
    Nat.dist (10^2 * occurrences 10 2 4 127) 127 = 173 := by
  rw [occurrence_5_4]
  decide
theorem count_5_5 : Blocks.count [0, 5] word_5 = 2 := by decide
theorem actualCount_5_5 : Blocks.enumeratedCount [0, 5]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_5
theorem occurrence_5_5 : occurrences 10 2 5 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [0, 5])
    (by decide) (by decide) (by decide) digits_5 count_5_5
theorem discrepancy_5_5 :
    Nat.dist (10^2 * occurrences 10 2 5 127) 127 = 73 := by
  rw [occurrence_5_5]
  decide
theorem count_5_6 : Blocks.count [0, 6] word_5 = 0 := by decide
theorem actualCount_5_6 : Blocks.enumeratedCount [0, 6]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_6
theorem occurrence_5_6 : occurrences 10 2 6 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [0, 6])
    (by decide) (by decide) (by decide) digits_5 count_5_6
theorem discrepancy_5_6 :
    Nat.dist (10^2 * occurrences 10 2 6 127) 127 = 127 := by
  rw [occurrence_5_6]
  decide
theorem count_5_7 : Blocks.count [0, 7] word_5 = 3 := by decide
theorem actualCount_5_7 : Blocks.enumeratedCount [0, 7]
    (actualDigits 10 0 word_5.length) = 3 :=
  certified_count_sound digits_5 count_5_7
theorem occurrence_5_7 : occurrences 10 2 7 127 = 3 :=
  certified_occurrences_sound (b := 10) (value := 3)
    (text := word_5) (pattern := [0, 7])
    (by decide) (by decide) (by decide) digits_5 count_5_7
theorem discrepancy_5_7 :
    Nat.dist (10^2 * occurrences 10 2 7 127) 127 = 173 := by
  rw [occurrence_5_7]
  decide
theorem count_5_8 : Blocks.count [0, 8] word_5 = 1 := by decide
theorem actualCount_5_8 : Blocks.enumeratedCount [0, 8]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_8
theorem occurrence_5_8 : occurrences 10 2 8 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [0, 8])
    (by decide) (by decide) (by decide) digits_5 count_5_8
theorem discrepancy_5_8 :
    Nat.dist (10^2 * occurrences 10 2 8 127) 127 = 27 := by
  rw [occurrence_5_8]
  decide
theorem count_5_9 : Blocks.count [0, 9] word_5 = 1 := by decide
theorem actualCount_5_9 : Blocks.enumeratedCount [0, 9]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_9
theorem occurrence_5_9 : occurrences 10 2 9 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [0, 9])
    (by decide) (by decide) (by decide) digits_5 count_5_9
theorem discrepancy_5_9 :
    Nat.dist (10^2 * occurrences 10 2 9 127) 127 = 27 := by
  rw [occurrence_5_9]
  decide
theorem count_5_10 : Blocks.count [1, 0] word_5 = 0 := by decide
theorem actualCount_5_10 : Blocks.enumeratedCount [1, 0]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_10
theorem occurrence_5_10 : occurrences 10 2 10 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [1, 0])
    (by decide) (by decide) (by decide) digits_5 count_5_10
theorem discrepancy_5_10 :
    Nat.dist (10^2 * occurrences 10 2 10 127) 127 = 127 := by
  rw [occurrence_5_10]
  decide
theorem count_5_11 : Blocks.count [1, 1] word_5 = 2 := by decide
theorem actualCount_5_11 : Blocks.enumeratedCount [1, 1]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_11
theorem occurrence_5_11 : occurrences 10 2 11 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [1, 1])
    (by decide) (by decide) (by decide) digits_5 count_5_11
theorem discrepancy_5_11 :
    Nat.dist (10^2 * occurrences 10 2 11 127) 127 = 73 := by
  rw [occurrence_5_11]
  decide
theorem count_5_12 : Blocks.count [1, 2] word_5 = 1 := by decide
theorem actualCount_5_12 : Blocks.enumeratedCount [1, 2]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_12
theorem occurrence_5_12 : occurrences 10 2 12 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [1, 2])
    (by decide) (by decide) (by decide) digits_5 count_5_12
theorem discrepancy_5_12 :
    Nat.dist (10^2 * occurrences 10 2 12 127) 127 = 27 := by
  rw [occurrence_5_12]
  decide
theorem count_5_13 : Blocks.count [1, 3] word_5 = 2 := by decide
theorem actualCount_5_13 : Blocks.enumeratedCount [1, 3]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_13
theorem occurrence_5_13 : occurrences 10 2 13 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [1, 3])
    (by decide) (by decide) (by decide) digits_5 count_5_13
theorem discrepancy_5_13 :
    Nat.dist (10^2 * occurrences 10 2 13 127) 127 = 73 := by
  rw [occurrence_5_13]
  decide
theorem count_5_14 : Blocks.count [1, 4] word_5 = 0 := by decide
theorem actualCount_5_14 : Blocks.enumeratedCount [1, 4]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_14
theorem occurrence_5_14 : occurrences 10 2 14 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [1, 4])
    (by decide) (by decide) (by decide) digits_5 count_5_14
theorem discrepancy_5_14 :
    Nat.dist (10^2 * occurrences 10 2 14 127) 127 = 127 := by
  rw [occurrence_5_14]
  decide
theorem count_5_15 : Blocks.count [1, 5] word_5 = 0 := by decide
theorem actualCount_5_15 : Blocks.enumeratedCount [1, 5]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_15
theorem occurrence_5_15 : occurrences 10 2 15 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [1, 5])
    (by decide) (by decide) (by decide) digits_5 count_5_15
theorem discrepancy_5_15 :
    Nat.dist (10^2 * occurrences 10 2 15 127) 127 = 127 := by
  rw [occurrence_5_15]
  decide
theorem count_5_16 : Blocks.count [1, 6] word_5 = 0 := by decide
theorem actualCount_5_16 : Blocks.enumeratedCount [1, 6]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_16
theorem occurrence_5_16 : occurrences 10 2 16 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [1, 6])
    (by decide) (by decide) (by decide) digits_5 count_5_16
theorem discrepancy_5_16 :
    Nat.dist (10^2 * occurrences 10 2 16 127) 127 = 127 := by
  rw [occurrence_5_16]
  decide
theorem count_5_17 : Blocks.count [1, 7] word_5 = 3 := by decide
theorem actualCount_5_17 : Blocks.enumeratedCount [1, 7]
    (actualDigits 10 0 word_5.length) = 3 :=
  certified_count_sound digits_5 count_5_17
theorem occurrence_5_17 : occurrences 10 2 17 127 = 3 :=
  certified_occurrences_sound (b := 10) (value := 3)
    (text := word_5) (pattern := [1, 7])
    (by decide) (by decide) (by decide) digits_5 count_5_17
theorem discrepancy_5_17 :
    Nat.dist (10^2 * occurrences 10 2 17 127) 127 = 173 := by
  rw [occurrence_5_17]
  decide
theorem count_5_18 : Blocks.count [1, 8] word_5 = 3 := by decide
theorem actualCount_5_18 : Blocks.enumeratedCount [1, 8]
    (actualDigits 10 0 word_5.length) = 3 :=
  certified_count_sound digits_5 count_5_18
theorem occurrence_5_18 : occurrences 10 2 18 127 = 3 :=
  certified_occurrences_sound (b := 10) (value := 3)
    (text := word_5) (pattern := [1, 8])
    (by decide) (by decide) (by decide) digits_5 count_5_18
theorem discrepancy_5_18 :
    Nat.dist (10^2 * occurrences 10 2 18 127) 127 = 173 := by
  rw [occurrence_5_18]
  decide
theorem count_5_19 : Blocks.count [1, 9] word_5 = 0 := by decide
theorem actualCount_5_19 : Blocks.enumeratedCount [1, 9]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_19
theorem occurrence_5_19 : occurrences 10 2 19 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [1, 9])
    (by decide) (by decide) (by decide) digits_5 count_5_19
theorem discrepancy_5_19 :
    Nat.dist (10^2 * occurrences 10 2 19 127) 127 = 127 := by
  rw [occurrence_5_19]
  decide
theorem count_5_20 : Blocks.count [2, 0] word_5 = 4 := by decide
theorem actualCount_5_20 : Blocks.enumeratedCount [2, 0]
    (actualDigits 10 0 word_5.length) = 4 :=
  certified_count_sound digits_5 count_5_20
theorem occurrence_5_20 : occurrences 10 2 20 127 = 4 :=
  certified_occurrences_sound (b := 10) (value := 4)
    (text := word_5) (pattern := [2, 0])
    (by decide) (by decide) (by decide) digits_5 count_5_20
theorem discrepancy_5_20 :
    Nat.dist (10^2 * occurrences 10 2 20 127) 127 = 273 := by
  rw [occurrence_5_20]
  decide
theorem count_5_21 : Blocks.count [2, 1] word_5 = 2 := by decide
theorem actualCount_5_21 : Blocks.enumeratedCount [2, 1]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_21
theorem occurrence_5_21 : occurrences 10 2 21 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [2, 1])
    (by decide) (by decide) (by decide) digits_5 count_5_21
theorem discrepancy_5_21 :
    Nat.dist (10^2 * occurrences 10 2 21 127) 127 = 73 := by
  rw [occurrence_5_21]
  decide
theorem count_5_22 : Blocks.count [2, 2] word_5 = 1 := by decide
theorem actualCount_5_22 : Blocks.enumeratedCount [2, 2]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_22
theorem occurrence_5_22 : occurrences 10 2 22 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [2, 2])
    (by decide) (by decide) (by decide) digits_5 count_5_22
theorem discrepancy_5_22 :
    Nat.dist (10^2 * occurrences 10 2 22 127) 127 = 27 := by
  rw [occurrence_5_22]
  decide
theorem count_5_23 : Blocks.count [2, 3] word_5 = 0 := by decide
theorem actualCount_5_23 : Blocks.enumeratedCount [2, 3]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_23
theorem occurrence_5_23 : occurrences 10 2 23 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [2, 3])
    (by decide) (by decide) (by decide) digits_5 count_5_23
theorem discrepancy_5_23 :
    Nat.dist (10^2 * occurrences 10 2 23 127) 127 = 127 := by
  rw [occurrence_5_23]
  decide
theorem count_5_24 : Blocks.count [2, 4] word_5 = 1 := by decide
theorem actualCount_5_24 : Blocks.enumeratedCount [2, 4]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_24
theorem occurrence_5_24 : occurrences 10 2 24 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [2, 4])
    (by decide) (by decide) (by decide) digits_5 count_5_24
theorem discrepancy_5_24 :
    Nat.dist (10^2 * occurrences 10 2 24 127) 127 = 27 := by
  rw [occurrence_5_24]
  decide
theorem count_5_25 : Blocks.count [2, 5] word_5 = 0 := by decide
theorem actualCount_5_25 : Blocks.enumeratedCount [2, 5]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_25
theorem occurrence_5_25 : occurrences 10 2 25 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [2, 5])
    (by decide) (by decide) (by decide) digits_5 count_5_25
theorem discrepancy_5_25 :
    Nat.dist (10^2 * occurrences 10 2 25 127) 127 = 127 := by
  rw [occurrence_5_25]
  decide
theorem count_5_26 : Blocks.count [2, 6] word_5 = 2 := by decide
theorem actualCount_5_26 : Blocks.enumeratedCount [2, 6]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_26
theorem occurrence_5_26 : occurrences 10 2 26 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [2, 6])
    (by decide) (by decide) (by decide) digits_5 count_5_26
theorem discrepancy_5_26 :
    Nat.dist (10^2 * occurrences 10 2 26 127) 127 = 73 := by
  rw [occurrence_5_26]
  decide
theorem count_5_27 : Blocks.count [2, 7] word_5 = 1 := by decide
theorem actualCount_5_27 : Blocks.enumeratedCount [2, 7]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_27
theorem occurrence_5_27 : occurrences 10 2 27 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [2, 7])
    (by decide) (by decide) (by decide) digits_5 count_5_27
theorem discrepancy_5_27 :
    Nat.dist (10^2 * occurrences 10 2 27 127) 127 = 27 := by
  rw [occurrence_5_27]
  decide
theorem count_5_28 : Blocks.count [2, 8] word_5 = 2 := by decide
theorem actualCount_5_28 : Blocks.enumeratedCount [2, 8]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_28
theorem occurrence_5_28 : occurrences 10 2 28 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [2, 8])
    (by decide) (by decide) (by decide) digits_5 count_5_28
theorem discrepancy_5_28 :
    Nat.dist (10^2 * occurrences 10 2 28 127) 127 = 73 := by
  rw [occurrence_5_28]
  decide
theorem count_5_29 : Blocks.count [2, 9] word_5 = 0 := by decide
theorem actualCount_5_29 : Blocks.enumeratedCount [2, 9]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_29
theorem occurrence_5_29 : occurrences 10 2 29 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [2, 9])
    (by decide) (by decide) (by decide) digits_5 count_5_29
theorem discrepancy_5_29 :
    Nat.dist (10^2 * occurrences 10 2 29 127) 127 = 127 := by
  rw [occurrence_5_29]
  decide
theorem count_5_30 : Blocks.count [3, 0] word_5 = 1 := by decide
theorem actualCount_5_30 : Blocks.enumeratedCount [3, 0]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_30
theorem occurrence_5_30 : occurrences 10 2 30 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [3, 0])
    (by decide) (by decide) (by decide) digits_5 count_5_30
theorem discrepancy_5_30 :
    Nat.dist (10^2 * occurrences 10 2 30 127) 127 = 27 := by
  rw [occurrence_5_30]
  decide
theorem count_5_31 : Blocks.count [3, 1] word_5 = 0 := by decide
theorem actualCount_5_31 : Blocks.enumeratedCount [3, 1]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_31
theorem occurrence_5_31 : occurrences 10 2 31 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [3, 1])
    (by decide) (by decide) (by decide) digits_5 count_5_31
theorem discrepancy_5_31 :
    Nat.dist (10^2 * occurrences 10 2 31 127) 127 = 127 := by
  rw [occurrence_5_31]
  decide
theorem count_5_32 : Blocks.count [3, 2] word_5 = 0 := by decide
theorem actualCount_5_32 : Blocks.enumeratedCount [3, 2]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_32
theorem occurrence_5_32 : occurrences 10 2 32 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [3, 2])
    (by decide) (by decide) (by decide) digits_5 count_5_32
theorem discrepancy_5_32 :
    Nat.dist (10^2 * occurrences 10 2 32 127) 127 = 127 := by
  rw [occurrence_5_32]
  decide
theorem count_5_33 : Blocks.count [3, 3] word_5 = 2 := by decide
theorem actualCount_5_33 : Blocks.enumeratedCount [3, 3]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_33
theorem occurrence_5_33 : occurrences 10 2 33 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [3, 3])
    (by decide) (by decide) (by decide) digits_5 count_5_33
theorem discrepancy_5_33 :
    Nat.dist (10^2 * occurrences 10 2 33 127) 127 = 73 := by
  rw [occurrence_5_33]
  decide
theorem count_5_34 : Blocks.count [3, 4] word_5 = 1 := by decide
theorem actualCount_5_34 : Blocks.enumeratedCount [3, 4]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_34
theorem occurrence_5_34 : occurrences 10 2 34 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [3, 4])
    (by decide) (by decide) (by decide) digits_5 count_5_34
theorem discrepancy_5_34 :
    Nat.dist (10^2 * occurrences 10 2 34 127) 127 = 27 := by
  rw [occurrence_5_34]
  decide
theorem count_5_35 : Blocks.count [3, 5] word_5 = 1 := by decide
theorem actualCount_5_35 : Blocks.enumeratedCount [3, 5]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_35
theorem occurrence_5_35 : occurrences 10 2 35 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [3, 5])
    (by decide) (by decide) (by decide) digits_5 count_5_35
theorem discrepancy_5_35 :
    Nat.dist (10^2 * occurrences 10 2 35 127) 127 = 27 := by
  rw [occurrence_5_35]
  decide
theorem count_5_36 : Blocks.count [3, 6] word_5 = 1 := by decide
theorem actualCount_5_36 : Blocks.enumeratedCount [3, 6]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_36
theorem occurrence_5_36 : occurrences 10 2 36 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [3, 6])
    (by decide) (by decide) (by decide) digits_5 count_5_36
theorem discrepancy_5_36 :
    Nat.dist (10^2 * occurrences 10 2 36 127) 127 = 27 := by
  rw [occurrence_5_36]
  decide
theorem count_5_37 : Blocks.count [3, 7] word_5 = 1 := by decide
theorem actualCount_5_37 : Blocks.enumeratedCount [3, 7]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_37
theorem occurrence_5_37 : occurrences 10 2 37 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [3, 7])
    (by decide) (by decide) (by decide) digits_5 count_5_37
theorem discrepancy_5_37 :
    Nat.dist (10^2 * occurrences 10 2 37 127) 127 = 27 := by
  rw [occurrence_5_37]
  decide
theorem count_5_38 : Blocks.count [3, 8] word_5 = 3 := by decide
theorem actualCount_5_38 : Blocks.enumeratedCount [3, 8]
    (actualDigits 10 0 word_5.length) = 3 :=
  certified_count_sound digits_5 count_5_38
theorem occurrence_5_38 : occurrences 10 2 38 127 = 3 :=
  certified_occurrences_sound (b := 10) (value := 3)
    (text := word_5) (pattern := [3, 8])
    (by decide) (by decide) (by decide) digits_5 count_5_38
theorem discrepancy_5_38 :
    Nat.dist (10^2 * occurrences 10 2 38 127) 127 = 173 := by
  rw [occurrence_5_38]
  decide
theorem count_5_39 : Blocks.count [3, 9] word_5 = 2 := by decide
theorem actualCount_5_39 : Blocks.enumeratedCount [3, 9]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_39
theorem occurrence_5_39 : occurrences 10 2 39 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [3, 9])
    (by decide) (by decide) (by decide) digits_5 count_5_39
theorem discrepancy_5_39 :
    Nat.dist (10^2 * occurrences 10 2 39 127) 127 = 73 := by
  rw [occurrence_5_39]
  decide
theorem count_5_40 : Blocks.count [4, 0] word_5 = 1 := by decide
theorem actualCount_5_40 : Blocks.enumeratedCount [4, 0]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_40
theorem occurrence_5_40 : occurrences 10 2 40 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [4, 0])
    (by decide) (by decide) (by decide) digits_5 count_5_40
theorem discrepancy_5_40 :
    Nat.dist (10^2 * occurrences 10 2 40 127) 127 = 27 := by
  rw [occurrence_5_40]
  decide
theorem count_5_41 : Blocks.count [4, 1] word_5 = 1 := by decide
theorem actualCount_5_41 : Blocks.enumeratedCount [4, 1]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_41
theorem occurrence_5_41 : occurrences 10 2 41 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [4, 1])
    (by decide) (by decide) (by decide) digits_5 count_5_41
theorem discrepancy_5_41 :
    Nat.dist (10^2 * occurrences 10 2 41 127) 127 = 27 := by
  rw [occurrence_5_41]
  decide
theorem count_5_42 : Blocks.count [4, 2] word_5 = 0 := by decide
theorem actualCount_5_42 : Blocks.enumeratedCount [4, 2]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_42
theorem occurrence_5_42 : occurrences 10 2 42 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [4, 2])
    (by decide) (by decide) (by decide) digits_5 count_5_42
theorem discrepancy_5_42 :
    Nat.dist (10^2 * occurrences 10 2 42 127) 127 = 127 := by
  rw [occurrence_5_42]
  decide
theorem count_5_43 : Blocks.count [4, 3] word_5 = 1 := by decide
theorem actualCount_5_43 : Blocks.enumeratedCount [4, 3]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_43
theorem occurrence_5_43 : occurrences 10 2 43 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [4, 3])
    (by decide) (by decide) (by decide) digits_5 count_5_43
theorem discrepancy_5_43 :
    Nat.dist (10^2 * occurrences 10 2 43 127) 127 = 27 := by
  rw [occurrence_5_43]
  decide
theorem count_5_44 : Blocks.count [4, 4] word_5 = 2 := by decide
theorem actualCount_5_44 : Blocks.enumeratedCount [4, 4]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_44
theorem occurrence_5_44 : occurrences 10 2 44 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [4, 4])
    (by decide) (by decide) (by decide) digits_5 count_5_44
theorem discrepancy_5_44 :
    Nat.dist (10^2 * occurrences 10 2 44 127) 127 = 73 := by
  rw [occurrence_5_44]
  decide
theorem count_5_45 : Blocks.count [4, 5] word_5 = 1 := by decide
theorem actualCount_5_45 : Blocks.enumeratedCount [4, 5]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_45
theorem occurrence_5_45 : occurrences 10 2 45 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [4, 5])
    (by decide) (by decide) (by decide) digits_5 count_5_45
theorem discrepancy_5_45 :
    Nat.dist (10^2 * occurrences 10 2 45 127) 127 = 27 := by
  rw [occurrence_5_45]
  decide
theorem count_5_46 : Blocks.count [4, 6] word_5 = 1 := by decide
theorem actualCount_5_46 : Blocks.enumeratedCount [4, 6]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_46
theorem occurrence_5_46 : occurrences 10 2 46 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [4, 6])
    (by decide) (by decide) (by decide) digits_5 count_5_46
theorem discrepancy_5_46 :
    Nat.dist (10^2 * occurrences 10 2 46 127) 127 = 27 := by
  rw [occurrence_5_46]
  decide
theorem count_5_47 : Blocks.count [4, 7] word_5 = 1 := by decide
theorem actualCount_5_47 : Blocks.enumeratedCount [4, 7]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_47
theorem occurrence_5_47 : occurrences 10 2 47 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [4, 7])
    (by decide) (by decide) (by decide) digits_5 count_5_47
theorem discrepancy_5_47 :
    Nat.dist (10^2 * occurrences 10 2 47 127) 127 = 27 := by
  rw [occurrence_5_47]
  decide
theorem count_5_48 : Blocks.count [4, 8] word_5 = 4 := by decide
theorem actualCount_5_48 : Blocks.enumeratedCount [4, 8]
    (actualDigits 10 0 word_5.length) = 4 :=
  certified_count_sound digits_5 count_5_48
theorem occurrence_5_48 : occurrences 10 2 48 127 = 4 :=
  certified_occurrences_sound (b := 10) (value := 4)
    (text := word_5) (pattern := [4, 8])
    (by decide) (by decide) (by decide) digits_5 count_5_48
theorem discrepancy_5_48 :
    Nat.dist (10^2 * occurrences 10 2 48 127) 127 = 273 := by
  rw [occurrence_5_48]
  decide
theorem count_5_49 : Blocks.count [4, 9] word_5 = 2 := by decide
theorem actualCount_5_49 : Blocks.enumeratedCount [4, 9]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_49
theorem occurrence_5_49 : occurrences 10 2 49 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [4, 9])
    (by decide) (by decide) (by decide) digits_5 count_5_49
theorem discrepancy_5_49 :
    Nat.dist (10^2 * occurrences 10 2 49 127) 127 = 73 := by
  rw [occurrence_5_49]
  decide
theorem count_5_50 : Blocks.count [5, 0] word_5 = 0 := by decide
theorem actualCount_5_50 : Blocks.enumeratedCount [5, 0]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_50
theorem occurrence_5_50 : occurrences 10 2 50 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [5, 0])
    (by decide) (by decide) (by decide) digits_5 count_5_50
theorem discrepancy_5_50 :
    Nat.dist (10^2 * occurrences 10 2 50 127) 127 = 127 := by
  rw [occurrence_5_50]
  decide
theorem count_5_51 : Blocks.count [5, 1] word_5 = 0 := by decide
theorem actualCount_5_51 : Blocks.enumeratedCount [5, 1]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_51
theorem occurrence_5_51 : occurrences 10 2 51 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [5, 1])
    (by decide) (by decide) (by decide) digits_5 count_5_51
theorem discrepancy_5_51 :
    Nat.dist (10^2 * occurrences 10 2 51 127) 127 = 127 := by
  rw [occurrence_5_51]
  decide
theorem count_5_52 : Blocks.count [5, 2] word_5 = 2 := by decide
theorem actualCount_5_52 : Blocks.enumeratedCount [5, 2]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_52
theorem occurrence_5_52 : occurrences 10 2 52 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [5, 2])
    (by decide) (by decide) (by decide) digits_5 count_5_52
theorem discrepancy_5_52 :
    Nat.dist (10^2 * occurrences 10 2 52 127) 127 = 73 := by
  rw [occurrence_5_52]
  decide
theorem count_5_53 : Blocks.count [5, 3] word_5 = 1 := by decide
theorem actualCount_5_53 : Blocks.enumeratedCount [5, 3]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_53
theorem occurrence_5_53 : occurrences 10 2 53 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [5, 3])
    (by decide) (by decide) (by decide) digits_5 count_5_53
theorem discrepancy_5_53 :
    Nat.dist (10^2 * occurrences 10 2 53 127) 127 = 27 := by
  rw [occurrence_5_53]
  decide
theorem count_5_54 : Blocks.count [5, 4] word_5 = 2 := by decide
theorem actualCount_5_54 : Blocks.enumeratedCount [5, 4]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_54
theorem occurrence_5_54 : occurrences 10 2 54 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [5, 4])
    (by decide) (by decide) (by decide) digits_5 count_5_54
theorem discrepancy_5_54 :
    Nat.dist (10^2 * occurrences 10 2 54 127) 127 = 73 := by
  rw [occurrence_5_54]
  decide
theorem count_5_55 : Blocks.count [5, 5] word_5 = 0 := by decide
theorem actualCount_5_55 : Blocks.enumeratedCount [5, 5]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_55
theorem occurrence_5_55 : occurrences 10 2 55 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [5, 5])
    (by decide) (by decide) (by decide) digits_5 count_5_55
theorem discrepancy_5_55 :
    Nat.dist (10^2 * occurrences 10 2 55 127) 127 = 127 := by
  rw [occurrence_5_55]
  decide
theorem count_5_56 : Blocks.count [5, 6] word_5 = 1 := by decide
theorem actualCount_5_56 : Blocks.enumeratedCount [5, 6]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_56
theorem occurrence_5_56 : occurrences 10 2 56 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [5, 6])
    (by decide) (by decide) (by decide) digits_5 count_5_56
theorem discrepancy_5_56 :
    Nat.dist (10^2 * occurrences 10 2 56 127) 127 = 27 := by
  rw [occurrence_5_56]
  decide
theorem count_5_57 : Blocks.count [5, 7] word_5 = 1 := by decide
theorem actualCount_5_57 : Blocks.enumeratedCount [5, 7]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_57
theorem occurrence_5_57 : occurrences 10 2 57 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [5, 7])
    (by decide) (by decide) (by decide) digits_5 count_5_57
theorem discrepancy_5_57 :
    Nat.dist (10^2 * occurrences 10 2 57 127) 127 = 27 := by
  rw [occurrence_5_57]
  decide
theorem count_5_58 : Blocks.count [5, 8] word_5 = 1 := by decide
theorem actualCount_5_58 : Blocks.enumeratedCount [5, 8]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_58
theorem occurrence_5_58 : occurrences 10 2 58 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [5, 8])
    (by decide) (by decide) (by decide) digits_5 count_5_58
theorem discrepancy_5_58 :
    Nat.dist (10^2 * occurrences 10 2 58 127) 127 = 27 := by
  rw [occurrence_5_58]
  decide
theorem count_5_59 : Blocks.count [5, 9] word_5 = 0 := by decide
theorem actualCount_5_59 : Blocks.enumeratedCount [5, 9]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_59
theorem occurrence_5_59 : occurrences 10 2 59 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [5, 9])
    (by decide) (by decide) (by decide) digits_5 count_5_59
theorem discrepancy_5_59 :
    Nat.dist (10^2 * occurrences 10 2 59 127) 127 = 127 := by
  rw [occurrence_5_59]
  decide
theorem count_5_60 : Blocks.count [6, 0] word_5 = 1 := by decide
theorem actualCount_5_60 : Blocks.enumeratedCount [6, 0]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_60
theorem occurrence_5_60 : occurrences 10 2 60 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [6, 0])
    (by decide) (by decide) (by decide) digits_5 count_5_60
theorem discrepancy_5_60 :
    Nat.dist (10^2 * occurrences 10 2 60 127) 127 = 27 := by
  rw [occurrence_5_60]
  decide
theorem count_5_61 : Blocks.count [6, 1] word_5 = 1 := by decide
theorem actualCount_5_61 : Blocks.enumeratedCount [6, 1]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_61
theorem occurrence_5_61 : occurrences 10 2 61 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [6, 1])
    (by decide) (by decide) (by decide) digits_5 count_5_61
theorem discrepancy_5_61 :
    Nat.dist (10^2 * occurrences 10 2 61 127) 127 = 27 := by
  rw [occurrence_5_61]
  decide
theorem count_5_62 : Blocks.count [6, 2] word_5 = 4 := by decide
theorem actualCount_5_62 : Blocks.enumeratedCount [6, 2]
    (actualDigits 10 0 word_5.length) = 4 :=
  certified_count_sound digits_5 count_5_62
theorem occurrence_5_62 : occurrences 10 2 62 127 = 4 :=
  certified_occurrences_sound (b := 10) (value := 4)
    (text := word_5) (pattern := [6, 2])
    (by decide) (by decide) (by decide) digits_5 count_5_62
theorem discrepancy_5_62 :
    Nat.dist (10^2 * occurrences 10 2 62 127) 127 = 273 := by
  rw [occurrence_5_62]
  decide
theorem count_5_63 : Blocks.count [6, 3] word_5 = 2 := by decide
theorem actualCount_5_63 : Blocks.enumeratedCount [6, 3]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_63
theorem occurrence_5_63 : occurrences 10 2 63 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [6, 3])
    (by decide) (by decide) (by decide) digits_5 count_5_63
theorem discrepancy_5_63 :
    Nat.dist (10^2 * occurrences 10 2 63 127) 127 = 73 := by
  rw [occurrence_5_63]
  decide
theorem count_5_64 : Blocks.count [6, 4] word_5 = 0 := by decide
theorem actualCount_5_64 : Blocks.enumeratedCount [6, 4]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_64
theorem occurrence_5_64 : occurrences 10 2 64 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [6, 4])
    (by decide) (by decide) (by decide) digits_5 count_5_64
theorem discrepancy_5_64 :
    Nat.dist (10^2 * occurrences 10 2 64 127) 127 = 127 := by
  rw [occurrence_5_64]
  decide
theorem count_5_65 : Blocks.count [6, 5] word_5 = 1 := by decide
theorem actualCount_5_65 : Blocks.enumeratedCount [6, 5]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_65
theorem occurrence_5_65 : occurrences 10 2 65 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [6, 5])
    (by decide) (by decide) (by decide) digits_5 count_5_65
theorem discrepancy_5_65 :
    Nat.dist (10^2 * occurrences 10 2 65 127) 127 = 27 := by
  rw [occurrence_5_65]
  decide
theorem count_5_66 : Blocks.count [6, 6] word_5 = 1 := by decide
theorem actualCount_5_66 : Blocks.enumeratedCount [6, 6]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_66
theorem occurrence_5_66 : occurrences 10 2 66 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [6, 6])
    (by decide) (by decide) (by decide) digits_5 count_5_66
theorem discrepancy_5_66 :
    Nat.dist (10^2 * occurrences 10 2 66 127) 127 = 27 := by
  rw [occurrence_5_66]
  decide
theorem count_5_67 : Blocks.count [6, 7] word_5 = 0 := by decide
theorem actualCount_5_67 : Blocks.enumeratedCount [6, 7]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_67
theorem occurrence_5_67 : occurrences 10 2 67 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [6, 7])
    (by decide) (by decide) (by decide) digits_5 count_5_67
theorem discrepancy_5_67 :
    Nat.dist (10^2 * occurrences 10 2 67 127) 127 = 127 := by
  rw [occurrence_5_67]
  decide
theorem count_5_68 : Blocks.count [6, 8] word_5 = 2 := by decide
theorem actualCount_5_68 : Blocks.enumeratedCount [6, 8]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_68
theorem occurrence_5_68 : occurrences 10 2 68 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [6, 8])
    (by decide) (by decide) (by decide) digits_5 count_5_68
theorem discrepancy_5_68 :
    Nat.dist (10^2 * occurrences 10 2 68 127) 127 = 73 := by
  rw [occurrence_5_68]
  decide
theorem count_5_69 : Blocks.count [6, 9] word_5 = 0 := by decide
theorem actualCount_5_69 : Blocks.enumeratedCount [6, 9]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_69
theorem occurrence_5_69 : occurrences 10 2 69 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [6, 9])
    (by decide) (by decide) (by decide) digits_5 count_5_69
theorem discrepancy_5_69 :
    Nat.dist (10^2 * occurrences 10 2 69 127) 127 = 127 := by
  rw [occurrence_5_69]
  decide
theorem count_5_70 : Blocks.count [7, 0] word_5 = 2 := by decide
theorem actualCount_5_70 : Blocks.enumeratedCount [7, 0]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_70
theorem occurrence_5_70 : occurrences 10 2 70 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [7, 0])
    (by decide) (by decide) (by decide) digits_5 count_5_70
theorem discrepancy_5_70 :
    Nat.dist (10^2 * occurrences 10 2 70 127) 127 = 73 := by
  rw [occurrence_5_70]
  decide
theorem count_5_71 : Blocks.count [7, 1] word_5 = 0 := by decide
theorem actualCount_5_71 : Blocks.enumeratedCount [7, 1]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_71
theorem occurrence_5_71 : occurrences 10 2 71 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [7, 1])
    (by decide) (by decide) (by decide) digits_5 count_5_71
theorem discrepancy_5_71 :
    Nat.dist (10^2 * occurrences 10 2 71 127) 127 = 127 := by
  rw [occurrence_5_71]
  decide
theorem count_5_72 : Blocks.count [7, 2] word_5 = 3 := by decide
theorem actualCount_5_72 : Blocks.enumeratedCount [7, 2]
    (actualDigits 10 0 word_5.length) = 3 :=
  certified_count_sound digits_5 count_5_72
theorem occurrence_5_72 : occurrences 10 2 72 127 = 3 :=
  certified_occurrences_sound (b := 10) (value := 3)
    (text := word_5) (pattern := [7, 2])
    (by decide) (by decide) (by decide) digits_5 count_5_72
theorem discrepancy_5_72 :
    Nat.dist (10^2 * occurrences 10 2 72 127) 127 = 173 := by
  rw [occurrence_5_72]
  decide
theorem count_5_73 : Blocks.count [7, 3] word_5 = 0 := by decide
theorem actualCount_5_73 : Blocks.enumeratedCount [7, 3]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_73
theorem occurrence_5_73 : occurrences 10 2 73 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [7, 3])
    (by decide) (by decide) (by decide) digits_5 count_5_73
theorem discrepancy_5_73 :
    Nat.dist (10^2 * occurrences 10 2 73 127) 127 = 127 := by
  rw [occurrence_5_73]
  decide
theorem count_5_74 : Blocks.count [7, 4] word_5 = 2 := by decide
theorem actualCount_5_74 : Blocks.enumeratedCount [7, 4]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_74
theorem occurrence_5_74 : occurrences 10 2 74 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [7, 4])
    (by decide) (by decide) (by decide) digits_5 count_5_74
theorem discrepancy_5_74 :
    Nat.dist (10^2 * occurrences 10 2 74 127) 127 = 73 := by
  rw [occurrence_5_74]
  decide
theorem count_5_75 : Blocks.count [7, 5] word_5 = 3 := by decide
theorem actualCount_5_75 : Blocks.enumeratedCount [7, 5]
    (actualDigits 10 0 word_5.length) = 3 :=
  certified_count_sound digits_5 count_5_75
theorem occurrence_5_75 : occurrences 10 2 75 127 = 3 :=
  certified_occurrences_sound (b := 10) (value := 3)
    (text := word_5) (pattern := [7, 5])
    (by decide) (by decide) (by decide) digits_5 count_5_75
theorem discrepancy_5_75 :
    Nat.dist (10^2 * occurrences 10 2 75 127) 127 = 173 := by
  rw [occurrence_5_75]
  decide
theorem count_5_76 : Blocks.count [7, 6] word_5 = 1 := by decide
theorem actualCount_5_76 : Blocks.enumeratedCount [7, 6]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_76
theorem occurrence_5_76 : occurrences 10 2 76 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [7, 6])
    (by decide) (by decide) (by decide) digits_5 count_5_76
theorem discrepancy_5_76 :
    Nat.dist (10^2 * occurrences 10 2 76 127) 127 = 27 := by
  rw [occurrence_5_76]
  decide
theorem count_5_77 : Blocks.count [7, 7] word_5 = 1 := by decide
theorem actualCount_5_77 : Blocks.enumeratedCount [7, 7]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_77
theorem occurrence_5_77 : occurrences 10 2 77 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [7, 7])
    (by decide) (by decide) (by decide) digits_5 count_5_77
theorem discrepancy_5_77 :
    Nat.dist (10^2 * occurrences 10 2 77 127) 127 = 27 := by
  rw [occurrence_5_77]
  decide
theorem count_5_78 : Blocks.count [7, 8] word_5 = 0 := by decide
theorem actualCount_5_78 : Blocks.enumeratedCount [7, 8]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_78
theorem occurrence_5_78 : occurrences 10 2 78 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [7, 8])
    (by decide) (by decide) (by decide) digits_5 count_5_78
theorem discrepancy_5_78 :
    Nat.dist (10^2 * occurrences 10 2 78 127) 127 = 127 := by
  rw [occurrence_5_78]
  decide
theorem count_5_79 : Blocks.count [7, 9] word_5 = 1 := by decide
theorem actualCount_5_79 : Blocks.enumeratedCount [7, 9]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_79
theorem occurrence_5_79 : occurrences 10 2 79 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [7, 9])
    (by decide) (by decide) (by decide) digits_5 count_5_79
theorem discrepancy_5_79 :
    Nat.dist (10^2 * occurrences 10 2 79 127) 127 = 27 := by
  rw [occurrence_5_79]
  decide
theorem count_5_80 : Blocks.count [8, 0] word_5 = 3 := by decide
theorem actualCount_5_80 : Blocks.enumeratedCount [8, 0]
    (actualDigits 10 0 word_5.length) = 3 :=
  certified_count_sound digits_5 count_5_80
theorem occurrence_5_80 : occurrences 10 2 80 127 = 3 :=
  certified_occurrences_sound (b := 10) (value := 3)
    (text := word_5) (pattern := [8, 0])
    (by decide) (by decide) (by decide) digits_5 count_5_80
theorem discrepancy_5_80 :
    Nat.dist (10^2 * occurrences 10 2 80 127) 127 = 173 := by
  rw [occurrence_5_80]
  decide
theorem count_5_81 : Blocks.count [8, 1] word_5 = 2 := by decide
theorem actualCount_5_81 : Blocks.enumeratedCount [8, 1]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_81
theorem occurrence_5_81 : occurrences 10 2 81 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [8, 1])
    (by decide) (by decide) (by decide) digits_5 count_5_81
theorem discrepancy_5_81 :
    Nat.dist (10^2 * occurrences 10 2 81 127) 127 = 73 := by
  rw [occurrence_5_81]
  decide
theorem count_5_82 : Blocks.count [8, 2] word_5 = 1 := by decide
theorem actualCount_5_82 : Blocks.enumeratedCount [8, 2]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_82
theorem occurrence_5_82 : occurrences 10 2 82 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [8, 2])
    (by decide) (by decide) (by decide) digits_5 count_5_82
theorem discrepancy_5_82 :
    Nat.dist (10^2 * occurrences 10 2 82 127) 127 = 27 := by
  rw [occurrence_5_82]
  decide
theorem count_5_83 : Blocks.count [8, 3] word_5 = 1 := by decide
theorem actualCount_5_83 : Blocks.enumeratedCount [8, 3]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_83
theorem occurrence_5_83 : occurrences 10 2 83 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [8, 3])
    (by decide) (by decide) (by decide) digits_5 count_5_83
theorem discrepancy_5_83 :
    Nat.dist (10^2 * occurrences 10 2 83 127) 127 = 27 := by
  rw [occurrence_5_83]
  decide
theorem count_5_84 : Blocks.count [8, 4] word_5 = 2 := by decide
theorem actualCount_5_84 : Blocks.enumeratedCount [8, 4]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_84
theorem occurrence_5_84 : occurrences 10 2 84 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [8, 4])
    (by decide) (by decide) (by decide) digits_5 count_5_84
theorem discrepancy_5_84 :
    Nat.dist (10^2 * occurrences 10 2 84 127) 127 = 73 := by
  rw [occurrence_5_84]
  decide
theorem count_5_85 : Blocks.count [8, 5] word_5 = 0 := by decide
theorem actualCount_5_85 : Blocks.enumeratedCount [8, 5]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_85
theorem occurrence_5_85 : occurrences 10 2 85 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [8, 5])
    (by decide) (by decide) (by decide) digits_5 count_5_85
theorem discrepancy_5_85 :
    Nat.dist (10^2 * occurrences 10 2 85 127) 127 = 127 := by
  rw [occurrence_5_85]
  decide
theorem count_5_86 : Blocks.count [8, 6] word_5 = 5 := by decide
theorem actualCount_5_86 : Blocks.enumeratedCount [8, 6]
    (actualDigits 10 0 word_5.length) = 5 :=
  certified_count_sound digits_5 count_5_86
theorem occurrence_5_86 : occurrences 10 2 86 127 = 5 :=
  certified_occurrences_sound (b := 10) (value := 5)
    (text := word_5) (pattern := [8, 6])
    (by decide) (by decide) (by decide) digits_5 count_5_86
theorem discrepancy_5_86 :
    Nat.dist (10^2 * occurrences 10 2 86 127) 127 = 373 := by
  rw [occurrence_5_86]
  decide
theorem count_5_87 : Blocks.count [8, 7] word_5 = 1 := by decide
theorem actualCount_5_87 : Blocks.enumeratedCount [8, 7]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_87
theorem occurrence_5_87 : occurrences 10 2 87 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [8, 7])
    (by decide) (by decide) (by decide) digits_5 count_5_87
theorem discrepancy_5_87 :
    Nat.dist (10^2 * occurrences 10 2 87 127) 127 = 27 := by
  rw [occurrence_5_87]
  decide
theorem count_5_88 : Blocks.count [8, 8] word_5 = 2 := by decide
theorem actualCount_5_88 : Blocks.enumeratedCount [8, 8]
    (actualDigits 10 0 word_5.length) = 2 :=
  certified_count_sound digits_5 count_5_88
theorem occurrence_5_88 : occurrences 10 2 88 127 = 2 :=
  certified_occurrences_sound (b := 10) (value := 2)
    (text := word_5) (pattern := [8, 8])
    (by decide) (by decide) (by decide) digits_5 count_5_88
theorem discrepancy_5_88 :
    Nat.dist (10^2 * occurrences 10 2 88 127) 127 = 73 := by
  rw [occurrence_5_88]
  decide
theorem count_5_89 : Blocks.count [8, 9] word_5 = 4 := by decide
theorem actualCount_5_89 : Blocks.enumeratedCount [8, 9]
    (actualDigits 10 0 word_5.length) = 4 :=
  certified_count_sound digits_5 count_5_89
theorem occurrence_5_89 : occurrences 10 2 89 127 = 4 :=
  certified_occurrences_sound (b := 10) (value := 4)
    (text := word_5) (pattern := [8, 9])
    (by decide) (by decide) (by decide) digits_5 count_5_89
theorem discrepancy_5_89 :
    Nat.dist (10^2 * occurrences 10 2 89 127) 127 = 273 := by
  rw [occurrence_5_89]
  decide
theorem count_5_90 : Blocks.count [9, 0] word_5 = 1 := by decide
theorem actualCount_5_90 : Blocks.enumeratedCount [9, 0]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_90
theorem occurrence_5_90 : occurrences 10 2 90 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [9, 0])
    (by decide) (by decide) (by decide) digits_5 count_5_90
theorem discrepancy_5_90 :
    Nat.dist (10^2 * occurrences 10 2 90 127) 127 = 27 := by
  rw [occurrence_5_90]
  decide
theorem count_5_91 : Blocks.count [9, 1] word_5 = 3 := by decide
theorem actualCount_5_91 : Blocks.enumeratedCount [9, 1]
    (actualDigits 10 0 word_5.length) = 3 :=
  certified_count_sound digits_5 count_5_91
theorem occurrence_5_91 : occurrences 10 2 91 127 = 3 :=
  certified_occurrences_sound (b := 10) (value := 3)
    (text := word_5) (pattern := [9, 1])
    (by decide) (by decide) (by decide) digits_5 count_5_91
theorem discrepancy_5_91 :
    Nat.dist (10^2 * occurrences 10 2 91 127) 127 = 173 := by
  rw [occurrence_5_91]
  decide
theorem count_5_92 : Blocks.count [9, 2] word_5 = 0 := by decide
theorem actualCount_5_92 : Blocks.enumeratedCount [9, 2]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_92
theorem occurrence_5_92 : occurrences 10 2 92 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [9, 2])
    (by decide) (by decide) (by decide) digits_5 count_5_92
theorem discrepancy_5_92 :
    Nat.dist (10^2 * occurrences 10 2 92 127) 127 = 127 := by
  rw [occurrence_5_92]
  decide
theorem count_5_93 : Blocks.count [9, 3] word_5 = 1 := by decide
theorem actualCount_5_93 : Blocks.enumeratedCount [9, 3]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_93
theorem occurrence_5_93 : occurrences 10 2 93 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [9, 3])
    (by decide) (by decide) (by decide) digits_5 count_5_93
theorem discrepancy_5_93 :
    Nat.dist (10^2 * occurrences 10 2 93 127) 127 = 27 := by
  rw [occurrence_5_93]
  decide
theorem count_5_94 : Blocks.count [9, 4] word_5 = 1 := by decide
theorem actualCount_5_94 : Blocks.enumeratedCount [9, 4]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_94
theorem occurrence_5_94 : occurrences 10 2 94 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [9, 4])
    (by decide) (by decide) (by decide) digits_5 count_5_94
theorem discrepancy_5_94 :
    Nat.dist (10^2 * occurrences 10 2 94 127) 127 = 27 := by
  rw [occurrence_5_94]
  decide
theorem count_5_95 : Blocks.count [9, 5] word_5 = 0 := by decide
theorem actualCount_5_95 : Blocks.enumeratedCount [9, 5]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_95
theorem occurrence_5_95 : occurrences 10 2 95 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [9, 5])
    (by decide) (by decide) (by decide) digits_5 count_5_95
theorem discrepancy_5_95 :
    Nat.dist (10^2 * occurrences 10 2 95 127) 127 = 127 := by
  rw [occurrence_5_95]
  decide
theorem count_5_96 : Blocks.count [9, 6] word_5 = 0 := by decide
theorem actualCount_5_96 : Blocks.enumeratedCount [9, 6]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_96
theorem occurrence_5_96 : occurrences 10 2 96 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [9, 6])
    (by decide) (by decide) (by decide) digits_5 count_5_96
theorem discrepancy_5_96 :
    Nat.dist (10^2 * occurrences 10 2 96 127) 127 = 127 := by
  rw [occurrence_5_96]
  decide
theorem count_5_97 : Blocks.count [9, 7] word_5 = 1 := by decide
theorem actualCount_5_97 : Blocks.enumeratedCount [9, 7]
    (actualDigits 10 0 word_5.length) = 1 :=
  certified_count_sound digits_5 count_5_97
theorem occurrence_5_97 : occurrences 10 2 97 127 = 1 :=
  certified_occurrences_sound (b := 10) (value := 1)
    (text := word_5) (pattern := [9, 7])
    (by decide) (by decide) (by decide) digits_5 count_5_97
theorem discrepancy_5_97 :
    Nat.dist (10^2 * occurrences 10 2 97 127) 127 = 27 := by
  rw [occurrence_5_97]
  decide
theorem count_5_98 : Blocks.count [9, 8] word_5 = 3 := by decide
theorem actualCount_5_98 : Blocks.enumeratedCount [9, 8]
    (actualDigits 10 0 word_5.length) = 3 :=
  certified_count_sound digits_5 count_5_98
theorem occurrence_5_98 : occurrences 10 2 98 127 = 3 :=
  certified_occurrences_sound (b := 10) (value := 3)
    (text := word_5) (pattern := [9, 8])
    (by decide) (by decide) (by decide) digits_5 count_5_98
theorem discrepancy_5_98 :
    Nat.dist (10^2 * occurrences 10 2 98 127) 127 = 173 := by
  rw [occurrence_5_98]
  decide
theorem count_5_99 : Blocks.count [9, 9] word_5 = 0 := by decide
theorem actualCount_5_99 : Blocks.enumeratedCount [9, 9]
    (actualDigits 10 0 word_5.length) = 0 :=
  certified_count_sound digits_5 count_5_99
theorem occurrence_5_99 : occurrences 10 2 99 127 = 0 :=
  certified_occurrences_sound (b := 10) (value := 0)
    (text := word_5) (pattern := [9, 9])
    (by decide) (by decide) (by decide) digits_5 count_5_99
theorem discrepancy_5_99 :
    Nat.dist (10^2 * occurrences 10 2 99 127) 127 = 127 := by
  rw [occurrence_5_99]
  decide

def word_6 : List ℕ := []
theorem prefix_6_0 : PrefixCertificate (2^0) 0 := by decide
theorem digits_6 : DigitsAt 2 0 word_6 := True.intro
theorem count_6_0 : Blocks.count [0, 0, 0] word_6 = 0 := by decide
theorem actualCount_6_0 : Blocks.enumeratedCount [0, 0, 0]
    (actualDigits 2 0 word_6.length) = 0 :=
  certified_count_sound digits_6 count_6_0
theorem occurrence_6_0 : occurrences 2 3 0 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_6) (pattern := [0, 0, 0])
    (by decide) (by decide) (by decide) digits_6 count_6_0
theorem discrepancy_6_0 :
    Nat.dist (2^3 * occurrences 2 3 0 0) 0 = 0 := by
  rw [occurrence_6_0]
  decide
theorem count_6_1 : Blocks.count [0, 0, 1] word_6 = 0 := by decide
theorem actualCount_6_1 : Blocks.enumeratedCount [0, 0, 1]
    (actualDigits 2 0 word_6.length) = 0 :=
  certified_count_sound digits_6 count_6_1
theorem occurrence_6_1 : occurrences 2 3 1 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_6) (pattern := [0, 0, 1])
    (by decide) (by decide) (by decide) digits_6 count_6_1
theorem discrepancy_6_1 :
    Nat.dist (2^3 * occurrences 2 3 1 0) 0 = 0 := by
  rw [occurrence_6_1]
  decide
theorem count_6_2 : Blocks.count [0, 1, 0] word_6 = 0 := by decide
theorem actualCount_6_2 : Blocks.enumeratedCount [0, 1, 0]
    (actualDigits 2 0 word_6.length) = 0 :=
  certified_count_sound digits_6 count_6_2
theorem occurrence_6_2 : occurrences 2 3 2 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_6) (pattern := [0, 1, 0])
    (by decide) (by decide) (by decide) digits_6 count_6_2
theorem discrepancy_6_2 :
    Nat.dist (2^3 * occurrences 2 3 2 0) 0 = 0 := by
  rw [occurrence_6_2]
  decide
theorem count_6_3 : Blocks.count [0, 1, 1] word_6 = 0 := by decide
theorem actualCount_6_3 : Blocks.enumeratedCount [0, 1, 1]
    (actualDigits 2 0 word_6.length) = 0 :=
  certified_count_sound digits_6 count_6_3
theorem occurrence_6_3 : occurrences 2 3 3 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_6) (pattern := [0, 1, 1])
    (by decide) (by decide) (by decide) digits_6 count_6_3
theorem discrepancy_6_3 :
    Nat.dist (2^3 * occurrences 2 3 3 0) 0 = 0 := by
  rw [occurrence_6_3]
  decide
theorem count_6_4 : Blocks.count [1, 0, 0] word_6 = 0 := by decide
theorem actualCount_6_4 : Blocks.enumeratedCount [1, 0, 0]
    (actualDigits 2 0 word_6.length) = 0 :=
  certified_count_sound digits_6 count_6_4
theorem occurrence_6_4 : occurrences 2 3 4 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_6) (pattern := [1, 0, 0])
    (by decide) (by decide) (by decide) digits_6 count_6_4
theorem discrepancy_6_4 :
    Nat.dist (2^3 * occurrences 2 3 4 0) 0 = 0 := by
  rw [occurrence_6_4]
  decide
theorem count_6_5 : Blocks.count [1, 0, 1] word_6 = 0 := by decide
theorem actualCount_6_5 : Blocks.enumeratedCount [1, 0, 1]
    (actualDigits 2 0 word_6.length) = 0 :=
  certified_count_sound digits_6 count_6_5
theorem occurrence_6_5 : occurrences 2 3 5 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_6) (pattern := [1, 0, 1])
    (by decide) (by decide) (by decide) digits_6 count_6_5
theorem discrepancy_6_5 :
    Nat.dist (2^3 * occurrences 2 3 5 0) 0 = 0 := by
  rw [occurrence_6_5]
  decide
theorem count_6_6 : Blocks.count [1, 1, 0] word_6 = 0 := by decide
theorem actualCount_6_6 : Blocks.enumeratedCount [1, 1, 0]
    (actualDigits 2 0 word_6.length) = 0 :=
  certified_count_sound digits_6 count_6_6
theorem occurrence_6_6 : occurrences 2 3 6 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_6) (pattern := [1, 1, 0])
    (by decide) (by decide) (by decide) digits_6 count_6_6
theorem discrepancy_6_6 :
    Nat.dist (2^3 * occurrences 2 3 6 0) 0 = 0 := by
  rw [occurrence_6_6]
  decide
theorem count_6_7 : Blocks.count [1, 1, 1] word_6 = 0 := by decide
theorem actualCount_6_7 : Blocks.enumeratedCount [1, 1, 1]
    (actualDigits 2 0 word_6.length) = 0 :=
  certified_count_sound digits_6 count_6_7
theorem occurrence_6_7 : occurrences 2 3 7 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_6) (pattern := [1, 1, 1])
    (by decide) (by decide) (by decide) digits_6 count_6_7
theorem discrepancy_6_7 :
    Nat.dist (2^3 * occurrences 2 3 7 0) 0 = 0 := by
  rw [occurrence_6_7]
  decide

def word_7 : List ℕ := [1]
theorem prefix_7_0 : PrefixCertificate (2^0) 0 := by decide
theorem prefix_7_1 : PrefixCertificate (2^1) 1 := by decide
theorem digit_7_0 : digit 2 0 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_7_0 prefix_7_1
theorem digits_7 : DigitsAt 2 0 word_7 := And.intro digit_7_0 (True.intro)
theorem count_7_0 : Blocks.count [0, 0, 0] word_7 = 0 := by decide
theorem actualCount_7_0 : Blocks.enumeratedCount [0, 0, 0]
    (actualDigits 2 0 word_7.length) = 0 :=
  certified_count_sound digits_7 count_7_0
theorem occurrence_7_0 : occurrences 2 3 0 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_7) (pattern := [0, 0, 0])
    (by decide) (by decide) (by decide) digits_7 count_7_0
theorem discrepancy_7_0 :
    Nat.dist (2^3 * occurrences 2 3 0 0) 0 = 0 := by
  rw [occurrence_7_0]
  decide
theorem count_7_1 : Blocks.count [0, 0, 1] word_7 = 0 := by decide
theorem actualCount_7_1 : Blocks.enumeratedCount [0, 0, 1]
    (actualDigits 2 0 word_7.length) = 0 :=
  certified_count_sound digits_7 count_7_1
theorem occurrence_7_1 : occurrences 2 3 1 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_7) (pattern := [0, 0, 1])
    (by decide) (by decide) (by decide) digits_7 count_7_1
theorem discrepancy_7_1 :
    Nat.dist (2^3 * occurrences 2 3 1 0) 0 = 0 := by
  rw [occurrence_7_1]
  decide
theorem count_7_2 : Blocks.count [0, 1, 0] word_7 = 0 := by decide
theorem actualCount_7_2 : Blocks.enumeratedCount [0, 1, 0]
    (actualDigits 2 0 word_7.length) = 0 :=
  certified_count_sound digits_7 count_7_2
theorem occurrence_7_2 : occurrences 2 3 2 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_7) (pattern := [0, 1, 0])
    (by decide) (by decide) (by decide) digits_7 count_7_2
theorem discrepancy_7_2 :
    Nat.dist (2^3 * occurrences 2 3 2 0) 0 = 0 := by
  rw [occurrence_7_2]
  decide
theorem count_7_3 : Blocks.count [0, 1, 1] word_7 = 0 := by decide
theorem actualCount_7_3 : Blocks.enumeratedCount [0, 1, 1]
    (actualDigits 2 0 word_7.length) = 0 :=
  certified_count_sound digits_7 count_7_3
theorem occurrence_7_3 : occurrences 2 3 3 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_7) (pattern := [0, 1, 1])
    (by decide) (by decide) (by decide) digits_7 count_7_3
theorem discrepancy_7_3 :
    Nat.dist (2^3 * occurrences 2 3 3 0) 0 = 0 := by
  rw [occurrence_7_3]
  decide
theorem count_7_4 : Blocks.count [1, 0, 0] word_7 = 0 := by decide
theorem actualCount_7_4 : Blocks.enumeratedCount [1, 0, 0]
    (actualDigits 2 0 word_7.length) = 0 :=
  certified_count_sound digits_7 count_7_4
theorem occurrence_7_4 : occurrences 2 3 4 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_7) (pattern := [1, 0, 0])
    (by decide) (by decide) (by decide) digits_7 count_7_4
theorem discrepancy_7_4 :
    Nat.dist (2^3 * occurrences 2 3 4 0) 0 = 0 := by
  rw [occurrence_7_4]
  decide
theorem count_7_5 : Blocks.count [1, 0, 1] word_7 = 0 := by decide
theorem actualCount_7_5 : Blocks.enumeratedCount [1, 0, 1]
    (actualDigits 2 0 word_7.length) = 0 :=
  certified_count_sound digits_7 count_7_5
theorem occurrence_7_5 : occurrences 2 3 5 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_7) (pattern := [1, 0, 1])
    (by decide) (by decide) (by decide) digits_7 count_7_5
theorem discrepancy_7_5 :
    Nat.dist (2^3 * occurrences 2 3 5 0) 0 = 0 := by
  rw [occurrence_7_5]
  decide
theorem count_7_6 : Blocks.count [1, 1, 0] word_7 = 0 := by decide
theorem actualCount_7_6 : Blocks.enumeratedCount [1, 1, 0]
    (actualDigits 2 0 word_7.length) = 0 :=
  certified_count_sound digits_7 count_7_6
theorem occurrence_7_6 : occurrences 2 3 6 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_7) (pattern := [1, 1, 0])
    (by decide) (by decide) (by decide) digits_7 count_7_6
theorem discrepancy_7_6 :
    Nat.dist (2^3 * occurrences 2 3 6 0) 0 = 0 := by
  rw [occurrence_7_6]
  decide
theorem count_7_7 : Blocks.count [1, 1, 1] word_7 = 0 := by decide
theorem actualCount_7_7 : Blocks.enumeratedCount [1, 1, 1]
    (actualDigits 2 0 word_7.length) = 0 :=
  certified_count_sound digits_7 count_7_7
theorem occurrence_7_7 : occurrences 2 3 7 0 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_7) (pattern := [1, 1, 1])
    (by decide) (by decide) (by decide) digits_7 count_7_7
theorem discrepancy_7_7 :
    Nat.dist (2^3 * occurrences 2 3 7 0) 0 = 0 := by
  rw [occurrence_7_7]
  decide

def word_8 : List ℕ := [1, 0, 0]
theorem prefix_8_0 : PrefixCertificate (2^0) 0 := by decide
theorem prefix_8_1 : PrefixCertificate (2^1) 1 := by decide
theorem prefix_8_2 : PrefixCertificate (2^2) 2 := by decide
theorem prefix_8_3 : PrefixCertificate (2^3) 4 := by decide
theorem digit_8_0 : digit 2 0 = (1 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_8_0 prefix_8_1
theorem digit_8_1 : digit 2 1 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_8_1 prefix_8_2
theorem digit_8_2 : digit 2 2 = (0 : ℤ) := by
  exact digit_of_certificates (by decide) prefix_8_2 prefix_8_3
theorem digits_8 : DigitsAt 2 0 word_8 := And.intro digit_8_0 (And.intro digit_8_1 (And.intro digit_8_2 (True.intro)))
theorem count_8_0 : Blocks.count [0, 0, 0] word_8 = 0 := by decide
theorem actualCount_8_0 : Blocks.enumeratedCount [0, 0, 0]
    (actualDigits 2 0 word_8.length) = 0 :=
  certified_count_sound digits_8 count_8_0
theorem occurrence_8_0 : occurrences 2 3 0 1 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_8) (pattern := [0, 0, 0])
    (by decide) (by decide) (by decide) digits_8 count_8_0
theorem discrepancy_8_0 :
    Nat.dist (2^3 * occurrences 2 3 0 1) 1 = 1 := by
  rw [occurrence_8_0]
  decide
theorem count_8_1 : Blocks.count [0, 0, 1] word_8 = 0 := by decide
theorem actualCount_8_1 : Blocks.enumeratedCount [0, 0, 1]
    (actualDigits 2 0 word_8.length) = 0 :=
  certified_count_sound digits_8 count_8_1
theorem occurrence_8_1 : occurrences 2 3 1 1 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_8) (pattern := [0, 0, 1])
    (by decide) (by decide) (by decide) digits_8 count_8_1
theorem discrepancy_8_1 :
    Nat.dist (2^3 * occurrences 2 3 1 1) 1 = 1 := by
  rw [occurrence_8_1]
  decide
theorem count_8_2 : Blocks.count [0, 1, 0] word_8 = 0 := by decide
theorem actualCount_8_2 : Blocks.enumeratedCount [0, 1, 0]
    (actualDigits 2 0 word_8.length) = 0 :=
  certified_count_sound digits_8 count_8_2
theorem occurrence_8_2 : occurrences 2 3 2 1 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_8) (pattern := [0, 1, 0])
    (by decide) (by decide) (by decide) digits_8 count_8_2
theorem discrepancy_8_2 :
    Nat.dist (2^3 * occurrences 2 3 2 1) 1 = 1 := by
  rw [occurrence_8_2]
  decide
theorem count_8_3 : Blocks.count [0, 1, 1] word_8 = 0 := by decide
theorem actualCount_8_3 : Blocks.enumeratedCount [0, 1, 1]
    (actualDigits 2 0 word_8.length) = 0 :=
  certified_count_sound digits_8 count_8_3
theorem occurrence_8_3 : occurrences 2 3 3 1 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_8) (pattern := [0, 1, 1])
    (by decide) (by decide) (by decide) digits_8 count_8_3
theorem discrepancy_8_3 :
    Nat.dist (2^3 * occurrences 2 3 3 1) 1 = 1 := by
  rw [occurrence_8_3]
  decide
theorem count_8_4 : Blocks.count [1, 0, 0] word_8 = 1 := by decide
theorem actualCount_8_4 : Blocks.enumeratedCount [1, 0, 0]
    (actualDigits 2 0 word_8.length) = 1 :=
  certified_count_sound digits_8 count_8_4
theorem occurrence_8_4 : occurrences 2 3 4 1 = 1 :=
  certified_occurrences_sound (b := 2) (value := 1)
    (text := word_8) (pattern := [1, 0, 0])
    (by decide) (by decide) (by decide) digits_8 count_8_4
theorem discrepancy_8_4 :
    Nat.dist (2^3 * occurrences 2 3 4 1) 1 = 7 := by
  rw [occurrence_8_4]
  decide
theorem count_8_5 : Blocks.count [1, 0, 1] word_8 = 0 := by decide
theorem actualCount_8_5 : Blocks.enumeratedCount [1, 0, 1]
    (actualDigits 2 0 word_8.length) = 0 :=
  certified_count_sound digits_8 count_8_5
theorem occurrence_8_5 : occurrences 2 3 5 1 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_8) (pattern := [1, 0, 1])
    (by decide) (by decide) (by decide) digits_8 count_8_5
theorem discrepancy_8_5 :
    Nat.dist (2^3 * occurrences 2 3 5 1) 1 = 1 := by
  rw [occurrence_8_5]
  decide
theorem count_8_6 : Blocks.count [1, 1, 0] word_8 = 0 := by decide
theorem actualCount_8_6 : Blocks.enumeratedCount [1, 1, 0]
    (actualDigits 2 0 word_8.length) = 0 :=
  certified_count_sound digits_8 count_8_6
theorem occurrence_8_6 : occurrences 2 3 6 1 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_8) (pattern := [1, 1, 0])
    (by decide) (by decide) (by decide) digits_8 count_8_6
theorem discrepancy_8_6 :
    Nat.dist (2^3 * occurrences 2 3 6 1) 1 = 1 := by
  rw [occurrence_8_6]
  decide
theorem count_8_7 : Blocks.count [1, 1, 1] word_8 = 0 := by decide
theorem actualCount_8_7 : Blocks.enumeratedCount [1, 1, 1]
    (actualDigits 2 0 word_8.length) = 0 :=
  certified_count_sound digits_8 count_8_7
theorem occurrence_8_7 : occurrences 2 3 7 1 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (text := word_8) (pattern := [1, 1, 1])
    (by decide) (by decide) (by decide) digits_8 count_8_7
theorem discrepancy_8_7 :
    Nat.dist (2^3 * occurrences 2 3 7 1) 1 = 1 := by
  rw [occurrence_8_7]
  decide

def fibonacciWord_0 : List Bool := [false]
theorem input_0 : BinaryAutomaton.fibonacciSum fibonacciWord_0 2 = 0 := by decide
theorem output_0 : BinaryAutomaton.classify fibonacciWord_0 = some 0 := by decide
theorem predicate_0 : BinaryAutomaton.binaryDifference 0 = (0 : ℤ) := by
  simpa only [input_0, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_0
def fibonacciWord_1 : List Bool := [true]
theorem input_1 : BinaryAutomaton.fibonacciSum fibonacciWord_1 2 = 1 := by decide
theorem output_1 : BinaryAutomaton.classify fibonacciWord_1 = some 1 := by decide
theorem predicate_1 : BinaryAutomaton.binaryDifference 1 = (1 : ℤ) := by
  simpa only [input_1, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_1
theorem powerDigit_0 : digit 2 0 = (1 : ℤ) :=
  BinaryAutomaton.power_input_digit input_1 output_1
def fibonacciWord_2 : List Bool := [true, false]
theorem input_2 : BinaryAutomaton.fibonacciSum fibonacciWord_2 2 = 2 := by decide
theorem output_2 : BinaryAutomaton.classify fibonacciWord_2 = some 0 := by decide
theorem predicate_2 : BinaryAutomaton.binaryDifference 2 = (0 : ℤ) := by
  simpa only [input_2, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_2
theorem powerDigit_1 : digit 2 1 = (0 : ℤ) :=
  BinaryAutomaton.power_input_digit input_2 output_2
def fibonacciWord_3 : List Bool := [true, false, false]
theorem input_3 : BinaryAutomaton.fibonacciSum fibonacciWord_3 2 = 3 := by decide
theorem output_3 : BinaryAutomaton.classify fibonacciWord_3 = some 1 := by decide
theorem predicate_3 : BinaryAutomaton.binaryDifference 3 = (1 : ℤ) := by
  simpa only [input_3, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_3
def fibonacciWord_4 : List Bool := [true, false, true]
theorem input_4 : BinaryAutomaton.fibonacciSum fibonacciWord_4 2 = 4 := by decide
theorem output_4 : BinaryAutomaton.classify fibonacciWord_4 = some 0 := by decide
theorem predicate_4 : BinaryAutomaton.binaryDifference 4 = (0 : ℤ) := by
  simpa only [input_4, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_4
theorem powerDigit_2 : digit 2 2 = (0 : ℤ) :=
  BinaryAutomaton.power_input_digit input_4 output_4
def fibonacciWord_5 : List Bool := [true, false, false, false]
theorem input_5 : BinaryAutomaton.fibonacciSum fibonacciWord_5 2 = 5 := by decide
theorem output_5 : BinaryAutomaton.classify fibonacciWord_5 = some 0 := by decide
theorem predicate_5 : BinaryAutomaton.binaryDifference 5 = (0 : ℤ) := by
  simpa only [input_5, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_5
def fibonacciWord_6 : List Bool := [true, false, false, true]
theorem input_6 : BinaryAutomaton.fibonacciSum fibonacciWord_6 2 = 6 := by decide
theorem output_6 : BinaryAutomaton.classify fibonacciWord_6 = some 1 := by decide
theorem predicate_6 : BinaryAutomaton.binaryDifference 6 = (1 : ℤ) := by
  simpa only [input_6, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_6
def fibonacciWord_7 : List Bool := [true, false, true, false]
theorem input_7 : BinaryAutomaton.fibonacciSum fibonacciWord_7 2 = 7 := by decide
theorem output_7 : BinaryAutomaton.classify fibonacciWord_7 = some 0 := by decide
theorem predicate_7 : BinaryAutomaton.binaryDifference 7 = (0 : ℤ) := by
  simpa only [input_7, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_7
def fibonacciWord_8 : List Bool := [true, false, false, false, false]
theorem input_8 : BinaryAutomaton.fibonacciSum fibonacciWord_8 2 = 8 := by decide
theorem output_8 : BinaryAutomaton.classify fibonacciWord_8 = some 1 := by decide
theorem predicate_8 : BinaryAutomaton.binaryDifference 8 = (1 : ℤ) := by
  simpa only [input_8, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_8
theorem powerDigit_3 : digit 2 3 = (1 : ℤ) :=
  BinaryAutomaton.power_input_digit input_8 output_8
def fibonacciWord_9 : List Bool := [true, false, false, false, true]
theorem input_9 : BinaryAutomaton.fibonacciSum fibonacciWord_9 2 = 9 := by decide
theorem output_9 : BinaryAutomaton.classify fibonacciWord_9 = some 1 := by decide
theorem predicate_9 : BinaryAutomaton.binaryDifference 9 = (1 : ℤ) := by
  simpa only [input_9, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_9
def fibonacciWord_10 : List Bool := [true, false, false, true, false]
theorem input_10 : BinaryAutomaton.fibonacciSum fibonacciWord_10 2 = 10 := by decide
theorem output_10 : BinaryAutomaton.classify fibonacciWord_10 = some 0 := by decide
theorem predicate_10 : BinaryAutomaton.binaryDifference 10 = (0 : ℤ) := by
  simpa only [input_10, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_10
def fibonacciWord_11 : List Bool := [true, false, true, false, false]
theorem input_11 : BinaryAutomaton.fibonacciSum fibonacciWord_11 2 = 11 := by decide
theorem output_11 : BinaryAutomaton.classify fibonacciWord_11 = some 1 := by decide
theorem predicate_11 : BinaryAutomaton.binaryDifference 11 = (1 : ℤ) := by
  simpa only [input_11, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_11
def fibonacciWord_12 : List Bool := [true, false, true, false, true]
theorem input_12 : BinaryAutomaton.fibonacciSum fibonacciWord_12 2 = 12 := by decide
theorem output_12 : BinaryAutomaton.classify fibonacciWord_12 = some 0 := by decide
theorem predicate_12 : BinaryAutomaton.binaryDifference 12 = (0 : ℤ) := by
  simpa only [input_12, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_12
def fibonacciWord_13 : List Bool := [true, false, false, false, false, false]
theorem input_13 : BinaryAutomaton.fibonacciSum fibonacciWord_13 2 = 13 := by decide
theorem output_13 : BinaryAutomaton.classify fibonacciWord_13 = some 0 := by decide
theorem predicate_13 : BinaryAutomaton.binaryDifference 13 = (0 : ℤ) := by
  simpa only [input_13, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_13
def fibonacciWord_14 : List Bool := [true, false, false, false, false, true]
theorem input_14 : BinaryAutomaton.fibonacciSum fibonacciWord_14 2 = 14 := by decide
theorem output_14 : BinaryAutomaton.classify fibonacciWord_14 = some 1 := by decide
theorem predicate_14 : BinaryAutomaton.binaryDifference 14 = (1 : ℤ) := by
  simpa only [input_14, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_14
def fibonacciWord_15 : List Bool := [true, false, false, false, true, false]
theorem input_15 : BinaryAutomaton.fibonacciSum fibonacciWord_15 2 = 15 := by decide
theorem output_15 : BinaryAutomaton.classify fibonacciWord_15 = some 0 := by decide
theorem predicate_15 : BinaryAutomaton.binaryDifference 15 = (0 : ℤ) := by
  simpa only [input_15, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_15
def fibonacciWord_16 : List Bool := [true, false, false, true, false, false]
theorem input_16 : BinaryAutomaton.fibonacciSum fibonacciWord_16 2 = 16 := by decide
theorem output_16 : BinaryAutomaton.classify fibonacciWord_16 = some 1 := by decide
theorem predicate_16 : BinaryAutomaton.binaryDifference 16 = (1 : ℤ) := by
  simpa only [input_16, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_16
theorem powerDigit_4 : digit 2 4 = (1 : ℤ) :=
  BinaryAutomaton.power_input_digit input_16 output_16
def fibonacciWord_17 : List Bool := [true, false, false, true, false, true]
theorem input_17 : BinaryAutomaton.fibonacciSum fibonacciWord_17 2 = 17 := by decide
theorem output_17 : BinaryAutomaton.classify fibonacciWord_17 = some 1 := by decide
theorem predicate_17 : BinaryAutomaton.binaryDifference 17 = (1 : ℤ) := by
  simpa only [input_17, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_17
def fibonacciWord_18 : List Bool := [true, false, true, false, false, false]
theorem input_18 : BinaryAutomaton.fibonacciSum fibonacciWord_18 2 = 18 := by decide
theorem output_18 : BinaryAutomaton.classify fibonacciWord_18 = some 0 := by decide
theorem predicate_18 : BinaryAutomaton.binaryDifference 18 = (0 : ℤ) := by
  simpa only [input_18, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_18
def fibonacciWord_19 : List Bool := [true, false, true, false, false, true]
theorem input_19 : BinaryAutomaton.fibonacciSum fibonacciWord_19 2 = 19 := by decide
theorem output_19 : BinaryAutomaton.classify fibonacciWord_19 = some 1 := by decide
theorem predicate_19 : BinaryAutomaton.binaryDifference 19 = (1 : ℤ) := by
  simpa only [input_19, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_19
def fibonacciWord_20 : List Bool := [true, false, true, false, true, false]
theorem input_20 : BinaryAutomaton.fibonacciSum fibonacciWord_20 2 = 20 := by decide
theorem output_20 : BinaryAutomaton.classify fibonacciWord_20 = some 0 := by decide
theorem predicate_20 : BinaryAutomaton.binaryDifference 20 = (0 : ℤ) := by
  simpa only [input_20, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_20
def fibonacciWord_21 : List Bool := [true, false, false, false, false, false, false]
theorem input_21 : BinaryAutomaton.fibonacciSum fibonacciWord_21 2 = 21 := by decide
theorem output_21 : BinaryAutomaton.classify fibonacciWord_21 = some 1 := by decide
theorem predicate_21 : BinaryAutomaton.binaryDifference 21 = (1 : ℤ) := by
  simpa only [input_21, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_21
def fibonacciWord_22 : List Bool := [true, false, false, false, false, false, true]
theorem input_22 : BinaryAutomaton.fibonacciSum fibonacciWord_22 2 = 22 := by decide
theorem output_22 : BinaryAutomaton.classify fibonacciWord_22 = some 1 := by decide
theorem predicate_22 : BinaryAutomaton.binaryDifference 22 = (1 : ℤ) := by
  simpa only [input_22, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_22
def fibonacciWord_23 : List Bool := [true, false, false, false, false, true, false]
theorem input_23 : BinaryAutomaton.fibonacciSum fibonacciWord_23 2 = 23 := by decide
theorem output_23 : BinaryAutomaton.classify fibonacciWord_23 = some 0 := by decide
theorem predicate_23 : BinaryAutomaton.binaryDifference 23 = (0 : ℤ) := by
  simpa only [input_23, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_23
def fibonacciWord_24 : List Bool := [true, false, false, false, true, false, false]
theorem input_24 : BinaryAutomaton.fibonacciSum fibonacciWord_24 2 = 24 := by decide
theorem output_24 : BinaryAutomaton.classify fibonacciWord_24 = some 1 := by decide
theorem predicate_24 : BinaryAutomaton.binaryDifference 24 = (1 : ℤ) := by
  simpa only [input_24, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_24
def fibonacciWord_25 : List Bool := [true, false, false, false, true, false, true]
theorem input_25 : BinaryAutomaton.fibonacciSum fibonacciWord_25 2 = 25 := by decide
theorem output_25 : BinaryAutomaton.classify fibonacciWord_25 = some 0 := by decide
theorem predicate_25 : BinaryAutomaton.binaryDifference 25 = (0 : ℤ) := by
  simpa only [input_25, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_25
def fibonacciWord_26 : List Bool := [true, false, false, true, false, false, false]
theorem input_26 : BinaryAutomaton.fibonacciSum fibonacciWord_26 2 = 26 := by decide
theorem output_26 : BinaryAutomaton.classify fibonacciWord_26 = some 0 := by decide
theorem predicate_26 : BinaryAutomaton.binaryDifference 26 = (0 : ℤ) := by
  simpa only [input_26, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_26
def fibonacciWord_27 : List Bool := [true, false, false, true, false, false, true]
theorem input_27 : BinaryAutomaton.fibonacciSum fibonacciWord_27 2 = 27 := by decide
theorem output_27 : BinaryAutomaton.classify fibonacciWord_27 = some 1 := by decide
theorem predicate_27 : BinaryAutomaton.binaryDifference 27 = (1 : ℤ) := by
  simpa only [input_27, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_27
def fibonacciWord_28 : List Bool := [true, false, false, true, false, true, false]
theorem input_28 : BinaryAutomaton.fibonacciSum fibonacciWord_28 2 = 28 := by decide
theorem output_28 : BinaryAutomaton.classify fibonacciWord_28 = some 0 := by decide
theorem predicate_28 : BinaryAutomaton.binaryDifference 28 = (0 : ℤ) := by
  simpa only [input_28, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_28
def fibonacciWord_29 : List Bool := [true, false, true, false, false, false, false]
theorem input_29 : BinaryAutomaton.fibonacciSum fibonacciWord_29 2 = 29 := by decide
theorem output_29 : BinaryAutomaton.classify fibonacciWord_29 = some 1 := by decide
theorem predicate_29 : BinaryAutomaton.binaryDifference 29 = (1 : ℤ) := by
  simpa only [input_29, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_29
def fibonacciWord_30 : List Bool := [true, false, true, false, false, false, true]
theorem input_30 : BinaryAutomaton.fibonacciSum fibonacciWord_30 2 = 30 := by decide
theorem output_30 : BinaryAutomaton.classify fibonacciWord_30 = some 1 := by decide
theorem predicate_30 : BinaryAutomaton.binaryDifference 30 = (1 : ℤ) := by
  simpa only [input_30, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_30
def fibonacciWord_31 : List Bool := [true, false, true, false, false, true, false]
theorem input_31 : BinaryAutomaton.fibonacciSum fibonacciWord_31 2 = 31 := by decide
theorem output_31 : BinaryAutomaton.classify fibonacciWord_31 = some 0 := by decide
theorem predicate_31 : BinaryAutomaton.binaryDifference 31 = (0 : ℤ) := by
  simpa only [input_31, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_31
def fibonacciWord_32 : List Bool := [true, false, true, false, true, false, false]
theorem input_32 : BinaryAutomaton.fibonacciSum fibonacciWord_32 2 = 32 := by decide
theorem output_32 : BinaryAutomaton.classify fibonacciWord_32 = some 1 := by decide
theorem predicate_32 : BinaryAutomaton.binaryDifference 32 = (1 : ℤ) := by
  simpa only [input_32, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_32
theorem powerDigit_5 : digit 2 5 = (1 : ℤ) :=
  BinaryAutomaton.power_input_digit input_32 output_32
def fibonacciWord_33 : List Bool := [true, false, true, false, true, false, true]
theorem input_33 : BinaryAutomaton.fibonacciSum fibonacciWord_33 2 = 33 := by decide
theorem output_33 : BinaryAutomaton.classify fibonacciWord_33 = some 0 := by decide
theorem predicate_33 : BinaryAutomaton.binaryDifference 33 = (0 : ℤ) := by
  simpa only [input_33, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_33
def fibonacciWord_34 : List Bool := [true, false, false, false, false, false, false, false]
theorem input_34 : BinaryAutomaton.fibonacciSum fibonacciWord_34 2 = 34 := by decide
theorem output_34 : BinaryAutomaton.classify fibonacciWord_34 = some 0 := by decide
theorem predicate_34 : BinaryAutomaton.binaryDifference 34 = (0 : ℤ) := by
  simpa only [input_34, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_34
def fibonacciWord_35 : List Bool := [true, false, false, false, false, false, false, true]
theorem input_35 : BinaryAutomaton.fibonacciSum fibonacciWord_35 2 = 35 := by decide
theorem output_35 : BinaryAutomaton.classify fibonacciWord_35 = some 1 := by decide
theorem predicate_35 : BinaryAutomaton.binaryDifference 35 = (1 : ℤ) := by
  simpa only [input_35, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_35
def fibonacciWord_36 : List Bool := [true, false, false, false, false, false, true, false]
theorem input_36 : BinaryAutomaton.fibonacciSum fibonacciWord_36 2 = 36 := by decide
theorem output_36 : BinaryAutomaton.classify fibonacciWord_36 = some 0 := by decide
theorem predicate_36 : BinaryAutomaton.binaryDifference 36 = (0 : ℤ) := by
  simpa only [input_36, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_36
def fibonacciWord_37 : List Bool := [true, false, false, false, false, true, false, false]
theorem input_37 : BinaryAutomaton.fibonacciSum fibonacciWord_37 2 = 37 := by decide
theorem output_37 : BinaryAutomaton.classify fibonacciWord_37 = some 1 := by decide
theorem predicate_37 : BinaryAutomaton.binaryDifference 37 = (1 : ℤ) := by
  simpa only [input_37, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_37
def fibonacciWord_38 : List Bool := [true, false, false, false, false, true, false, true]
theorem input_38 : BinaryAutomaton.fibonacciSum fibonacciWord_38 2 = 38 := by decide
theorem output_38 : BinaryAutomaton.classify fibonacciWord_38 = some 0 := by decide
theorem predicate_38 : BinaryAutomaton.binaryDifference 38 = (0 : ℤ) := by
  simpa only [input_38, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_38
def fibonacciWord_39 : List Bool := [true, false, false, false, true, false, false, false]
theorem input_39 : BinaryAutomaton.fibonacciSum fibonacciWord_39 2 = 39 := by decide
theorem output_39 : BinaryAutomaton.classify fibonacciWord_39 = some 0 := by decide
theorem predicate_39 : BinaryAutomaton.binaryDifference 39 = (0 : ℤ) := by
  simpa only [input_39, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_39
def fibonacciWord_40 : List Bool := [true, false, false, false, true, false, false, true]
theorem input_40 : BinaryAutomaton.fibonacciSum fibonacciWord_40 2 = 40 := by decide
theorem output_40 : BinaryAutomaton.classify fibonacciWord_40 = some 1 := by decide
theorem predicate_40 : BinaryAutomaton.binaryDifference 40 = (1 : ℤ) := by
  simpa only [input_40, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_40
def fibonacciWord_41 : List Bool := [true, false, false, false, true, false, true, false]
theorem input_41 : BinaryAutomaton.fibonacciSum fibonacciWord_41 2 = 41 := by decide
theorem output_41 : BinaryAutomaton.classify fibonacciWord_41 = some 0 := by decide
theorem predicate_41 : BinaryAutomaton.binaryDifference 41 = (0 : ℤ) := by
  simpa only [input_41, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_41
def fibonacciWord_42 : List Bool := [true, false, false, true, false, false, false, false]
theorem input_42 : BinaryAutomaton.fibonacciSum fibonacciWord_42 2 = 42 := by decide
theorem output_42 : BinaryAutomaton.classify fibonacciWord_42 = some 1 := by decide
theorem predicate_42 : BinaryAutomaton.binaryDifference 42 = (1 : ℤ) := by
  simpa only [input_42, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_42
def fibonacciWord_43 : List Bool := [true, false, false, true, false, false, false, true]
theorem input_43 : BinaryAutomaton.fibonacciSum fibonacciWord_43 2 = 43 := by decide
theorem output_43 : BinaryAutomaton.classify fibonacciWord_43 = some 1 := by decide
theorem predicate_43 : BinaryAutomaton.binaryDifference 43 = (1 : ℤ) := by
  simpa only [input_43, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_43
def fibonacciWord_44 : List Bool := [true, false, false, true, false, false, true, false]
theorem input_44 : BinaryAutomaton.fibonacciSum fibonacciWord_44 2 = 44 := by decide
theorem output_44 : BinaryAutomaton.classify fibonacciWord_44 = some 0 := by decide
theorem predicate_44 : BinaryAutomaton.binaryDifference 44 = (0 : ℤ) := by
  simpa only [input_44, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_44
def fibonacciWord_45 : List Bool := [true, false, false, true, false, true, false, false]
theorem input_45 : BinaryAutomaton.fibonacciSum fibonacciWord_45 2 = 45 := by decide
theorem output_45 : BinaryAutomaton.classify fibonacciWord_45 = some 1 := by decide
theorem predicate_45 : BinaryAutomaton.binaryDifference 45 = (1 : ℤ) := by
  simpa only [input_45, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_45
def fibonacciWord_46 : List Bool := [true, false, false, true, false, true, false, true]
theorem input_46 : BinaryAutomaton.fibonacciSum fibonacciWord_46 2 = 46 := by decide
theorem output_46 : BinaryAutomaton.classify fibonacciWord_46 = some 0 := by decide
theorem predicate_46 : BinaryAutomaton.binaryDifference 46 = (0 : ℤ) := by
  simpa only [input_46, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_46
def fibonacciWord_47 : List Bool := [true, false, true, false, false, false, false, false]
theorem input_47 : BinaryAutomaton.fibonacciSum fibonacciWord_47 2 = 47 := by decide
theorem output_47 : BinaryAutomaton.classify fibonacciWord_47 = some 0 := by decide
theorem predicate_47 : BinaryAutomaton.binaryDifference 47 = (0 : ℤ) := by
  simpa only [input_47, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_47
def fibonacciWord_48 : List Bool := [true, false, true, false, false, false, false, true]
theorem input_48 : BinaryAutomaton.fibonacciSum fibonacciWord_48 2 = 48 := by decide
theorem output_48 : BinaryAutomaton.classify fibonacciWord_48 = some 1 := by decide
theorem predicate_48 : BinaryAutomaton.binaryDifference 48 = (1 : ℤ) := by
  simpa only [input_48, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_48
def fibonacciWord_49 : List Bool := [true, false, true, false, false, false, true, false]
theorem input_49 : BinaryAutomaton.fibonacciSum fibonacciWord_49 2 = 49 := by decide
theorem output_49 : BinaryAutomaton.classify fibonacciWord_49 = some 0 := by decide
theorem predicate_49 : BinaryAutomaton.binaryDifference 49 = (0 : ℤ) := by
  simpa only [input_49, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_49
def fibonacciWord_50 : List Bool := [true, false, true, false, false, true, false, false]
theorem input_50 : BinaryAutomaton.fibonacciSum fibonacciWord_50 2 = 50 := by decide
theorem output_50 : BinaryAutomaton.classify fibonacciWord_50 = some 1 := by decide
theorem predicate_50 : BinaryAutomaton.binaryDifference 50 = (1 : ℤ) := by
  simpa only [input_50, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_50
def fibonacciWord_51 : List Bool := [true, false, true, false, false, true, false, true]
theorem input_51 : BinaryAutomaton.fibonacciSum fibonacciWord_51 2 = 51 := by decide
theorem output_51 : BinaryAutomaton.classify fibonacciWord_51 = some 1 := by decide
theorem predicate_51 : BinaryAutomaton.binaryDifference 51 = (1 : ℤ) := by
  simpa only [input_51, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_51
def fibonacciWord_52 : List Bool := [true, false, true, false, true, false, false, false]
theorem input_52 : BinaryAutomaton.fibonacciSum fibonacciWord_52 2 = 52 := by decide
theorem output_52 : BinaryAutomaton.classify fibonacciWord_52 = some 0 := by decide
theorem predicate_52 : BinaryAutomaton.binaryDifference 52 = (0 : ℤ) := by
  simpa only [input_52, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_52
def fibonacciWord_53 : List Bool := [true, false, true, false, true, false, false, true]
theorem input_53 : BinaryAutomaton.fibonacciSum fibonacciWord_53 2 = 53 := by decide
theorem output_53 : BinaryAutomaton.classify fibonacciWord_53 = some 1 := by decide
theorem predicate_53 : BinaryAutomaton.binaryDifference 53 = (1 : ℤ) := by
  simpa only [input_53, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_53
def fibonacciWord_54 : List Bool := [true, false, true, false, true, false, true, false]
theorem input_54 : BinaryAutomaton.fibonacciSum fibonacciWord_54 2 = 54 := by decide
theorem output_54 : BinaryAutomaton.classify fibonacciWord_54 = some 0 := by decide
theorem predicate_54 : BinaryAutomaton.binaryDifference 54 = (0 : ℤ) := by
  simpa only [input_54, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_54
def fibonacciWord_55 : List Bool := [true, false, false, false, false, false, false, false, false]
theorem input_55 : BinaryAutomaton.fibonacciSum fibonacciWord_55 2 = 55 := by decide
theorem output_55 : BinaryAutomaton.classify fibonacciWord_55 = some 1 := by decide
theorem predicate_55 : BinaryAutomaton.binaryDifference 55 = (1 : ℤ) := by
  simpa only [input_55, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_55
def fibonacciWord_56 : List Bool := [true, false, false, false, false, false, false, false, true]
theorem input_56 : BinaryAutomaton.fibonacciSum fibonacciWord_56 2 = 56 := by decide
theorem output_56 : BinaryAutomaton.classify fibonacciWord_56 = some 1 := by decide
theorem predicate_56 : BinaryAutomaton.binaryDifference 56 = (1 : ℤ) := by
  simpa only [input_56, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_56
def fibonacciWord_57 : List Bool := [true, false, false, false, false, false, false, true, false]
theorem input_57 : BinaryAutomaton.fibonacciSum fibonacciWord_57 2 = 57 := by decide
theorem output_57 : BinaryAutomaton.classify fibonacciWord_57 = some 0 := by decide
theorem predicate_57 : BinaryAutomaton.binaryDifference 57 = (0 : ℤ) := by
  simpa only [input_57, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_57
def fibonacciWord_58 : List Bool := [true, false, false, false, false, false, true, false, false]
theorem input_58 : BinaryAutomaton.fibonacciSum fibonacciWord_58 2 = 58 := by decide
theorem output_58 : BinaryAutomaton.classify fibonacciWord_58 = some 1 := by decide
theorem predicate_58 : BinaryAutomaton.binaryDifference 58 = (1 : ℤ) := by
  simpa only [input_58, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_58
def fibonacciWord_59 : List Bool := [true, false, false, false, false, false, true, false, true]
theorem input_59 : BinaryAutomaton.fibonacciSum fibonacciWord_59 2 = 59 := by decide
theorem output_59 : BinaryAutomaton.classify fibonacciWord_59 = some 0 := by decide
theorem predicate_59 : BinaryAutomaton.binaryDifference 59 = (0 : ℤ) := by
  simpa only [input_59, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_59
def fibonacciWord_60 : List Bool := [true, false, false, false, false, true, false, false, false]
theorem input_60 : BinaryAutomaton.fibonacciSum fibonacciWord_60 2 = 60 := by decide
theorem output_60 : BinaryAutomaton.classify fibonacciWord_60 = some 0 := by decide
theorem predicate_60 : BinaryAutomaton.binaryDifference 60 = (0 : ℤ) := by
  simpa only [input_60, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_60
def fibonacciWord_61 : List Bool := [true, false, false, false, false, true, false, false, true]
theorem input_61 : BinaryAutomaton.fibonacciSum fibonacciWord_61 2 = 61 := by decide
theorem output_61 : BinaryAutomaton.classify fibonacciWord_61 = some 1 := by decide
theorem predicate_61 : BinaryAutomaton.binaryDifference 61 = (1 : ℤ) := by
  simpa only [input_61, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_61
def fibonacciWord_62 : List Bool := [true, false, false, false, false, true, false, true, false]
theorem input_62 : BinaryAutomaton.fibonacciSum fibonacciWord_62 2 = 62 := by decide
theorem output_62 : BinaryAutomaton.classify fibonacciWord_62 = some 0 := by decide
theorem predicate_62 : BinaryAutomaton.binaryDifference 62 = (0 : ℤ) := by
  simpa only [input_62, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_62
def fibonacciWord_63 : List Bool := [true, false, false, false, true, false, false, false, false]
theorem input_63 : BinaryAutomaton.fibonacciSum fibonacciWord_63 2 = 63 := by decide
theorem output_63 : BinaryAutomaton.classify fibonacciWord_63 = some 1 := by decide
theorem predicate_63 : BinaryAutomaton.binaryDifference 63 = (1 : ℤ) := by
  simpa only [input_63, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_63
def fibonacciWord_64 : List Bool := [true, false, false, false, true, false, false, false, true]
theorem input_64 : BinaryAutomaton.fibonacciSum fibonacciWord_64 2 = 64 := by decide
theorem output_64 : BinaryAutomaton.classify fibonacciWord_64 = some 1 := by decide
theorem predicate_64 : BinaryAutomaton.binaryDifference 64 = (1 : ℤ) := by
  simpa only [input_64, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_64
theorem powerDigit_6 : digit 2 6 = (1 : ℤ) :=
  BinaryAutomaton.power_input_digit input_64 output_64
def fibonacciWord_65 : List Bool := [true, false, false, false, true, false, false, true, false]
theorem input_65 : BinaryAutomaton.fibonacciSum fibonacciWord_65 2 = 65 := by decide
theorem output_65 : BinaryAutomaton.classify fibonacciWord_65 = some 0 := by decide
theorem predicate_65 : BinaryAutomaton.binaryDifference 65 = (0 : ℤ) := by
  simpa only [input_65, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_65
def fibonacciWord_66 : List Bool := [true, false, false, false, true, false, true, false, false]
theorem input_66 : BinaryAutomaton.fibonacciSum fibonacciWord_66 2 = 66 := by decide
theorem output_66 : BinaryAutomaton.classify fibonacciWord_66 = some 1 := by decide
theorem predicate_66 : BinaryAutomaton.binaryDifference 66 = (1 : ℤ) := by
  simpa only [input_66, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_66
def fibonacciWord_67 : List Bool := [true, false, false, false, true, false, true, false, true]
theorem input_67 : BinaryAutomaton.fibonacciSum fibonacciWord_67 2 = 67 := by decide
theorem output_67 : BinaryAutomaton.classify fibonacciWord_67 = some 0 := by decide
theorem predicate_67 : BinaryAutomaton.binaryDifference 67 = (0 : ℤ) := by
  simpa only [input_67, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_67
def fibonacciWord_68 : List Bool := [true, false, false, true, false, false, false, false, false]
theorem input_68 : BinaryAutomaton.fibonacciSum fibonacciWord_68 2 = 68 := by decide
theorem output_68 : BinaryAutomaton.classify fibonacciWord_68 = some 0 := by decide
theorem predicate_68 : BinaryAutomaton.binaryDifference 68 = (0 : ℤ) := by
  simpa only [input_68, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_68
def fibonacciWord_69 : List Bool := [true, false, false, true, false, false, false, false, true]
theorem input_69 : BinaryAutomaton.fibonacciSum fibonacciWord_69 2 = 69 := by decide
theorem output_69 : BinaryAutomaton.classify fibonacciWord_69 = some 1 := by decide
theorem predicate_69 : BinaryAutomaton.binaryDifference 69 = (1 : ℤ) := by
  simpa only [input_69, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_69
def fibonacciWord_70 : List Bool := [true, false, false, true, false, false, false, true, false]
theorem input_70 : BinaryAutomaton.fibonacciSum fibonacciWord_70 2 = 70 := by decide
theorem output_70 : BinaryAutomaton.classify fibonacciWord_70 = some 0 := by decide
theorem predicate_70 : BinaryAutomaton.binaryDifference 70 = (0 : ℤ) := by
  simpa only [input_70, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_70
def fibonacciWord_71 : List Bool := [true, false, false, true, false, false, true, false, false]
theorem input_71 : BinaryAutomaton.fibonacciSum fibonacciWord_71 2 = 71 := by decide
theorem output_71 : BinaryAutomaton.classify fibonacciWord_71 = some 1 := by decide
theorem predicate_71 : BinaryAutomaton.binaryDifference 71 = (1 : ℤ) := by
  simpa only [input_71, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_71
def fibonacciWord_72 : List Bool := [true, false, false, true, false, false, true, false, true]
theorem input_72 : BinaryAutomaton.fibonacciSum fibonacciWord_72 2 = 72 := by decide
theorem output_72 : BinaryAutomaton.classify fibonacciWord_72 = some 0 := by decide
theorem predicate_72 : BinaryAutomaton.binaryDifference 72 = (0 : ℤ) := by
  simpa only [input_72, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_72
def fibonacciWord_73 : List Bool := [true, false, false, true, false, true, false, false, false]
theorem input_73 : BinaryAutomaton.fibonacciSum fibonacciWord_73 2 = 73 := by decide
theorem output_73 : BinaryAutomaton.classify fibonacciWord_73 = some 0 := by decide
theorem predicate_73 : BinaryAutomaton.binaryDifference 73 = (0 : ℤ) := by
  simpa only [input_73, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_73
def fibonacciWord_74 : List Bool := [true, false, false, true, false, true, false, false, true]
theorem input_74 : BinaryAutomaton.fibonacciSum fibonacciWord_74 2 = 74 := by decide
theorem output_74 : BinaryAutomaton.classify fibonacciWord_74 = some 1 := by decide
theorem predicate_74 : BinaryAutomaton.binaryDifference 74 = (1 : ℤ) := by
  simpa only [input_74, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_74
def fibonacciWord_75 : List Bool := [true, false, false, true, false, true, false, true, false]
theorem input_75 : BinaryAutomaton.fibonacciSum fibonacciWord_75 2 = 75 := by decide
theorem output_75 : BinaryAutomaton.classify fibonacciWord_75 = some 0 := by decide
theorem predicate_75 : BinaryAutomaton.binaryDifference 75 = (0 : ℤ) := by
  simpa only [input_75, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_75
def fibonacciWord_76 : List Bool := [true, false, true, false, false, false, false, false, false]
theorem input_76 : BinaryAutomaton.fibonacciSum fibonacciWord_76 2 = 76 := by decide
theorem output_76 : BinaryAutomaton.classify fibonacciWord_76 = some 1 := by decide
theorem predicate_76 : BinaryAutomaton.binaryDifference 76 = (1 : ℤ) := by
  simpa only [input_76, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_76
def fibonacciWord_77 : List Bool := [true, false, true, false, false, false, false, false, true]
theorem input_77 : BinaryAutomaton.fibonacciSum fibonacciWord_77 2 = 77 := by decide
theorem output_77 : BinaryAutomaton.classify fibonacciWord_77 = some 1 := by decide
theorem predicate_77 : BinaryAutomaton.binaryDifference 77 = (1 : ℤ) := by
  simpa only [input_77, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_77
def fibonacciWord_78 : List Bool := [true, false, true, false, false, false, false, true, false]
theorem input_78 : BinaryAutomaton.fibonacciSum fibonacciWord_78 2 = 78 := by decide
theorem output_78 : BinaryAutomaton.classify fibonacciWord_78 = some 0 := by decide
theorem predicate_78 : BinaryAutomaton.binaryDifference 78 = (0 : ℤ) := by
  simpa only [input_78, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_78
def fibonacciWord_79 : List Bool := [true, false, true, false, false, false, true, false, false]
theorem input_79 : BinaryAutomaton.fibonacciSum fibonacciWord_79 2 = 79 := by decide
theorem output_79 : BinaryAutomaton.classify fibonacciWord_79 = some 1 := by decide
theorem predicate_79 : BinaryAutomaton.binaryDifference 79 = (1 : ℤ) := by
  simpa only [input_79, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_79
def fibonacciWord_80 : List Bool := [true, false, true, false, false, false, true, false, true]
theorem input_80 : BinaryAutomaton.fibonacciSum fibonacciWord_80 2 = 80 := by decide
theorem output_80 : BinaryAutomaton.classify fibonacciWord_80 = some 0 := by decide
theorem predicate_80 : BinaryAutomaton.binaryDifference 80 = (0 : ℤ) := by
  simpa only [input_80, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_80
def fibonacciWord_81 : List Bool := [true, false, true, false, false, true, false, false, false]
theorem input_81 : BinaryAutomaton.fibonacciSum fibonacciWord_81 2 = 81 := by decide
theorem output_81 : BinaryAutomaton.classify fibonacciWord_81 = some 0 := by decide
theorem predicate_81 : BinaryAutomaton.binaryDifference 81 = (0 : ℤ) := by
  simpa only [input_81, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_81
def fibonacciWord_82 : List Bool := [true, false, true, false, false, true, false, false, true]
theorem input_82 : BinaryAutomaton.fibonacciSum fibonacciWord_82 2 = 82 := by decide
theorem output_82 : BinaryAutomaton.classify fibonacciWord_82 = some 1 := by decide
theorem predicate_82 : BinaryAutomaton.binaryDifference 82 = (1 : ℤ) := by
  simpa only [input_82, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_82
def fibonacciWord_83 : List Bool := [true, false, true, false, false, true, false, true, false]
theorem input_83 : BinaryAutomaton.fibonacciSum fibonacciWord_83 2 = 83 := by decide
theorem output_83 : BinaryAutomaton.classify fibonacciWord_83 = some 0 := by decide
theorem predicate_83 : BinaryAutomaton.binaryDifference 83 = (0 : ℤ) := by
  simpa only [input_83, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_83
def fibonacciWord_84 : List Bool := [true, false, true, false, true, false, false, false, false]
theorem input_84 : BinaryAutomaton.fibonacciSum fibonacciWord_84 2 = 84 := by decide
theorem output_84 : BinaryAutomaton.classify fibonacciWord_84 = some 1 := by decide
theorem predicate_84 : BinaryAutomaton.binaryDifference 84 = (1 : ℤ) := by
  simpa only [input_84, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_84
def fibonacciWord_85 : List Bool := [true, false, true, false, true, false, false, false, true]
theorem input_85 : BinaryAutomaton.fibonacciSum fibonacciWord_85 2 = 85 := by decide
theorem output_85 : BinaryAutomaton.classify fibonacciWord_85 = some 1 := by decide
theorem predicate_85 : BinaryAutomaton.binaryDifference 85 = (1 : ℤ) := by
  simpa only [input_85, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_85
def fibonacciWord_86 : List Bool := [true, false, true, false, true, false, false, true, false]
theorem input_86 : BinaryAutomaton.fibonacciSum fibonacciWord_86 2 = 86 := by decide
theorem output_86 : BinaryAutomaton.classify fibonacciWord_86 = some 0 := by decide
theorem predicate_86 : BinaryAutomaton.binaryDifference 86 = (0 : ℤ) := by
  simpa only [input_86, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_86
def fibonacciWord_87 : List Bool := [true, false, true, false, true, false, true, false, false]
theorem input_87 : BinaryAutomaton.fibonacciSum fibonacciWord_87 2 = 87 := by decide
theorem output_87 : BinaryAutomaton.classify fibonacciWord_87 = some 1 := by decide
theorem predicate_87 : BinaryAutomaton.binaryDifference 87 = (1 : ℤ) := by
  simpa only [input_87, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_87
def fibonacciWord_88 : List Bool := [true, false, true, false, true, false, true, false, true]
theorem input_88 : BinaryAutomaton.fibonacciSum fibonacciWord_88 2 = 88 := by decide
theorem output_88 : BinaryAutomaton.classify fibonacciWord_88 = some 0 := by decide
theorem predicate_88 : BinaryAutomaton.binaryDifference 88 = (0 : ℤ) := by
  simpa only [input_88, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_88
def fibonacciWord_89 : List Bool := [true, false, false, false, false, false, false, false, false, false]
theorem input_89 : BinaryAutomaton.fibonacciSum fibonacciWord_89 2 = 89 := by decide
theorem output_89 : BinaryAutomaton.classify fibonacciWord_89 = some 0 := by decide
theorem predicate_89 : BinaryAutomaton.binaryDifference 89 = (0 : ℤ) := by
  simpa only [input_89, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_89
def fibonacciWord_90 : List Bool := [true, false, false, false, false, false, false, false, false, true]
theorem input_90 : BinaryAutomaton.fibonacciSum fibonacciWord_90 2 = 90 := by decide
theorem output_90 : BinaryAutomaton.classify fibonacciWord_90 = some 1 := by decide
theorem predicate_90 : BinaryAutomaton.binaryDifference 90 = (1 : ℤ) := by
  simpa only [input_90, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_90
def fibonacciWord_91 : List Bool := [true, false, false, false, false, false, false, false, true, false]
theorem input_91 : BinaryAutomaton.fibonacciSum fibonacciWord_91 2 = 91 := by decide
theorem output_91 : BinaryAutomaton.classify fibonacciWord_91 = some 0 := by decide
theorem predicate_91 : BinaryAutomaton.binaryDifference 91 = (0 : ℤ) := by
  simpa only [input_91, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_91
def fibonacciWord_92 : List Bool := [true, false, false, false, false, false, false, true, false, false]
theorem input_92 : BinaryAutomaton.fibonacciSum fibonacciWord_92 2 = 92 := by decide
theorem output_92 : BinaryAutomaton.classify fibonacciWord_92 = some 1 := by decide
theorem predicate_92 : BinaryAutomaton.binaryDifference 92 = (1 : ℤ) := by
  simpa only [input_92, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_92
def fibonacciWord_93 : List Bool := [true, false, false, false, false, false, false, true, false, true]
theorem input_93 : BinaryAutomaton.fibonacciSum fibonacciWord_93 2 = 93 := by decide
theorem output_93 : BinaryAutomaton.classify fibonacciWord_93 = some 0 := by decide
theorem predicate_93 : BinaryAutomaton.binaryDifference 93 = (0 : ℤ) := by
  simpa only [input_93, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_93
def fibonacciWord_94 : List Bool := [true, false, false, false, false, false, true, false, false, false]
theorem input_94 : BinaryAutomaton.fibonacciSum fibonacciWord_94 2 = 94 := by decide
theorem output_94 : BinaryAutomaton.classify fibonacciWord_94 = some 0 := by decide
theorem predicate_94 : BinaryAutomaton.binaryDifference 94 = (0 : ℤ) := by
  simpa only [input_94, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_94
def fibonacciWord_95 : List Bool := [true, false, false, false, false, false, true, false, false, true]
theorem input_95 : BinaryAutomaton.fibonacciSum fibonacciWord_95 2 = 95 := by decide
theorem output_95 : BinaryAutomaton.classify fibonacciWord_95 = some 1 := by decide
theorem predicate_95 : BinaryAutomaton.binaryDifference 95 = (1 : ℤ) := by
  simpa only [input_95, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_95
def fibonacciWord_96 : List Bool := [true, false, false, false, false, false, true, false, true, false]
theorem input_96 : BinaryAutomaton.fibonacciSum fibonacciWord_96 2 = 96 := by decide
theorem output_96 : BinaryAutomaton.classify fibonacciWord_96 = some 0 := by decide
theorem predicate_96 : BinaryAutomaton.binaryDifference 96 = (0 : ℤ) := by
  simpa only [input_96, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_96
def fibonacciWord_97 : List Bool := [true, false, false, false, false, true, false, false, false, false]
theorem input_97 : BinaryAutomaton.fibonacciSum fibonacciWord_97 2 = 97 := by decide
theorem output_97 : BinaryAutomaton.classify fibonacciWord_97 = some 1 := by decide
theorem predicate_97 : BinaryAutomaton.binaryDifference 97 = (1 : ℤ) := by
  simpa only [input_97, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_97
def fibonacciWord_98 : List Bool := [true, false, false, false, false, true, false, false, false, true]
theorem input_98 : BinaryAutomaton.fibonacciSum fibonacciWord_98 2 = 98 := by decide
theorem output_98 : BinaryAutomaton.classify fibonacciWord_98 = some 1 := by decide
theorem predicate_98 : BinaryAutomaton.binaryDifference 98 = (1 : ℤ) := by
  simpa only [input_98, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_98
def fibonacciWord_99 : List Bool := [true, false, false, false, false, true, false, false, true, false]
theorem input_99 : BinaryAutomaton.fibonacciSum fibonacciWord_99 2 = 99 := by decide
theorem output_99 : BinaryAutomaton.classify fibonacciWord_99 = some 0 := by decide
theorem predicate_99 : BinaryAutomaton.binaryDifference 99 = (0 : ℤ) := by
  simpa only [input_99, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_99
def fibonacciWord_100 : List Bool := [true, false, false, false, false, true, false, true, false, false]
theorem input_100 : BinaryAutomaton.fibonacciSum fibonacciWord_100 2 = 100 := by decide
theorem output_100 : BinaryAutomaton.classify fibonacciWord_100 = some 1 := by decide
theorem predicate_100 : BinaryAutomaton.binaryDifference 100 = (1 : ℤ) := by
  simpa only [input_100, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_100
def fibonacciWord_101 : List Bool := [true, false, false, false, false, true, false, true, false, true]
theorem input_101 : BinaryAutomaton.fibonacciSum fibonacciWord_101 2 = 101 := by decide
theorem output_101 : BinaryAutomaton.classify fibonacciWord_101 = some 0 := by decide
theorem predicate_101 : BinaryAutomaton.binaryDifference 101 = (0 : ℤ) := by
  simpa only [input_101, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_101
def fibonacciWord_102 : List Bool := [true, false, false, false, true, false, false, false, false, false]
theorem input_102 : BinaryAutomaton.fibonacciSum fibonacciWord_102 2 = 102 := by decide
theorem output_102 : BinaryAutomaton.classify fibonacciWord_102 = some 0 := by decide
theorem predicate_102 : BinaryAutomaton.binaryDifference 102 = (0 : ℤ) := by
  simpa only [input_102, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_102
def fibonacciWord_103 : List Bool := [true, false, false, false, true, false, false, false, false, true]
theorem input_103 : BinaryAutomaton.fibonacciSum fibonacciWord_103 2 = 103 := by decide
theorem output_103 : BinaryAutomaton.classify fibonacciWord_103 = some 1 := by decide
theorem predicate_103 : BinaryAutomaton.binaryDifference 103 = (1 : ℤ) := by
  simpa only [input_103, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_103
def fibonacciWord_104 : List Bool := [true, false, false, false, true, false, false, false, true, false]
theorem input_104 : BinaryAutomaton.fibonacciSum fibonacciWord_104 2 = 104 := by decide
theorem output_104 : BinaryAutomaton.classify fibonacciWord_104 = some 0 := by decide
theorem predicate_104 : BinaryAutomaton.binaryDifference 104 = (0 : ℤ) := by
  simpa only [input_104, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_104
def fibonacciWord_105 : List Bool := [true, false, false, false, true, false, false, true, false, false]
theorem input_105 : BinaryAutomaton.fibonacciSum fibonacciWord_105 2 = 105 := by decide
theorem output_105 : BinaryAutomaton.classify fibonacciWord_105 = some 1 := by decide
theorem predicate_105 : BinaryAutomaton.binaryDifference 105 = (1 : ℤ) := by
  simpa only [input_105, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_105
def fibonacciWord_106 : List Bool := [true, false, false, false, true, false, false, true, false, true]
theorem input_106 : BinaryAutomaton.fibonacciSum fibonacciWord_106 2 = 106 := by decide
theorem output_106 : BinaryAutomaton.classify fibonacciWord_106 = some 1 := by decide
theorem predicate_106 : BinaryAutomaton.binaryDifference 106 = (1 : ℤ) := by
  simpa only [input_106, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_106
def fibonacciWord_107 : List Bool := [true, false, false, false, true, false, true, false, false, false]
theorem input_107 : BinaryAutomaton.fibonacciSum fibonacciWord_107 2 = 107 := by decide
theorem output_107 : BinaryAutomaton.classify fibonacciWord_107 = some 0 := by decide
theorem predicate_107 : BinaryAutomaton.binaryDifference 107 = (0 : ℤ) := by
  simpa only [input_107, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_107
def fibonacciWord_108 : List Bool := [true, false, false, false, true, false, true, false, false, true]
theorem input_108 : BinaryAutomaton.fibonacciSum fibonacciWord_108 2 = 108 := by decide
theorem output_108 : BinaryAutomaton.classify fibonacciWord_108 = some 1 := by decide
theorem predicate_108 : BinaryAutomaton.binaryDifference 108 = (1 : ℤ) := by
  simpa only [input_108, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_108
def fibonacciWord_109 : List Bool := [true, false, false, false, true, false, true, false, true, false]
theorem input_109 : BinaryAutomaton.fibonacciSum fibonacciWord_109 2 = 109 := by decide
theorem output_109 : BinaryAutomaton.classify fibonacciWord_109 = some 0 := by decide
theorem predicate_109 : BinaryAutomaton.binaryDifference 109 = (0 : ℤ) := by
  simpa only [input_109, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_109
def fibonacciWord_110 : List Bool := [true, false, false, true, false, false, false, false, false, false]
theorem input_110 : BinaryAutomaton.fibonacciSum fibonacciWord_110 2 = 110 := by decide
theorem output_110 : BinaryAutomaton.classify fibonacciWord_110 = some 1 := by decide
theorem predicate_110 : BinaryAutomaton.binaryDifference 110 = (1 : ℤ) := by
  simpa only [input_110, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_110
def fibonacciWord_111 : List Bool := [true, false, false, true, false, false, false, false, false, true]
theorem input_111 : BinaryAutomaton.fibonacciSum fibonacciWord_111 2 = 111 := by decide
theorem output_111 : BinaryAutomaton.classify fibonacciWord_111 = some 1 := by decide
theorem predicate_111 : BinaryAutomaton.binaryDifference 111 = (1 : ℤ) := by
  simpa only [input_111, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_111
def fibonacciWord_112 : List Bool := [true, false, false, true, false, false, false, false, true, false]
theorem input_112 : BinaryAutomaton.fibonacciSum fibonacciWord_112 2 = 112 := by decide
theorem output_112 : BinaryAutomaton.classify fibonacciWord_112 = some 0 := by decide
theorem predicate_112 : BinaryAutomaton.binaryDifference 112 = (0 : ℤ) := by
  simpa only [input_112, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_112
def fibonacciWord_113 : List Bool := [true, false, false, true, false, false, false, true, false, false]
theorem input_113 : BinaryAutomaton.fibonacciSum fibonacciWord_113 2 = 113 := by decide
theorem output_113 : BinaryAutomaton.classify fibonacciWord_113 = some 1 := by decide
theorem predicate_113 : BinaryAutomaton.binaryDifference 113 = (1 : ℤ) := by
  simpa only [input_113, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_113
def fibonacciWord_114 : List Bool := [true, false, false, true, false, false, false, true, false, true]
theorem input_114 : BinaryAutomaton.fibonacciSum fibonacciWord_114 2 = 114 := by decide
theorem output_114 : BinaryAutomaton.classify fibonacciWord_114 = some 0 := by decide
theorem predicate_114 : BinaryAutomaton.binaryDifference 114 = (0 : ℤ) := by
  simpa only [input_114, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_114
def fibonacciWord_115 : List Bool := [true, false, false, true, false, false, true, false, false, false]
theorem input_115 : BinaryAutomaton.fibonacciSum fibonacciWord_115 2 = 115 := by decide
theorem output_115 : BinaryAutomaton.classify fibonacciWord_115 = some 0 := by decide
theorem predicate_115 : BinaryAutomaton.binaryDifference 115 = (0 : ℤ) := by
  simpa only [input_115, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_115
def fibonacciWord_116 : List Bool := [true, false, false, true, false, false, true, false, false, true]
theorem input_116 : BinaryAutomaton.fibonacciSum fibonacciWord_116 2 = 116 := by decide
theorem output_116 : BinaryAutomaton.classify fibonacciWord_116 = some 1 := by decide
theorem predicate_116 : BinaryAutomaton.binaryDifference 116 = (1 : ℤ) := by
  simpa only [input_116, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_116
def fibonacciWord_117 : List Bool := [true, false, false, true, false, false, true, false, true, false]
theorem input_117 : BinaryAutomaton.fibonacciSum fibonacciWord_117 2 = 117 := by decide
theorem output_117 : BinaryAutomaton.classify fibonacciWord_117 = some 0 := by decide
theorem predicate_117 : BinaryAutomaton.binaryDifference 117 = (0 : ℤ) := by
  simpa only [input_117, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_117
def fibonacciWord_118 : List Bool := [true, false, false, true, false, true, false, false, false, false]
theorem input_118 : BinaryAutomaton.fibonacciSum fibonacciWord_118 2 = 118 := by decide
theorem output_118 : BinaryAutomaton.classify fibonacciWord_118 = some 1 := by decide
theorem predicate_118 : BinaryAutomaton.binaryDifference 118 = (1 : ℤ) := by
  simpa only [input_118, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_118
def fibonacciWord_119 : List Bool := [true, false, false, true, false, true, false, false, false, true]
theorem input_119 : BinaryAutomaton.fibonacciSum fibonacciWord_119 2 = 119 := by decide
theorem output_119 : BinaryAutomaton.classify fibonacciWord_119 = some 1 := by decide
theorem predicate_119 : BinaryAutomaton.binaryDifference 119 = (1 : ℤ) := by
  simpa only [input_119, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_119
def fibonacciWord_120 : List Bool := [true, false, false, true, false, true, false, false, true, false]
theorem input_120 : BinaryAutomaton.fibonacciSum fibonacciWord_120 2 = 120 := by decide
theorem output_120 : BinaryAutomaton.classify fibonacciWord_120 = some 0 := by decide
theorem predicate_120 : BinaryAutomaton.binaryDifference 120 = (0 : ℤ) := by
  simpa only [input_120, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_120
def fibonacciWord_121 : List Bool := [true, false, false, true, false, true, false, true, false, false]
theorem input_121 : BinaryAutomaton.fibonacciSum fibonacciWord_121 2 = 121 := by decide
theorem output_121 : BinaryAutomaton.classify fibonacciWord_121 = some 1 := by decide
theorem predicate_121 : BinaryAutomaton.binaryDifference 121 = (1 : ℤ) := by
  simpa only [input_121, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_121
def fibonacciWord_122 : List Bool := [true, false, false, true, false, true, false, true, false, true]
theorem input_122 : BinaryAutomaton.fibonacciSum fibonacciWord_122 2 = 122 := by decide
theorem output_122 : BinaryAutomaton.classify fibonacciWord_122 = some 0 := by decide
theorem predicate_122 : BinaryAutomaton.binaryDifference 122 = (0 : ℤ) := by
  simpa only [input_122, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_122
def fibonacciWord_123 : List Bool := [true, false, true, false, false, false, false, false, false, false]
theorem input_123 : BinaryAutomaton.fibonacciSum fibonacciWord_123 2 = 123 := by decide
theorem output_123 : BinaryAutomaton.classify fibonacciWord_123 = some 0 := by decide
theorem predicate_123 : BinaryAutomaton.binaryDifference 123 = (0 : ℤ) := by
  simpa only [input_123, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_123
def fibonacciWord_124 : List Bool := [true, false, true, false, false, false, false, false, false, true]
theorem input_124 : BinaryAutomaton.fibonacciSum fibonacciWord_124 2 = 124 := by decide
theorem output_124 : BinaryAutomaton.classify fibonacciWord_124 = some 1 := by decide
theorem predicate_124 : BinaryAutomaton.binaryDifference 124 = (1 : ℤ) := by
  simpa only [input_124, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_124
def fibonacciWord_125 : List Bool := [true, false, true, false, false, false, false, false, true, false]
theorem input_125 : BinaryAutomaton.fibonacciSum fibonacciWord_125 2 = 125 := by decide
theorem output_125 : BinaryAutomaton.classify fibonacciWord_125 = some 0 := by decide
theorem predicate_125 : BinaryAutomaton.binaryDifference 125 = (0 : ℤ) := by
  simpa only [input_125, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_125
def fibonacciWord_126 : List Bool := [true, false, true, false, false, false, false, true, false, false]
theorem input_126 : BinaryAutomaton.fibonacciSum fibonacciWord_126 2 = 126 := by decide
theorem output_126 : BinaryAutomaton.classify fibonacciWord_126 = some 1 := by decide
theorem predicate_126 : BinaryAutomaton.binaryDifference 126 = (1 : ℤ) := by
  simpa only [input_126, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_126
def fibonacciWord_127 : List Bool := [true, false, true, false, false, false, false, true, false, true]
theorem input_127 : BinaryAutomaton.fibonacciSum fibonacciWord_127 2 = 127 := by decide
theorem output_127 : BinaryAutomaton.classify fibonacciWord_127 = some 0 := by decide
theorem predicate_127 : BinaryAutomaton.binaryDifference 127 = (0 : ℤ) := by
  simpa only [input_127, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_127
end GoldenNormality.Receipts
