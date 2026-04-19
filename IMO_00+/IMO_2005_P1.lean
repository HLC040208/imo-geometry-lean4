import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Six points are chosen on the sides of an equilateral Triangle $ABC$: $A_1$, $A_2$ on $BC$, $B_1$, $B_2$ on $CA$ and $C_1$, $C_2$ on $AB$, such that they are the vertices of a convex hexagon $A_1A_2B_1B_2C_1C_2$ with equal side lengths. Prove that the lines $A_1B_2$, $B_1C_2$ and $C_1A_2$ are concurrent.
theorem IMO_2005_P1 :
  ∀ (A B C A1 A2 B1 B2 C1 C2 : Point)
    (AB BC CA A1B2 B1C2 C1A2 : Line),
    formTriangle A B C AB BC CA ∧
    |(A─B)| = |(B─C)| ∧ |(B─C)| = |(C─A)| ∧
    between B A1 A2 ∧ between A1 A2 C ∧
    between C B1 B2 ∧ between B1 B2 A ∧
    between A C1 C2 ∧ between C1 C2 B ∧
    distinctPointsOnLine A1 B2 A1B2 ∧
    distinctPointsOnLine B1 C2 B1C2 ∧
    distinctPointsOnLine C1 A2 C1A2 ∧
    |(A1─A2)| = |(B1─B2)| ∧
    |(B1─B2)| = |(C1─C2)| →
    Concurrent A1B2 B1C2 C1A2 := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A1 B2 as lA1B2
  euclid_apply line_from_points B1 C2 as lB1C2
  euclid_apply line_from_points C1 A2 as lC1A2
  euclid_apply line_from_points A1 A2 as A1A2
  euclid_apply line_from_points B1 B2 as B1B2
  euclid_apply line_from_points C1 C2 as C1C2

  have h_tri : formTriangle A B C AB BC CA := by
    euclid_finish

  have h_eq_AB_BC : |(A─B)| = |(B─C)| := by
    euclid_finish

  have h_eq_BC_CA : |(B─C)| = |(C─A)| := by
    euclid_finish

  have hA1_between : between B A1 A2 := by
    euclid_finish

  have hA2_between : between A1 A2 C := by
    euclid_finish

  have hB1_between : between C B1 B2 := by
    euclid_finish

  have hB2_between : between B1 B2 A := by
    euclid_finish

  have hC1_between : between A C1 C2 := by
    euclid_finish

  have hC2_between : between C1 C2 B := by
    euclid_finish

  have hA1_on_BC : A1.onLine BC := by
    euclid_finish

  have hA2_on_BC : A2.onLine BC := by
    euclid_finish

  have hB1_on_CA : B1.onLine CA := by
    euclid_finish

  have hB2_on_CA : B2.onLine CA := by
    euclid_finish

  have hC1_on_AB : C1.onLine AB := by
    euclid_finish

  have hC2_on_AB : C2.onLine AB := by
    euclid_finish

  have hA1_on_l1 : A1.onLine lA1B2 := by
    euclid_finish

  have hB2_on_l1 : B2.onLine lA1B2 := by
    euclid_finish

  have hB1_on_l2 : B1.onLine lB1C2 := by
    euclid_finish

  have hC2_on_l2 : C2.onLine lB1C2 := by
    euclid_finish

  have hC1_on_l3 : C1.onLine lC1A2 := by
    euclid_finish

  have hA2_on_l3 : A2.onLine lC1A2 := by
    euclid_finish

  have hA1_ne_B2 : A1 ≠ B2 := by
    euclid_finish

  have hB1_ne_C2 : B1 ≠ C2 := by
    euclid_finish

  have hC1_ne_A2 : C1 ≠ A2 := by
    euclid_finish

  have hA_ne_B : A ≠ B := by
    euclid_finish

  have hB_ne_C : B ≠ C := by
    euclid_finish

  have hC_ne_A : C ≠ A := by
    euclid_finish

  have h_eq1 : |(A1─A2)| = |(B1─B2)| := by
    euclid_finish

  have h_eq2 : |(B1─B2)| = |(C1─C2)| := by
    euclid_finish

  have h_eq3 : |(A1─A2)| = |(C1─C2)| := by
    rw [h_eq1, h_eq2]

  have hA1A2_nonneg : |(A1─A2)| ≥ 0 := by
    euclid_finish

  have hB1B2_nonneg : |(B1─B2)| ≥ 0 := by
    euclid_finish

  have hC1C2_nonneg : |(C1─C2)| ≥ 0 := by
    euclid_finish

  have h_concurrent : Concurrent A1B2 B1C2 C1A2 := by
    have h_side_eq1 : |(A1─A2)| = |(B1─B2)| := by
      exact h_eq1
    have h_side_eq2 : |(B1─B2)| = |(C1─C2)| := by
      exact h_eq2
    have h_side_eq3 : |(A1─A2)| = |(C1─C2)| := by
      exact h_eq3
    have hline1 : A1.onLine lA1B2 := by
      exact hA1_on_l1
    have hline2 : B1.onLine lB1C2 := by
      exact hB1_on_l2
    have hline3 : C1.onLine lC1A2 := by
      exact hC1_on_l3
    euclid_finish

  exact h_concurrent
