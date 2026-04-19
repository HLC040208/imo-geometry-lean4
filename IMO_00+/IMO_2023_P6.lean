import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

set_option maxHeartbeats 0

--Let $ABC$ be an equilateral triangle. Let $A_1,B_1,C_1$ be interior points of $ABC$ such that $BA_1=A_1C$, $CB_1=B_1A$, $AC_1=C_1B$, and \[\angle BA_1C+\angle CB_1A+\angle AC_1B=480^\circ\]Let $BC_1$ and $CB_1$ meet at $A_2,$ let $CA_1$ and $AC_1$ meet at $B_2,$ and let $AB_1$ and $BA_1$ meet at $C_2$. Prove that if Triangle $A_1B_1C_1$ is scalene, then the three circumcircles of triangles $AA_1A_2, BB_1B_2$ and $CC_1C_2$ all pass through two common points. (Note: a scalene Triangle is one where no two sides have equal length.)
theorem IMO_2023_P6 :
  ∀ (A B C A1 B1 C1 A2 B2 C2 : Point)
    (AB BC CA l1 l2 l3 l4 l5 l6 : Line),
    formTriangle A B C AB BC CA ∧
    |(A─B)| = |(B─C)| ∧ |(B─C)| = |(C─A)| ∧
    InsideTriangle A1 A B C AB BC CA ∧
    InsideTriangle B1 A B C AB BC CA ∧
    InsideTriangle C1 A B C AB BC CA ∧
    |(B─A1)| = |(A1─C)| ∧
    |(C─B1)| = |(B1─A)| ∧
    |(A─C1)| = |(C1─B)| ∧
    ∠ B:A1:C + ∠ C:B1:A + ∠ A:C1:B = (16/3) * ∟ ∧
    distinctPointsOnLine B C1 l1 ∧ distinctPointsOnLine C B1 l2 ∧
    A2.onLine l1 ∧ A2.onLine l2 ∧
    distinctPointsOnLine C A1 l3 ∧ distinctPointsOnLine A C1 l4 ∧
    B2.onLine l3 ∧ B2.onLine l4 ∧
    distinctPointsOnLine A B1 l5 ∧ distinctPointsOnLine B A1 l6 ∧
    C2.onLine l5 ∧ C2.onLine l6 ∧
    |(A1─B1)| ≠ |(B1─C1)| ∧ |(B1─C1)| ≠ |(C1─A1)| ∧ |(C1─A1)| ≠ |(A1─B1)| →
  ∃ (Ω1 Ω2 Ω3 : Circle) (X Y : Point),
    Circumcircle Ω1 A A1 A2 ∧ Circumcircle Ω2 B B1 B2 ∧ Circumcircle Ω3 C C1 C2 ∧
    X.onCircle Ω1 ∧ X.onCircle Ω2 ∧ X.onCircle Ω3 ∧
    Y.onCircle Ω1 ∧ Y.onCircle Ω2 ∧ Y.onCircle Ω3 ∧
    X ≠ Y := by
  intro A B C A1 B1 C1 A2 B2 C2 AB BC CA l1 l2 l3 l4 l5 l6 h
  rcases h with
    ⟨h_tri, h_AB_eq_BC, h_BC_eq_CA,
      h_A1_inside, h_B1_inside, h_C1_inside,
      h_BA1_eq_A1C, h_CB1_eq_B1A, h_AC1_eq_C1B,
      h_angle_sum,
      h_l1, h_l2, h_A2_on_l1, h_A2_on_l2,
      h_l3, h_l4, h_B2_on_l3, h_B2_on_l4,
      h_l5, h_l6, h_C2_on_l5, h_C2_on_l6,
      h_scalene1, h_scalene2, h_scalene3⟩
  euclid_apply rightAngle_eq_pi_div_two

  have h_tri_A : Triangle A A1 A2 := by
    euclid_finish

  have h_tri_B : Triangle B B1 B2 := by
    euclid_finish

  have h_tri_C : Triangle C C1 C2 := by
    euclid_finish

  rcases threePoints_existCircle A A1 A2 h_tri_A with ⟨Ω1, hA_on_Ω1, hA1_on_Ω1, hA2_on_Ω1⟩
  rcases threePoints_existCircle B B1 B2 h_tri_B with ⟨Ω2, hB_on_Ω2, hB1_on_Ω2, hB2_on_Ω2⟩
  rcases threePoints_existCircle C C1 C2 h_tri_C with ⟨Ω3, hC_on_Ω3, hC1_on_Ω3, hC2_on_Ω3⟩

  have hΩ1 : Circumcircle Ω1 A A1 A2 := by
    exact ⟨hA_on_Ω1, hA1_on_Ω1, hA2_on_Ω1⟩

  have hΩ2 : Circumcircle Ω2 B B1 B2 := by
    exact ⟨hB_on_Ω2, hB1_on_Ω2, hB2_on_Ω2⟩

  have hΩ3 : Circumcircle Ω3 C C1 C2 := by
    exact ⟨hC_on_Ω3, hC1_on_Ω3, hC2_on_Ω3⟩

  have h_common :
      ∃ X Y : Point,
        X.onCircle Ω1 ∧ X.onCircle Ω2 ∧ X.onCircle Ω3 ∧
        Y.onCircle Ω1 ∧ Y.onCircle Ω2 ∧ Y.onCircle Ω3 ∧
        X ≠ Y := by
    have h_tri' : formTriangle A B C AB BC CA := by
      exact h_tri
    have hΩ1' : Circumcircle Ω1 A A1 A2 := by
      exact hΩ1
    have hΩ2' : Circumcircle Ω2 B B1 B2 := by
      exact hΩ2
    have hΩ3' : Circumcircle Ω3 C C1 C2 := by
      exact hΩ3
    euclid_finish

  rcases h_common with ⟨X, Y, hX1, hX2, hX3, hY1, hY2, hY3, hXY⟩
  exact ⟨Ω1, Ω2, Ω3, X, Y, hΩ1, hΩ2, hΩ3, hX1, hX2, hX3, hY1, hY2, hY3, hXY⟩
