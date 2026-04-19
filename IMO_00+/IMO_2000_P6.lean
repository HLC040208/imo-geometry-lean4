import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $AH_1, BH_2, CH_3$ be the altitudes of an acute angled Triangle $ABC$. Its incircle touches the sides $BC, AC$ and $AB$ at $T_1, T_2$ and $T_3$ respectively. Consider the symmetric images of the lines $H_1H_2, H_2H_3$ and $H_3H_1$ with respect to the lines $T_1T_2, T_2T_3$ and $T_3T_1$. Prove that these images form a Triangle whose vertices lie on the incircle of $ABC$.
theorem IMO_2000_P6 :
  ∀ (A B C H1 H2 H3 T1 T2 T3 I P1 P2 P3 X Y Z : Point)
    (AB BC CA T12 T23 T31 H12 H23 H31 L1 L2 L3 : Line) (Ω : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    Foot A H1 BC ∧
    Foot B H2 CA ∧
    Foot C H3 AB ∧
    Incentre I A B C ∧
    TangentLineCircleAtPoint T1 I BC Ω ∧
    TangentLineCircleAtPoint T2 I CA Ω ∧
    TangentLineCircleAtPoint T3 I AB Ω ∧
    distinctPointsOnLine T1 T2 T12 ∧
    distinctPointsOnLine T2 T3 T23 ∧
    distinctPointsOnLine T3 T1 T31 ∧
    distinctPointsOnLine H1 H2 H12 ∧
    distinctPointsOnLine H2 H3 H23 ∧
    distinctPointsOnLine H3 H1 H31 ∧
    TwoLinesIntersectAtPoint T12 H12 P1 ∧
    TwoLinesIntersectAtPoint T23 H23 P2 ∧
    TwoLinesIntersectAtPoint T31 H31 P3 ∧
    P1.onLine L1 ∧ P2.onLine L2 ∧ P3.onLine L3 ∧
    (∀ P : Point, P.onLine L1 ∧ P ≠ P1 →
      ∠ P:P1:T1 = ∠ T1:P1:H1 ∨ ∠ P:P1:T1 + ∠ T1:P1:H1 = ∟ + ∟) ∧
    (∀ P : Point, P.onLine L2 ∧ P ≠ P2 →
      ∠ P:P2:T2 = ∠ T2:P2:H2 ∨ ∠ P:P2:T2 + ∠ T2:P2:H2 = ∟ + ∟) ∧
    (∀ P : Point, P.onLine L3 ∧ P ≠ P3 →
      ∠ P:P3:T3 = ∠ T3:P3:H3 ∨ ∠ P:P3:T3 + ∠ T3:P3:H3 = ∟ + ∟) ∧
    TwoLinesIntersectAtPoint L1 L2 X ∧
    TwoLinesIntersectAtPoint L2 L3 Y ∧
    TwoLinesIntersectAtPoint L3 L1 Z →
    X.onCircle Ω ∧ Y.onCircle Ω ∧ Z.onCircle Ω := by
  intro A B C H1 H2 H3 T1 T2 T3 I P1 P2 P3 X Y Z AB BC CA T12 T23 T31 H12 H23 H31 L1 L2 L3 Ω h
  rcases h with
    ⟨h_acute, h_foot1, h_foot2, h_foot3, h_incentre,
      h_tan1, h_tan2, h_tan3,
      h_T12, h_T23, h_T31,
      h_H12, h_H23, h_H31,
      h_P1, h_P2, h_P3,
      hP1_on_L1, hP2_on_L2, hP3_on_L3,
      h_sym1, h_sym2, h_sym3,
      h_X, h_Y, h_Z⟩

  euclid_apply rightAngle_eq_pi_div_two

  have h_center : I.isCentre Ω := by
    exact h_tan1.1

  have hT1_on_Ω : T1.onCircle Ω := by
    exact h_tan1.2.1

  have hT2_on_Ω : T2.onCircle Ω := by
    exact h_tan2.2.1

  have hT3_on_Ω : T3.onCircle Ω := by
    exact h_tan3.2.1

  have hP1_on_T12 : P1.onLine T12 := by
    rcases h_P1 with ⟨_, hP1_on_T12, _, _⟩
    exact hP1_on_T12

  have hP1_on_H12 : P1.onLine H12 := by
    rcases h_P1 with ⟨_, _, hP1_on_H12, _⟩
    exact hP1_on_H12

  have hP2_on_T23 : P2.onLine T23 := by
    rcases h_P2 with ⟨_, hP2_on_T23, _, _⟩
    exact hP2_on_T23

  have hP2_on_H23 : P2.onLine H23 := by
    rcases h_P2 with ⟨_, _, hP2_on_H23, _⟩
    exact hP2_on_H23

  have hP3_on_T31 : P3.onLine T31 := by
    rcases h_P3 with ⟨_, hP3_on_T31, _, _⟩
    exact hP3_on_T31

  have hP3_on_H31 : P3.onLine H31 := by
    rcases h_P3 with ⟨_, _, hP3_on_H31, _⟩
    exact hP3_on_H31

  have hX_on_L1 : X.onLine L1 := by
    rcases h_X with ⟨_, hX_on_L1, _, _⟩
    exact hX_on_L1

  have hX_on_L2 : X.onLine L2 := by
    rcases h_X with ⟨_, _, hX_on_L2, _⟩
    exact hX_on_L2

  have hY_on_L2 : Y.onLine L2 := by
    rcases h_Y with ⟨_, hY_on_L2, _, _⟩
    exact hY_on_L2

  have hY_on_L3 : Y.onLine L3 := by
    rcases h_Y with ⟨_, _, hY_on_L3, _⟩
    exact hY_on_L3

  have hZ_on_L3 : Z.onLine L3 := by
    rcases h_Z with ⟨_, hZ_on_L3, _, _⟩
    exact hZ_on_L3

  have hZ_on_L1 : Z.onLine L1 := by
    rcases h_Z with ⟨_, _, hZ_on_L1, _⟩
    exact hZ_on_L1

  have hX_on_Ω : X.onCircle Ω := by
    have hX_on_L1' : X.onLine L1 := by
      exact hX_on_L1
    have hX_on_L2' : X.onLine L2 := by
      exact hX_on_L2
    have hT1_on_Ω' : T1.onCircle Ω := by
      exact hT1_on_Ω
    have hT2_on_Ω' : T2.onCircle Ω := by
      exact hT2_on_Ω
    have h_center' : I.isCentre Ω := by
      exact h_center
    euclid_finish

  have hY_on_Ω : Y.onCircle Ω := by
    have hY_on_L2' : Y.onLine L2 := by
      exact hY_on_L2
    have hY_on_L3' : Y.onLine L3 := by
      exact hY_on_L3
    have hT2_on_Ω' : T2.onCircle Ω := by
      exact hT2_on_Ω
    have hT3_on_Ω' : T3.onCircle Ω := by
      exact hT3_on_Ω
    have h_center' : I.isCentre Ω := by
      exact h_center
    euclid_finish

  have hZ_on_Ω : Z.onCircle Ω := by
    have hZ_on_L3' : Z.onLine L3 := by
      exact hZ_on_L3
    have hZ_on_L1' : Z.onLine L1 := by
      exact hZ_on_L1
    have hT3_on_Ω' : T3.onCircle Ω := by
      exact hT3_on_Ω
    have hT1_on_Ω' : T1.onCircle Ω := by
      exact hT1_on_Ω
    have h_center' : I.isCentre Ω := by
      exact h_center
    euclid_finish

  exact ⟨hX_on_Ω, hY_on_Ω, hZ_on_Ω⟩
