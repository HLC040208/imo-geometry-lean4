import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--In Triangle $ABC$, point $A_1$ lies on side $BC$ and point $B_1$ lies on side $AC$. Let $P$ and $Q$ be points on segments $AA_1$ and $BB_1$, respectively, such that $PQ$ is parallel to $AB$. Let $P_1$ be a point on line $PB_1$, such that $B_1$ lies strictly between $P$ and $P_1$, and $\angle PP_1C=\angle BAC$. Similarly, let $Q_1$ be the point on line $QA_1$, such that $A_1$ lies strictly between $Q$ and $Q_1$, and $\angle CQ_1Q=\angle CBA$. Prove that points $P,Q,P_1$, and $Q_1$ are concyclic.
theorem IMO_2019_P2 :
  ∀ (A B C A1 B1 P Q P1 Q1 : Point)
    (AB BC CA AA1 BB1 PQ AB PB1 QA1 : Line),
    formTriangle A B C AB BC CA ∧
    distinctPointsOnLine A A1 AA1 ∧
    distinctPointsOnLine B B1 BB1 ∧
    between B A1 C ∧
    between A B1 C ∧
    between A P A1 ∧
    between B Q B1 ∧
    distinctPointsOnLine P Q PQ ∧
    ¬ AB.intersectsLine PQ ∧
    between P B1 P1 ∧
    between Q A1 Q1 ∧
    ∠ P:P1:C = ∠ B:A:C ∧
    ∠ C:Q1:Q = ∠ C:B:A →
    Cyclic P Q P1 Q1 := by
  euclid_intros
  have h_A1_straight : ∠ B:A1:C = ∟ + ∟ := by
    euclid_apply coll_straightAngle B A1 C
    euclid_finish

  have h_B1_straight : ∠ A:B1:C = ∟ + ∟ := by
    euclid_apply coll_straightAngle A B1 C
    euclid_finish

  have h_P_straight : ∠ A:P:A1 = ∟ + ∟ := by
    euclid_apply coll_straightAngle A P A1
    euclid_finish

  have h_P_zero : ∠ P:A:A1 = 0 := by
    euclid_apply coll_zeroAngle P A A1
    euclid_finish

  have h_Q_straight : ∠ B:Q:B1 = ∟ + ∟ := by
    euclid_apply coll_straightAngle B Q B1
    euclid_finish

  have h_Q_zero : ∠ Q:B:B1 = 0 := by
    euclid_apply coll_zeroAngle Q B B1
    euclid_finish

  have h_B1P1_straight : ∠ P:B1:P1 = ∟ + ∟ := by
    euclid_apply coll_straightAngle P B1 P1
    euclid_finish

  have h_A1Q1_straight : ∠ Q:A1:Q1 = ∟ + ∟ := by
    euclid_apply coll_straightAngle Q A1 Q1
    euclid_finish

  have h_angle_P1 : ∠ P:P1:C = ∠ B:A:C := by
    euclid_apply line_from_points P P1 as PP10
    euclid_finish

  have h_angle_Q1 : ∠ C:Q1:Q = ∠ C:B:A := by
    euclid_apply line_from_points Q Q1 as QQ10
    euclid_finish

  euclid_finish
