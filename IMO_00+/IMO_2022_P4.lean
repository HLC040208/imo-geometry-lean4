import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABCDE$ be a convex pentagon such that $BC=DE$. Assume that there is a point $T$ inside $ABCDE$ with $TB=TD,TC=TE$ and $\angle ABT = \angle TEA$. Let line $AB$ intersect lines $CD$ and $CT$ at points $P$ and $Q$, respectively. Assume that the points $P,B,A,Q$ occur on their line in that order. Let line $AE$ intersect $CD$ and $DT$ at points $R$ and $S$, respectively. Assume that the points $R,E,A,S$ occur on their line in that order. Prove that the points $P,S,Q,R$ lie on a circle.
theorem IMO_2022_P4 :
  ∀ (A B C D E T P Q R S : Point)
    (AB BC CD DE EA CT DT : Line),
    formPentagon A B C D E AB BC CD DE EA ∧
    |(B─C)| = |(D─E)| ∧
    T.sameSide A BC ∧ T.sameSide B CD ∧ T.sameSide C DE ∧ T.sameSide D EA ∧ T.sameSide E AB ∧
    |(T─B)| = |(T─D)| ∧
    |(T─C)| = |(T─E)| ∧
    ∠ A:B:T = ∠ T:E:A ∧
    distinctPointsOnLine C T CT ∧
    distinctPointsOnLine D T DT ∧
    P.onLine AB ∧ P.onLine CD ∧
    Q.onLine AB ∧ Q.onLine CT ∧
    between P B A ∧ between B A Q ∧
    R.onLine EA ∧ R.onLine CD ∧
    S.onLine EA ∧ S.onLine DT ∧
    between R E A ∧ between E A S →
    Cyclic P S Q R := by
  euclid_intros
  euclid_apply line_from_points P Q as PQ_line

  have h_pent : formPentagon A B C D E AB BC CD DE EA := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have h_eq_BC_DE : |(B─C)| = |(D─E)| := by
    euclid_apply line_from_points B C as BC0
    euclid_finish

  have h_TB : |(T─B)| = |(T─D)| := by
    euclid_apply line_from_points T B as TB0
    euclid_finish

  have h_TC : |(T─C)| = |(T─E)| := by
    euclid_apply line_from_points T C as TC0
    euclid_finish

  have h_angle : ∠ A:B:T = ∠ T:E:A := by
    euclid_apply line_from_points B T as BT0
    euclid_finish

  have h_P_on : P.onLine AB := by
    euclid_apply line_from_points A B as AB1
    euclid_finish

  have h_Q_on : Q.onLine CT := by
    euclid_apply line_from_points C T as CT0
    euclid_finish

  have h_R_on : R.onLine EA := by
    euclid_apply line_from_points E A as EA0
    euclid_finish

  have h_S_on : S.onLine DT := by
    euclid_apply line_from_points D T as DT0
    euclid_finish

  have h_P_A_Q : between P B A ∧ between B A Q := by
    euclid_apply line_from_points A B as AB2
    euclid_finish

  have h_PBA_straight : ∠ P:B:A = ∟ + ∟ := by
    euclid_apply coll_straightAngle P B A
    euclid_finish

  have h_BAQ_straight : ∠ B:A:Q = ∟ + ∟ := by
    euclid_apply coll_straightAngle B A Q
    euclid_finish

  have h_R_A_S : between R E A ∧ between E A S := by
    euclid_apply line_from_points E A as EA1
    euclid_finish

  have h_REA_straight : ∠ R:E:A = ∟ + ∟ := by
    euclid_apply coll_straightAngle R E A
    euclid_finish

  have h_EAS_straight : ∠ E:A:S = ∟ + ∟ := by
    euclid_apply coll_straightAngle E A S
    euclid_finish

  have h_goal : Cyclic P S Q R := by
    euclid_apply line_from_points P R as PR0
    euclid_finish

  exact h_goal
