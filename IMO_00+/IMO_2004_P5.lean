import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--In a convex quadrilateral $ABCD$, the diagonal $BD$ bisects neither the angle $ABC$ nor the angle $CDA$. The point $P$ lies inside $ABCD$ and satisfies\[\angle PBC=\angle DBA\quad \text{and}\quad \angle PDC=\angle BDA.\]Prove that $ABCD$ is a Cyclic quadrilateral if and only if $AP=CP$.
theorem IMO_2004_P5 :
  ∀ (A B C D P : Point) (AB BC CD DA BD : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    ¬ (∠ A:B:D = ∠ D:B:C) ∧
    ¬ (∠ C:D:B = ∠ B:D:A) ∧
    InsideQuadrilateral P A B C D AB BC CD DA ∧
    ∠ P:B:C = ∠ D:B:A ∧
    ∠ P:D:C = ∠ B:D:A →
    (Cyclic A B C D ↔ |(A─P)| = |(C─P)|) := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A P as AP
  euclid_apply line_from_points C P as CP
  euclid_apply line_from_points B P as BP
  euclid_apply line_from_points D P as DP
  euclid_apply line_from_points B D as BD_line

  have h_quad : formQuadrilateral A B C D AB BC CD DA := by
    euclid_finish

  have h_inside : InsideQuadrilateral P A B C D AB BC CD DA := by
    euclid_finish

  have h_angle_B : ∠ P:B:C = ∠ D:B:A := by
    euclid_finish

  have h_angle_D : ∠ P:D:C = ∠ B:D:A := by
    euclid_finish

  have h_not_bis_B : ¬ (∠ A:B:D = ∠ D:B:C) := by
    euclid_finish

  have h_not_bis_D : ¬ (∠ C:D:B = ∠ B:D:A) := by
    euclid_finish

  have hP_on_AP : P.onLine AP := by
    euclid_finish

  have hA_on_AP : A.onLine AP := by
    euclid_finish

  have hP_on_CP : P.onLine CP := by
    euclid_finish

  have hC_on_CP : C.onLine CP := by
    euclid_finish

  have hP_on_BP : P.onLine BP := by
    euclid_finish

  have hB_on_BP : B.onLine BP := by
    euclid_finish

  have hP_on_DP : P.onLine DP := by
    euclid_finish

  have hD_on_DP : D.onLine DP := by
    euclid_finish

  have hB_on_BD : B.onLine BD_line := by
    euclid_finish

  have hD_on_BD : D.onLine BD_line := by
    euclid_finish

  have hA_ne_B : A ≠ B := by
    euclid_finish

  have hB_ne_C : B ≠ C := by
    euclid_finish

  have hC_ne_D : C ≠ D := by
    euclid_finish

  have hD_ne_A : D ≠ A := by
    euclid_finish

  constructor
  · intro h_cyclic
    have h_quad_cyclic : Cyclic A B C D := by
      exact h_cyclic
    have hPB_angle : ∠ P:B:C = ∠ D:B:A := by
      exact h_angle_B
    have hPD_angle : ∠ P:D:C = ∠ B:D:A := by
      exact h_angle_D
    have h_eq : |(A─P)| = |(C─P)| := by
      euclid_finish
    exact h_eq
  · intro h_eq
    have hdist : |(A─P)| = |(C─P)| := by
      exact h_eq
    have hPB_angle : ∠ P:B:C = ∠ D:B:A := by
      exact h_angle_B
    have hPD_angle : ∠ P:D:C = ∠ B:D:A := by
      exact h_angle_D
    have h_cyclic : Cyclic A B C D := by
      euclid_finish
    exact h_cyclic
