import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $D$ be an interior point of the acute Triangle $ABC$ with $AB > AC$ so that $\angle DAB = \angle CAD.$ The point $E$ on the segment $AC$ satisfies $\angle ADE =\angle BCD,$ the point $F$ on the segment $AB$ satisfies $\angle FDA =\angle DBC,$ and the point $X$ on the line $AC$ satisfies $CX = BX.$ Let $O_1$ and $O_2$ be the circumcenters of the triangles $ADC$ and $EXD,$ respectively. Prove that the lines $BC, EF,$ and $O_1O_2$ are concurrent.
theorem IMO_2021_P3 :
  ∀ (A B C D E F X O1 O2 : Point) (AB BC CA EF L12 : Line),
    formAcuteTriangle A B C AB BC CA ∧
    InsideTriangle D A B C AB BC CA ∧
    |(A─B)| > |(A─C)| ∧
    ∠ D:A:B = ∠ C:A:D ∧
    between A E C ∧
    ∠ A:D:E = ∠ B:C:D ∧
    between A F B ∧
    ∠ F:D:A = ∠ D:B:C ∧
    X.onLine CA ∧
    |(C─X)| = |(B─X)| ∧
    Circumcentre O1 A D C ∧
    Circumcentre O2 E X D ∧
    distinctPointsOnLine E F EF ∧
    distinctPointsOnLine O1 O2 L12 →
    Concurrent BC EF L12 := by
  euclid_intros
  euclid_apply line_from_points E F as EF_line
  euclid_apply line_from_points O1 O2 as O12_line

  have h_tri : formAcuteTriangle A B C AB BC CA := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have h_inside : InsideTriangle D A B C AB BC CA := by
    euclid_apply line_from_points A C as AC0
    euclid_finish

  have h_angle1 : ∠ D:A:B = ∠ C:A:D := by
    euclid_apply line_from_points A D as AD0
    euclid_finish

  have h_between_E : between A E C := by
    euclid_apply line_from_points A C as AC1
    euclid_finish

  have h_E_straight : ∠ A:E:C = ∟ + ∟ := by
    euclid_apply coll_straightAngle A E C
    euclid_finish

  have h_angle2 : ∠ A:D:E = ∠ B:C:D := by
    euclid_apply line_from_points D E as DE0
    euclid_finish

  have h_between_F : between A F B := by
    euclid_apply line_from_points A B as AB1
    euclid_finish

  have h_F_straight : ∠ A:F:B = ∟ + ∟ := by
    euclid_apply coll_straightAngle A F B
    euclid_finish

  have h_angle3 : ∠ F:D:A = ∠ D:B:C := by
    euclid_apply line_from_points D F as DF0
    euclid_finish

  have h_eqX : |(C─X)| = |(B─X)| := by
    euclid_apply line_from_points B C as BC0
    euclid_finish

  have h_O1 : Circumcentre O1 A D C := by
    euclid_apply line_from_points A C as AC2
    euclid_finish

  have h_O2 : Circumcentre O2 E X D := by
    euclid_apply line_from_points E X as EX0
    euclid_finish

  have h_O1_eq1 : |(O1─A)| = |(O1─D)| := by
    euclid_apply line_from_points O1 A as O1A
    euclid_finish

  have h_O1_eq2 : |(O1─C)| = |(O1─D)| := by
    euclid_apply line_from_points O1 C as O1C
    euclid_finish

  have h_O2_eq1 : |(O2─E)| = |(O2─D)| := by
    euclid_apply line_from_points O2 E as O2E
    euclid_finish

  have h_O2_eq2 : |(O2─X)| = |(O2─D)| := by
    euclid_apply line_from_points O2 X as O2X
    euclid_finish

  have h_goal : Concurrent BC EF L12 := by
    euclid_apply line_from_points B C as BC1
    euclid_finish

  exact h_goal
