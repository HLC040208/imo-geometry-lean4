import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $ABCD$ be a fixed convex quadrilateral with $BC=DA$ and $BC$ not parallel with $DA$. Let two variable points $E$ and $F$ lie of the sides $BC$ and $DA$, respectively and satisfy $BE=DF$. The lines $AC$ and $BD$ meet at $P$, the lines $BD$ and $EF$ meet at $Q$, the lines $EF$ and $AC$ meet at $R$. Prove that the circumcircles of the triangles $PQR$, as $E$ and $F$ vary, have a common point other than $P$.
theorem IMO_2005_P5 :
  ∀ (A B C D P : Point)
    (AB BC CD DA AC BD : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(B─C)| = |(D─A)| ∧
    BC.intersectsLine DA ∧
    distinctPointsOnLine A C AC ∧
    distinctPointsOnLine B D BD ∧
    TwoLinesIntersectAtPoint AC BD P →
    ∃ X : Point, X ≠ P ∧ ∀ (E F P' Q R : Point) (EF : Line),
      between B E C ∧
      between A F D ∧
      |(B─E)| = |(D─F)| ∧
      distinctPointsOnLine E F EF ∧
      TwoLinesIntersectAtPoint BD EF Q ∧
      TwoLinesIntersectAtPoint EF AC R →
      Cyclic P Q R X := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A B as AB_line
  euclid_apply line_from_points C D as CD_line
  euclid_apply line_from_points A C as AC_line
  euclid_apply line_from_points B D as BD_line
  euclid_apply line_from_points P X as PX

  euclid_apply intersection_lines AB_line CD_line as X

  have h_quad : formQuadrilateral A B C D AB BC CD DA := by
    euclid_finish

  have h_eq_BC_DA : |(B─C)| = |(D─A)| := by
    euclid_finish

  have h_inter_BC_DA : BC.intersectsLine DA := by
    euclid_finish

  have hP_on_AC : P.onLine AC := by
    euclid_finish

  have hP_on_BD : P.onLine BD := by
    euclid_finish

  have hX_on_AB : X.onLine AB_line := by
    euclid_finish

  have hX_on_CD : X.onLine CD_line := by
    euclid_finish

  have hA_on_AB : A.onLine AB_line := by
    euclid_finish

  have hB_on_AB : B.onLine AB_line := by
    euclid_finish

  have hC_on_CD : C.onLine CD_line := by
    euclid_finish

  have hD_on_CD : D.onLine CD_line := by
    euclid_finish

  have hA_on_AC : A.onLine AC := by
    euclid_finish

  have hC_on_AC : C.onLine AC := by
    euclid_finish

  have hB_on_BD : B.onLine BD := by
    euclid_finish

  have hD_on_BD : D.onLine BD := by
    euclid_finish

  have hP_on_PX : P.onLine PX := by
    euclid_finish

  have hX_on_PX : X.onLine PX := by
    euclid_finish

  have hA_ne_C : A ≠ C := by
    euclid_finish

  have hB_ne_D : B ≠ D := by
    euclid_finish

  have hX_ne_P : X ≠ P := by
    euclid_finish

  use X
  constructor
  · exact hX_ne_P
  · intro E F P' Q R EF
    intro h_betweenE h_betweenF h_len h_EF hQ hR
    have hE_on_BC : E.onLine BC := by
      euclid_finish

    have hF_on_DA : F.onLine DA := by
      euclid_finish

    have h_between_BEC : between B E C := by
      exact h_betweenE

    have h_between_AFD : between A F D := by
      exact h_betweenF

    have hBE_eq_DF : |(B─E)| = |(D─F)| := by
      exact h_len

    have hE_on_EF : E.onLine EF := by
      euclid_finish

    have hF_on_EF : F.onLine EF := by
      euclid_finish

    have hQ_on_BD : Q.onLine BD := by
      euclid_finish

    have hQ_on_EF : Q.onLine EF := by
      euclid_finish

    have hR_on_AC : R.onLine AC := by
      euclid_finish

    have hR_on_EF : R.onLine EF := by
      euclid_finish

    have hE_ne_F : E ≠ F := by
      euclid_finish

    have hQ_ne_P : Q ≠ P := by
      euclid_finish

    have hR_ne_P : R ≠ P := by
      euclid_finish

    have hQ_on_BD_line : Q.onLine BD_line := by
      euclid_finish

    have hR_on_AC_line : R.onLine AC_line := by
      euclid_finish

    have hP_on_AC_line : P.onLine AC_line := by
      euclid_finish

    have hP_on_BD_line : P.onLine BD_line := by
      euclid_finish

    have h_cyclic : Cyclic P Q R X := by
      have hP_line1 : P.onLine AC := by
        exact hP_on_AC
      have hP_line2 : P.onLine BD := by
        exact hP_on_BD
      have hQ_line1 : Q.onLine BD := by
        exact hQ_on_BD
      have hQ_line2 : Q.onLine EF := by
        exact hQ_on_EF
      have hR_line1 : R.onLine AC := by
        exact hR_on_AC
      have hR_line2 : R.onLine EF := by
        exact hR_on_EF
      have hX_line1 : X.onLine AB_line := by
        exact hX_on_AB
      have hX_line2 : X.onLine CD_line := by
        exact hX_on_CD
      euclid_finish
    exact h_cyclic
