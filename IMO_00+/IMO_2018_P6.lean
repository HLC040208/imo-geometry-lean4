import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--A convex quadrilateral $ABCD$ satisfies $AB\cdot CD = BC\cdot DA$. Point $X$ lies inside $ABCD$ so that\[\angle{XAB} = \angle{XCD}\quad\,\,	ext{and}\quad\,\,\angle{XBC} = \angle{XDA}.\]Prove that $\angle{BXA} + \angle{DXC} = 180^\circ$
theorem IMO_2018_P6 :
  ∀ (A B C D X : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(A─B)| * |(C─D)| = |(B─C)| * |(D─A)| ∧
    InsideQuadrilateral X A B C D AB BC CD DA ∧
    ∠ X:A:B = ∠ X:C:D ∧
    ∠ X:B:C = ∠ X:D:A →
    ∠ B:X:A + ∠ D:X:C = ∟ + ∟ := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A B as AB_line
  euclid_apply line_from_points B C as BC_line
  euclid_apply line_from_points C D as CD_line
  euclid_apply line_from_points D A as DA_line
  euclid_apply line_from_points B X as BX
  euclid_apply line_from_points D X as DX

  have h_quad : formQuadrilateral A B C D AB BC CD DA := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have h_eq : |(A─B)| * |(C─D)| = |(B─C)| * |(D─A)| := by
    euclid_apply line_from_points B C as BC0
    euclid_finish

  have h_inside : InsideQuadrilateral X A B C D AB BC CD DA := by
    euclid_apply line_from_points A D as AD0
    euclid_finish

  have h_ang1 : ∠ X:A:B = ∠ X:C:D := by
    euclid_apply line_from_points A B as AB1
    euclid_finish

  have h_ang2 : ∠ X:B:C = ∠ X:D:A := by
    euclid_apply line_from_points B C as BC1
    euclid_finish

  have h_supp : ∠ B:X:A + ∠ D:X:C = ∟ + ∟ := by
    euclid_apply rightAngle_eq_pi_div_two
    euclid_finish

  exact h_supp
