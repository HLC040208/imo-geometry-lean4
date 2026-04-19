import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Triangle $BCF$ has a right angle at $B$. Let $A$ be the point on line $CF$ such that $FA=FB$ and $F$ lies between $A$ and $C$. Point $D$ is chosen so that $DA=DC$ and $AC$ is the bisector of $\angle{DAB}$. Point $E$ is chosen so that $EA=ED$ and $AD$ is the bisector of $\angle{EAC}$. Let $M$ be the MidPoint of $CF$. Let $X$ be the point such that $AMXE$ is a parallelogram. Prove that $BD,FX$ and $ME$ are concurrent.
theorem IMO_2016_P1 :
  ∀ (B C F A D E M X : Point)
    (BC CF FB AM MX XE EA BD FX ME : Line),
    formTriangle B C F BC CF FB ∧
    ∠ C:B:F = ∟ ∧
    between A F C ∧ |(F─A)| = |(F─B)| ∧
    |(D─A)| = |(D─C)| ∧ ∠ D:A:C = ∠ C:A:B ∧
    |(E─A)| = |(E─D)| ∧ ∠ E:A:D = ∠ D:A:C ∧
    between C M F ∧ |(C─M)| = |(M─F)| ∧
    Parallelogram A M X E AM MX XE EA →
    Concurrent BD FX ME := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points B C as BC_line
  euclid_apply line_from_points C F as CF_line
  euclid_apply line_from_points A F as AF
  euclid_apply line_from_points B D as BD_line
  euclid_apply line_from_points F X as FX_line
  euclid_apply line_from_points M E as ME_line

  have h_tri : formTriangle B C F BC CF FB := by
    euclid_apply line_from_points B C as BC0
    euclid_finish

  have h_right : ∠ C:B:F = ∟ := by
    euclid_apply rightAngle_eq_pi_div_two
    euclid_finish

  have h_between_AFC : between A F C := by
    euclid_apply line_from_points C F as CF0
    euclid_finish

  have h_FA_eq_FB : |(F─A)| = |(F─B)| := by
    euclid_apply line_from_points F A as FA0
    euclid_finish

  have h_DA_eq_DC : |(D─A)| = |(D─C)| := by
    euclid_apply line_from_points D A as DA0
    euclid_finish

  have h_angle_DAC : ∠ D:A:C = ∠ C:A:B := by
    euclid_apply line_from_points A C as AC0
    euclid_finish

  have h_EA_eq_ED : |(E─A)| = |(E─D)| := by
    euclid_apply line_from_points E A as EA0
    euclid_finish

  have h_angle_EAD : ∠ E:A:D = ∠ D:A:C := by
    euclid_apply line_from_points A D as AD0
    euclid_finish

  have h_mid_M : between C M F ∧ |(C─M)| = |(M─F)| := by
    euclid_apply line_from_points C F as CF1
    euclid_finish

  have h_para : Parallelogram A M X E AM MX XE EA := by
    euclid_apply line_from_points A M as AM0
    euclid_finish

  have h_conc : Concurrent BD FX ME := by
    euclid_apply line_from_points B D as BD0
    euclid_finish

  exact h_conc
