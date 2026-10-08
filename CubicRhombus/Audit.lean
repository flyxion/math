import CubicRhombus.Gram
import CubicRhombus.Theorems
import CubicRhombus.Expansion
import CubicRhombus.Geometry
import CubicRhombus.Rank
import CubicRhombus.Plane
import CubicRhombus.Infinite
import CubicRhombus.Uniqueness
import CubicRhombus.Corners
import CubicRhombus.Operator
import CubicRhombus.CubeAut
import CubicRhombus.Isometry

/-! Axiom audit.  Every theorem listed here should depend only on `propext`,
`Classical.choice` and `Quot.sound`.  Any `sorryAx` in the output means the proof is incomplete. -/

#print axioms CubicRhombus.det_gram
#print axioms CubicRhombus.facet_gram
#print axioms CubicRhombus.hasDerivAt_vol2
#print axioms CubicRhombus.vol2_le_one
#print axioms CubicRhombus.vol2_eq_one_iff
#print axioms CubicRhombus.deriv_vol2_eq_zero_iff
#print axioms CubicRhombus.vol2_two_fibres
#print axioms CubicRhombus.quadForm_gram
#print axioms CubicRhombus.posdef_iff
#print axioms CubicRhombus.tendsto_vol2
#print axioms CubicRhombus.vertex_lemma
#print axioms CubicRhombus.log_vol2_expansion
#print axioms CubicRhombus.log_vol2_isBigO
#print axioms CubicRhombus.volume_sq_eq_det
#print axioms CubicRhombus.posSemidef_gram
#print axioms CubicRhombus.exists_system
#print axioms CubicRhombus.volume_sq_rhombus
#print axioms CubicRhombus.volume_rhombus_le_one
#print axioms CubicRhombus.principal_gram
#print axioms CubicRhombus.rank_gram_of_det_ne
#print axioms CubicRhombus.rank_interior
#print axioms CubicRhombus.rank_upper
#print axioms CubicRhombus.rank_lower
#print axioms CubicRhombus.ipGram_flip2
#print axioms CubicRhombus.parallelepiped_flip2
#print axioms CubicRhombus.flipGram_two
#print axioms CubicRhombus.flipGram_not_member
#print axioms CubicRhombus.tendsto_vol2_zero
#print axioms CubicRhombus.limit_volume_eq_one
#print axioms CubicRhombus.limit_volume_not_injective
#print axioms CubicRhombus.quadratic_coeff_diverges
#print axioms CubicRhombus.inner_sum_system
#print axioms CubicRhombus.system_linearIndependent
#print axioms CubicRhombus.system_not_finite_dim
#print axioms CubicRhombus.ip_single
#print axioms CubicRhombus.sysVec_isSystem
#print axioms CubicRhombus.gram_form_unbounded
#print axioms CubicRhombus.exists_isometry_of_ipGram_eq
#print axioms CubicRhombus.finrank_span_eq_rank_ipGram
#print axioms CubicRhombus.rhombus_unique
#print axioms CubicRhombus.span_dim_interior
#print axioms CubicRhombus.span_dim_upper
#print axioms CubicRhombus.span_dim_lower
#print axioms CubicRhombus.cornerSet_eq_iff
#print axioms CubicRhombus.cornerSet_two_neg
#print axioms CubicRhombus.cornerSet_two_not_determined
#print axioms CubicRhombus.gramCol_not_mem_l2
#print axioms CubicRhombus.no_gram_operator
#print axioms CubicRhombus.gram_operator_zero
#print axioms CubicRhombus.cube_affine
#print axioms CubicRhombus.affine_image_extremePoints
#print axioms CubicRhombus.extremePoints_parallelepiped
#print axioms CubicRhombus.edge_to_signed_edge
#print axioms CubicRhombus.linIndep_of_ipGram
#print axioms CubicRhombus.congruent_rhombi_param_eq
#print axioms CubicRhombus.congruent_two_neg
