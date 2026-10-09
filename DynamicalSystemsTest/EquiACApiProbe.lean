import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open Set MeasureTheory MeasurableSpace
open scoped ENNReal symmDiff BigOperators

#check IsSetSemiring.mem_supClosure_iff
#check Finpartition.sup_parts
#check Finpartition.supIndep
#check Finset.sup_id_set_eq_sUnion
#check measure_iUnion
#check measure_biUnion_finset
#check withDensity_apply
#check withDensity_absolutelyContinuous
#check isFiniteMeasure_withDensity
#check Measure.restrict_apply
#check Measure.restrict_restrict
#check unifIntegrable_iff
#check unifIntegrable_iff_norm
#check unifIntegrable_iff_of_measurable
#check eLpNorm_mono_measure
#check measure_toMeasurable
#check subset_toMeasurable
#check ENNReal.ofReal_div_of_pos
#check borel_eq_generateFrom_Ioc_le
#check Measure.AbsolutelyContinuous.mk
#check measure_inter_eq_left_of_ae
#check Measure.restrict_eq_self_of_ae_mem
#check Measure.restrict_apply_univ
#check Measure.restrict_compl_self
#check Measure.restrict_Icc_eq_restrict_Ioc
#check restrict_Icc_eq_restrict_Ioc
