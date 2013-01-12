EXTRA_DIST = reconf configure
AM_CPPFLAGS = -DFILIB_EXTENDED
SUBDIRS = libprim examples test @benchmark_subdir@

nobase_include_HEADERS = \
		fp_traits/fp_traits.hpp                                    fp_traits/fp_traits_double_x87_no_rounding.icc \
		fp_traits/fp_traits_base_double.icc                        fp_traits/fp_traits_double_x87_pred_succ_rounding.icc \
		fp_traits/fp_traits_base_float.icc                         fp_traits/fp_traits_float.hpp \
		fp_traits/fp_traits_double.hpp                             fp_traits/fp_traits_float_generic_multiplicative.icc \
		fp_traits/fp_traits_double_generic_multiplicative.icc      fp_traits/fp_traits_float_generic_native_directed.icc \
		fp_traits/fp_traits_double_generic_native_directed.icc     fp_traits/fp_traits_float_generic_native_switched.icc \
		fp_traits/fp_traits_double_generic_native_switched.icc     fp_traits/fp_traits_float_generic_no_rounding.icc \
		fp_traits/fp_traits_double_generic_no_rounding.icc         fp_traits/fp_traits_float_sse_multiplicative.icc \
		fp_traits/fp_traits_double_generic_pred_succ_rounding.icc  fp_traits/fp_traits_float_sse_native_directed.icc \
		fp_traits/fp_traits_double_sse_multiplicative.icc          fp_traits/fp_traits_float_sse_native_switched.icc \
		fp_traits/fp_traits_double_sse_native_directed.icc         fp_traits/fp_traits_float_sse_no_rounding.icc \
		fp_traits/fp_traits_double_sse_native_switched.icc         fp_traits/fp_traits_float_x87_multiplicative.icc \
		fp_traits/fp_traits_double_sse_no_rounding.icc             fp_traits/fp_traits_float_x87_native_directed.icc \
		fp_traits/fp_traits_double_sse_pred_succ_rounding.icc      fp_traits/fp_traits_float_x87_native_switched.icc \
		fp_traits/fp_traits_double_x87_multiplicative.icc          fp_traits/fp_traits_float_x87_no_rounding.icc \
		fp_traits/fp_traits_double_x87_native_directed.icc         fp_traits/fp_traits_sse_const.hpp \
		fp_traits/fp_traits_double_x87_native_switched.icc         fp_traits/fp_traits_x87_const.hpp \
		fp_traits/fp_traits_double_sse_native_onesided_global.icc \
		fp_traits/fp_traits_double_x87_native_onesided_global.icc \
		fp_traits/fp_traits_float_sse_native_onesided_global.icc \
		fp_traits/fp_traits_float_x87_native_onesided_global.icc \
		fp_traits/fp_traits_double_generic_native_onesided_global.icc \
		fp_traits/fp_traits_float_generic_native_onesided_global.icc \
		interval/stdfun/point/q_acos.icc interval/stdfun/point/q_acot.icc interval/stdfun/point/q_acsh.icc \
		interval/stdfun/point/q_acth.icc interval/stdfun/point/q_asin.icc interval/stdfun/point/q_asnh.icc \
		interval/stdfun/point/q_atan.icc interval/stdfun/point/q_atn1.icc interval/stdfun/point/q_atnh.icc \
		interval/stdfun/point/q_cos.icc interval/stdfun/point/q_cos1.icc interval/stdfun/point/q_cosh.icc \
		interval/stdfun/point/q_cot.icc interval/stdfun/point/q_coth.icc interval/stdfun/point/q_cth1.icc \
		interval/stdfun/point/q_ep1.icc interval/stdfun/point/q_epm1.icc interval/stdfun/point/q_errm.icc \
		interval/stdfun/point/q_ex10.icc interval/stdfun/point/q_exp.icc interval/stdfun/point/q_exp2.icc \
		interval/stdfun/point/q_expm.icc interval/stdfun/point/q_lg10.icc interval/stdfun/point/q_log.icc \
		interval/stdfun/point/q_log1.icc interval/stdfun/point/q_log2.icc interval/stdfun/point/q_rtrg.icc \
		interval/stdfun/point/q_sin.icc interval/stdfun/point/q_sin1.icc interval/stdfun/point/q_sinh.icc interval/stdfun/point/q_sqr.icc interval/stdfun/point/q_sqrt.icc interval/stdfun/point/q_tan.icc \
		interval/stdfun/point/q_tanh.icc interval/stdfun/interval/acos.icc \
		interval/stdfun/interval/acosh.icc interval/stdfun/interval//acot.icc interval/stdfun/interval/acoth.icc \
		interval/stdfun/interval/asin.icc interval/stdfun/interval/asinh.icc interval/stdfun/interval/atan.icc interval/stdfun/interval/atanh.icc interval/stdfun/interval/cos.icc \
		interval/stdfun/interval/cosh.icc interval/stdfun/interval/cot.icc interval/stdfun/interval/coth.icc interval/stdfun/interval/exp.icc interval/stdfun/interval/exp10.icc interval/stdfun/interval/exp2.icc \
		interval/stdfun/interval/expm1.icc interval/stdfun/interval/log.icc interval/stdfun/interval/log10.icc interval/stdfun/interval/log1p.icc interval/stdfun/interval/log2.icc \
		interval/stdfun/interval/pow.icc interval/stdfun/interval/sin.icc interval/stdfun/interval/sinh.icc interval/stdfun/interval/sqr.icc interval/stdfun/interval/sqrt.icc interval/stdfun/interval/tan.icc \
		interval/stdfun/interval/tanh.icc interval/stdfun/filib_tools.icc interval/stdfun/filib_consts.hpp interval/tools.icc \
		interval/interval.hpp interval/interval_fo.hpp interval/filib.hpp interval/interval_arith.icc interval/interval.icc ieee/primitive.hpp \
		rounding_control/rounding_control.hpp                     rounding_control/rounding_control_float.hpp \
		rounding_control/rounding_control_config.hpp              rounding_control/rounding_control_float_asmmsvci386.icc \
		rounding_control/rounding_control_double.hpp              rounding_control/rounding_control_float_asmsparc.icc \
		rounding_control/rounding_control_double_asmmsvci386.icc  rounding_control/rounding_control_float_iso9x.icc \
		rounding_control/rounding_control_double_asmsparc.icc     rounding_control/rounding_control_float_void.icc \
		rounding_control/rounding_control_double_iso9x.icc        rounding_control/rounding_control_stub.hpp \
		rounding_control/rounding_control_double_void.icc
