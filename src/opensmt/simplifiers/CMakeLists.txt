add_library(opensmt_simplifiers TopLevelProp.C ExpandITEs.C BVBooleanize.C DLRescale.C BVNormalize.C Ackermanize.C ArraySimplify.C Purify.C)
target_link_libraries(opensmt_simplifiers util)
