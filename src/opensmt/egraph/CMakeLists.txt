add_library(opensmt_egraph EgraphSolver.C EgraphStore.C EgraphExplain.C EgraphDTC.C EgraphDebug.C Enode.C SigTab.C)
target_link_libraries(opensmt_egraph util)
