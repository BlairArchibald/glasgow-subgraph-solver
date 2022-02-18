TARGET := glasgow_bigraph.so

SOURCES := \
    glasgow_bigraph_lib.cc \
    formats/bigraph.cc \
    formats/csv.cc \
    formats/dimacs.cc \
    formats/graph_file_error.cc \
    formats/input_graph.cc \
    formats/lad.cc \
    formats/read_file_format.cc \
    formats/vfmcs.cc \
    cheap_all_different.cc \
    clique.cc \
    common_subgraph.cc \
    configuration.cc \
    graph_traits.cc \
    homomorphism.cc \
    homomorphism_domain.cc \
    homomorphism_model.cc \
    homomorphism_searcher.cc \
    homomorphism_traits.cc \
    lackey.cc \
    proof.cc \
    restarts.cc \
    svo_bitset.cc \
    sip_decomposer.cc \
    symmetries.cc \
    thread_utils.cc \
    timeout.cc \
    verify.cc \
    watches.cc


TGT_LDFLAGS := -shared

ifeq ($(shell uname -s), Linux)
TGT_LDLIBS := -lpthread $(boost_ldlibs) -lstdc++fs
else
TGT_LDLIBS := $(boost_ldlibs)
endif
