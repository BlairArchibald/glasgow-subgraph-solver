#ifndef GLASGOW_BIGRAPH_LIB_H_
#define GLASGOW_BIGRAPH_LIB_H_

#include <vector>
#include <map>
#include <gss/homomorphism.hh>

using gss::VertexToVertexMapping;

class Results {
    public:
        std::vector<VertexToVertexMapping> mapping;
        unsigned next = 0;
        int count = 0;

        Results () { mapping.clear(); };

        void clear () { mapping.clear(); next = 0; }
        bool match_found () { return !mapping.empty(); }
};

#ifdef __cplusplus
extern "C" {
#endif

void gbs_start_pattern(int size);
void gbs_start_target(int size);

void gbs_add_node(const int i, const char* lbl, const char* name,
                  const std::vector<int> indeg, const std::vector<int> outdeg);
void gbs_add_edge(const int i, const int j);

void gbs_match_one();
void gbs_match_all();
int gbs_count_sols();
bool gbs_equal();

VertexToVertexMapping gbs_nextsol();
std::map<int, int> gbs_getEdges(const VertexToVertexMapping & mapping);
std::map<int, int> gbs_getNodes(const VertexToVertexMapping & mapping);
std::vector<std::pair<int, int>> gbs_getHyp(const VertexToVertexMapping & mapping);

#ifdef __cplusplus
}
#endif

#endif // GLASGOW_BIGRAPH_LIB_H_
