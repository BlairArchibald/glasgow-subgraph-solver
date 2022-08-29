#ifndef GLASGOW_BIGRAPH_LIB_H_
#define GLASGOW_BIGRAPH_LIB_H_

#include <vector>
#include <map>
#include "homomorphism.hh"

class Results {
    public:
        std::vector<VertexToVertexMapping> mapping;
        unsigned next = 0;
        int count = 0;

        Results () {
            mapping.clear();
        };

        void clear () { mapping.clear(); next = 0; }
        bool match_found () { return !mapping.empty(); }
};

#ifdef __cplusplus
extern "C" {
#endif


// Simple interface for now, using the strings. Later we will read/write directly
void gbs_match_all(InputGraph pat, InputGraph tar);
void gbs_match_one(InputGraph pat, InputGraph tar);
int gbs_count_sols(InputGraph pat, InputGraph tar);
bool gbs_equal(InputGraph pat, InputGraph tar);

VertexToVertexMapping gbs_nextsol();
std::map<int, int> gbs_getEdges(const VertexToVertexMapping & mapping);
std::map<int, int> gbs_getNodes(const VertexToVertexMapping & mapping);
std::vector<std::pair<int, int>> gbs_getHyp(const VertexToVertexMapping & mapping);

#ifdef __cplusplus
}
#endif

#endif // GLASGOW_BIGRAPH_LIB_H_
