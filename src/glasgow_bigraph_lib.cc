#include "glasgow_bigraph_lib.hh"

#include <gss/homomorphism.hh>
#include <gss/formats/input_graph.hh>

#include <chrono>
#include <cstdlib>
#include <string>
#include <ctime>
#include <exception>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <memory>
#include <vector>
#include <regex>

#include <unistd.h>

using std::boolalpha;
using std::cerr;
using std::cout;
using std::endl;
using std::exception;
using std::function;
using std::ifstream;
using std::localtime;
using std::make_pair;
using std::make_shared;
using std::make_unique;
using std::put_time;
using std::string;
using std::vector;

using std::chrono::duration_cast;
using std::chrono::milliseconds;
using std::chrono::operator""s;
using std::chrono::seconds;
using std::chrono::steady_clock;
using std::chrono::system_clock;

using gss::VertexToVertexMapping;

// Global variables to maintain results/graphs, cleared as required
static Results res;
static bool isPat = true;
static std::unique_ptr<InputGraph> patG;
static std::unique_ptr<InputGraph> tarG;

// Compile regex ahead of time (and globally accessible) for performance
const std::regex linkOpen { R"(:OPX:.*:(\d+):.*)" };
const std::regex linkClosed { R"(:CLX:(\d+):.*)" };

VertexToVertexMapping gbs_nextsol() {
    if (res.mapping.empty() || res.mapping.size() <= res.next) {
        return {};
    }


    auto r = res.mapping[res.next];
    res.next++;
    return r;
}

std::map<int, int> gbs_getEdges(const VertexToVertexMapping & mapping) {
    std::map<int, int> res;
    for (auto v : mapping) {
        if(patG->vertex_name(v.first).find("C_LINK") != string::npos) {
            int k = std::stoi(patG->vertex_name(v.first).substr(7));
            int val = std::stoi(tarG->vertex_name(v.second).substr(7));
            res[k] = val;
        }
    }
    return res;
}


std::map<int, int> gbs_getNodes(const VertexToVertexMapping & mapping) {
    std::map<int, int> res;
    for (auto v : mapping) {
        if(patG->vertex_name(v.first).find("C_LINK") == string::npos
           && patG->vertex_label(v.first) != "LINK") {
            int k = std::stoi(patG->vertex_name(v.first));
            int val = std::stoi(tarG->vertex_name(v.second));
            res[k] = val;
        }
    }
    return res;
}

std::vector<std::pair<int,int>> gbs_getHyp(const VertexToVertexMapping & mapping) {
    std::vector<std::pair<int, int>> res;

    std::smatch match;
    for (auto v : mapping) {
        if(patG->vertex_label(v.first) == "LINK") {
            std::string str = patG->vertex_name(v.first);
            if (regex_match(str, match, linkOpen)) {
                int l1 = stoi(match.str(1));

                str = tarG->vertex_name(v.second);
                if (regex_match(str, match, linkOpen)) {
                    int l2 = stoi(match.str(1));
                    res.emplace_back(std::make_pair(l1,l2));
                } else if (regex_match(str, match, linkClosed)) {
                    int l2 = stoi(match.str(1));
                    res.emplace_back(std::make_pair(l1,l2));
                }
            }
        }
    }
    return res;
}

// Assumes target/pattern setup before calling
void gbs_match_one() {
    res.clear();

    if (tarG->size() == 0 || patG->size() == 0) {
        std::cerr << "Target or Pattern not available in match\n";
    }

    gss::HomomorphismParams params;
    params.injectivity = gss::Injectivity::Injective;
    params.induced = false;
    params.bigraph = true;
    params.count_solutions = false;
    params.no_supplementals = true;

    /* Prepare and start timeout */
    params.restarts_schedule = make_unique<gss::LubyRestartsSchedule>(gss::LubyRestartsSchedule::default_multiplier);
    params.timeout = make_shared<gss::Timeout>(0s);

    auto result = gss::solve_homomorphism_problem(*patG, *tarG, params);

    if(!result.mapping.empty() && params.bigraph) {
        res.mapping.push_back(result.mapping);
    }
}

void gbs_match_all() {
    res.clear();

    if (tarG->size() == 0 || patG->size() == 0) {
        std::cerr << "Target or Pattern not available in match\n";
    }

    gss::HomomorphismParams params;
    params.injectivity = gss::Injectivity::Injective;
    params.induced = false;
    params.bigraph = true;
    params.count_solutions = true;
    params.no_supplementals = true;

    /* Prepare and start timeout */
    params.restarts_schedule = make_unique<gss::NoRestartsSchedule>();
    params.timeout = make_shared<gss::Timeout>(0s);

    // Return true to keep going after this solution
    params.enumerate_callback =
        [&](auto m) { res.mapping.push_back(m); return true; };

    auto result = gss::solve_homomorphism_problem(*patG, *tarG, params);
}

int gbs_count_sols() {
    res.clear();

    gss::HomomorphismParams params;
    params.injectivity = gss::Injectivity::Injective;
    params.induced = false;
    params.bigraph = true;
    params.count_solutions = true;
    params.no_supplementals = true;

    /* Prepare and start timeout */
    params.restarts_schedule = make_unique<gss::NoRestartsSchedule>();
    params.timeout = make_shared<gss::Timeout>(0s);

    auto result = solve_homomorphism_problem(*patG, *tarG, params);

    return (int) result.solution_count;
}

auto gbs_equal() -> bool {
    res.clear();

    gss::HomomorphismParams params;
    params.injectivity = gss::Injectivity::Injective;
    params.induced = false;
    params.bigraph = true;
    params.bigraph_equality_check = true;
    params.count_solutions = false;
    params.no_supplementals = true;

    params.restarts_schedule = make_unique<gss::NoRestartsSchedule>();


    /* Prepare and start timeout */
    params.timeout = make_shared<gss::Timeout>(0s);

    auto result = gss::solve_homomorphism_problem(*patG, *tarG, params);

    return result.mapping.size() > 0;
}


void gbs_add_node(const int i, const char* lbl, const char* name,
                  const std::vector<int> indeg, const std::vector<int> outdeg) {
    auto &ig = isPat? patG : tarG;
    ig->set_vertex_label(i, lbl);
    ig->set_vertex_name(i, name);

    if (indeg.size() > 0) {
        ig->set_child_of_root(i);
        for (const auto & j : indeg) {
            ig->add_pattern_root_edge(j, i);
        }
    }
    if (outdeg.size() > 0) {
        ig->set_parent_of_site(i);
        for (const auto & j : outdeg) {
            ig->add_pattern_site_edge(i, j);
        }
    }
}

void gbs_add_edge(const int i, const int j) {
    auto &ig = isPat? patG : tarG;
    ig->add_directed_edge(i,j,"dir");
}

void gbs_start_pattern(int size) {
    isPat = true;
    patG = make_unique<InputGraph>(InputGraph(size, true, true));
}

void gbs_start_target(int size) {
    isPat = false;
    tarG = make_unique<InputGraph>(InputGraph(size, true, true));
}
