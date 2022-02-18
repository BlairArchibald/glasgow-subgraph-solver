#include "glasgow_bigraph_lib.h"

#include "formats/bigraph.hh"
#include "homomorphism.hh"
#include "lackey.hh"
#include "symmetries.hh"
#include "proof.hh"
#include "restarts.hh"

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

// Global variables to maintain results/graphs, cleared as required
static Results res;
static InputGraph patG;
static InputGraph tarG;

auto printBigraphMappingBigraphER(const VertexToVertexMapping & mapping) -> std::string
{
    std::stringstream str;
    str << "S" << std::endl;
    for (auto v : mapping) {
        if(patG.vertex_name(v.first).find("C_LINK") != string::npos) {
            str << "E "
                 << patG.vertex_name(v.first).substr(7) << " "
                 << tarG.vertex_name(v.second).substr(7) << std::endl;
        }
        else if(patG.vertex_label(v.first) != "LINK") {
            str << "N "
                << patG.vertex_name(v.first) << " "
                << tarG.vertex_name(v.second) << std::endl;
        }
    }

    // Combine hyperedges for printing
    std::map<int, std::set<int>> hyper_edges;
    const std::regex linkL { R"(L(\d+)_.*)" };
    const std::regex linkAny { R"((L|C)(\d+)_.*)" };
    std::smatch match;

    for (auto v : mapping) {
        int l1, l2;
        if(patG.vertex_label(v.first) == "LINK") {
            std::string str = patG.vertex_name(v.first);
            if (regex_match(str, match, linkL)) {
                l1 = stoi(match.str(1));

                str = tarG.vertex_name(v.second);
                if (regex_match(str, match, linkAny)) {
                    l2 = stoi(match.str(2));
                    hyper_edges[l1].insert(l2);
                }
            }
        }
    }

    for (auto & s : hyper_edges) {
        str << "H " << s.first << " ";
        for (auto & i : s.second) {
              str << i << " ";
        }
        str << std::endl;
    }

    str << "D" << std::endl;
    return str.str();
}

auto doEqual(string pattern, string target) -> void {
    HomomorphismParams params;
    params.injectivity = Injectivity::Injective;
    //params.induced = true; // For equals we don't want extra edges unmatched
    params.induced = false; // For equals we don't want extra edges unmatched
    params.bigraph = true;
    params.bigraph_equal = true;
    params.count_solutions = true; // In case the first solution doesn't do the hyperedges properly -- todo constriain this

    params.restarts_schedule = make_unique<NoRestartsSchedule>();

    // ifstream pattern_infile{ pattern_filename };
    // if (! pattern_infile)
    //     throw GraphFileError{ pattern_filename, "unable to open pattern file", false };

    // ifstream target_infile{ target_filename };
    // if (! target_infile)
    //     throw GraphFileError{ target_filename, "unable to open target file", false };

    // We use both as targets for equality checks
    patG = read_target_bigraph(std::stringstream(pattern), "");
    tarG = read_target_bigraph(std::stringstream(target), "");

    if(params.bigraph) {
        //params.enumerate_callback = std::bind(printBigraphMappingBigraphER, graphs, std::placeholders::_1);
        params.enumerate_callback = [&](auto m) {res.mapping.push_back(m);};
    }

    // Additional constraints for equality
    //params.enumerate_callback = std::bind(printBigraphMappingBigraphER, std::placeholders::_1);

    /* Prepare and start timeout */
    params.timeout = make_shared<Timeout>(0s);

    auto result = solve_homomorphism_problem(patG, tarG, params);
}

auto doSearch(std::string pattern, std::string target, bool all) -> void {
    HomomorphismParams params;
    params.injectivity = Injectivity::Injective;
    params.induced = false;
    params.bigraph = true;
    params.count_solutions = all;

    if (all) {
        params.restarts_schedule = make_unique<NoRestartsSchedule>();
    } else {
        params.restarts_schedule = make_unique<LubyRestartsSchedule>(LubyRestartsSchedule::default_multiplier);
    }

    // ifstream pattern_infile{ pattern_filename };
    // if (! pattern_infile)
    //     throw GraphFileError{ pattern_filename, "unable to open pattern file", false };

    // ifstream target_infile{ target_filename };
    // if (! target_infile)
    //     throw GraphFileError{ target_filename, "unable to open target file", false };

    patG = read_pattern_bigraph(std::stringstream(pattern), "");
    tarG = read_target_bigraph(std::stringstream(target), "");

    if(all && params.bigraph) {
        //params.enumerate_callback = std::bind(printBigraphMappingBigraphER, graphs, std::placeholders::_1);
        params.enumerate_callback = [&](auto m) {res.mapping.push_back(m);};
    }

    /* Prepare and start timeout */
    params.timeout = make_shared<Timeout>(0s);

    auto result = solve_homomorphism_problem(patG, tarG, params);

    if(! result.mapping.empty() && !all && params.bigraph) {
        res.mapping.push_back(result.mapping);
    }
}

void gbs_match_all(const char* pat, const char* tar) {
    res.clear();
    doSearch(std::string(pat), std::string(tar), true);
}

void gbs_match_one(const char* pat, const char* tar) {
    res.clear();
    doSearch(std::string(pat), std::string(tar), false);
}

bool gbs_equal(const char* pat, const char* tar) {
    res.clear();
    doEqual(std::string(pat), std::string(tar));
    // Check Interface equality
    if (res.mapping.empty()) {
        return false;
    }
    // Just need one to be equal
    for (auto m : res.mapping) {
        // std::cout << "Sol:\n" << printBigraphMappingBigraphER(m) << std::endl;
        bool failure = false;
        for (auto v : m) {
            if (patG.vertex_name(v.first).find("ROOT") != string::npos) {
                int l = std::stoi(patG.vertex_name(v.first).substr(4));
                int r = std::stoi(tarG.vertex_name(v.second).substr(4));
                if (l != r) { failure = true; break; } // Roots are not identity
            }

            const std::regex linkL { R"(L(\d+)_.*)" };
            const std::regex linkAny { R"((L|C)(\d+)_.*)" };
            std::smatch match;
            if(patG.vertex_label(v.first) == "LINK") {
                int l1, l2;
                std::string str = patG.vertex_name(v.first);
                if (regex_match(str, match, linkL)) {
                    l1 = stoi(match.str(1));

                    str = tarG.vertex_name(v.second);
                    if (regex_match(str, match, linkAny)) {
                        l2 = stoi(match.str(2));
                        if (l1 != l2) { failure = true; break; } // Hyperedge not identity
                    }
                }
            }
        }

        if (!failure) {
            return true;
        }

    }

    return false;
}

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
        if(patG.vertex_name(v.first).find("C_LINK") != string::npos) {
            int k = std::stoi(patG.vertex_name(v.first).substr(7));
            int val = std::stoi(tarG.vertex_name(v.second).substr(7));
            res[k] = val;
        }
    }
    return res;
}


std::map<int, int> gbs_getNodes(const VertexToVertexMapping & mapping) {
    std::map<int, int> res;
    for (auto v : mapping) {
        if(patG.vertex_name(v.first).find("C_LINK") == string::npos
           && patG.vertex_label(v.first) != "LINK") {
            int k = std::stoi(patG.vertex_name(v.first));
            int val = std::stoi(tarG.vertex_name(v.second));
            res[k] = val;
        }
    }
    return res;
}

std::vector<std::pair<int,int>> gbs_getHyp(const VertexToVertexMapping & mapping) {
    std::vector<std::pair<int, int>> res;

    // Combine hyperedges
    const std::regex linkL { R"(L(\d+)_.*)" };
    const std::regex linkAny { R"((L|C)(\d+)_.*)" };
    std::smatch match;

    for (auto v : mapping) {
        if(patG.vertex_label(v.first) == "LINK") {
            std::string str = patG.vertex_name(v.first);
            if (regex_match(str, match, linkL)) {
                int l1 = stoi(match.str(1));

                str = tarG.vertex_name(v.second);
                if (regex_match(str, match, linkAny)) {
                    int l2 = stoi(match.str(2));
                    res.emplace_back(std::make_pair(l1,l2));
                }
            }
        }
    }
    return res;
}
