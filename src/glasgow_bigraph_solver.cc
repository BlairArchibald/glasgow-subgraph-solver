/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "formats/bigraph.hh"
#include "homomorphism.hh"
#include "lackey.hh"
#include "symmetries.hh"
#include "proof.hh"
#include "restarts.hh"

#include <boost/program_options.hpp>

#include <chrono>
#include <cstdlib>
#include <ctime>
#include <exception>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <memory>
#include <vector>
#include <regex>

#include <unistd.h>

namespace po = boost::program_options;

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

auto printBigraphMapping(const std::pair<InputGraph, InputGraph> graphs,
                         const VertexToVertexMapping & mapping) -> void
{
    cout << "mapping = {";
    bool lazy_flag = false;

    for (auto v : mapping) {
        if(graphs.first.vertex_name(v.first).find("C_LINK") != string::npos) break;
        if(graphs.first.vertex_label(v.first) == "LINK") continue;
        if(lazy_flag) cout << ",";
        lazy_flag = true;
        cout << "(" << graphs.first.vertex_name(v.first) << ", " << graphs.second.vertex_name(v.second) << ")";
    }
    cout << "} -- {";

    lazy_flag = false;
    for (auto v : mapping) {
        if(graphs.first.vertex_name(v.first).find("C_LINK") == string::npos) continue;
        if(lazy_flag) cout << ",";
        lazy_flag = true;
        cout << "(" << graphs.first.vertex_name(v.first).substr(7) << ", " << graphs.second.vertex_name(v.second).substr(7) << ")";
    }

    cout << "} -- {";

    lazy_flag = false;
    for (auto v : mapping) {
        if(lazy_flag) cout << ",";
        lazy_flag = true;
        cout << "(" << graphs.first.vertex_name(v.first) << ", " << graphs.second.vertex_name(v.second) << ")";
    }

    cout << "}";
    cout << endl;
}

auto printBigraphMappingBigraphER(const std::pair<InputGraph, InputGraph> graphs,
                                  const VertexToVertexMapping & mapping) -> void
{
    cout << "S" << std::endl;
    for (auto v : mapping) {
        if(graphs.first.vertex_name(v.first).find("C_LINK") != string::npos) {
            cout << "E "
                 << graphs.first.vertex_name(v.first).substr(7) << " "
                 << graphs.second.vertex_name(v.second).substr(7) << std::endl;
        }
        else if(graphs.first.vertex_label(v.first) != "LINK") {
            cout << "N "
                << graphs.first.vertex_name(v.first) << " "
                << graphs.second.vertex_name(v.second) << std::endl;
        }
    }

    // Combine hyperedges for printing
    std::map<int, std::set<int>> hyper_edges;
    const std::regex linkL { R"(L(\d+)_.*)" };
    const std::regex linkAny { R"((L|C)(\d+)_.*)" };
    std::smatch match;

    for (auto v : mapping) {
        int l1, l2;
        if(graphs.first.vertex_label(v.first) == "LINK") {
            std::string str = graphs.first.vertex_name(v.first);
            if (regex_match(str, match, linkL)) {
                l1 = stoi(match.str(1));

                str = graphs.second.vertex_name(v.second);
                if (regex_match(str, match, linkAny)) {
                    l2 = stoi(match.str(2));
                    hyper_edges[l1].insert(l2);
                }
            }
        }
    }

    for (auto & s : hyper_edges) {
        cout << "H " << s.first << " ";
        for (auto & i : s.second) {
              cout << i << " ";
        }
        cout << std::endl;
    }

    cout << "D" << std::endl;
}

auto doEqual(string pattern_filename, string target_filename) -> void {
    HomomorphismParams params;
    params.injectivity = Injectivity::Injective;
    //params.induced = true; // For equals we don't want extra edges unmatched
    params.induced = false; // For equals we don't want extra edges unmatched
    params.bigraph = true;
    params.bigraph_equal = true;
    params.count_solutions = true; // In case the first solution doesn't do the hyperedges properly -- todo constriain this

    params.restarts_schedule = make_unique<LubyRestartsSchedule>(LubyRestartsSchedule::default_multiplier);

    ifstream pattern_infile{ pattern_filename };
    if (! pattern_infile)
        throw GraphFileError{ pattern_filename, "unable to open pattern file", false };

    ifstream target_infile{ target_filename };
    if (! target_infile)
        throw GraphFileError{ target_filename, "unable to open target file", false };

    // We use both as targets for equality checks
    auto graphs = make_pair(
        read_target_bigraph(move(pattern_infile), pattern_filename),
        read_target_bigraph(move(target_infile), target_filename));

    // Additional constraints for equality

    params.enumerate_callback = std::bind(printBigraphMappingBigraphER, graphs, std::placeholders::_1);

    /* Prepare and start timeout */
    params.timeout = make_shared<Timeout>(0s);

    auto result = solve_homomorphism_problem(graphs.first, graphs.second, params);

    if(! result.mapping.empty() && params.bigraph) {
        printBigraphMappingBigraphER(graphs, result.mapping);
    }

}

/* Wrapper to call search in batch mode */
auto doSearch(string pattern_filename, string target_filename, bool all) -> void {
    HomomorphismParams params;
    params.injectivity = Injectivity::Injective;
    params.induced = false;
    params.bigraph = true;
    params.count_solutions = all;

    if (all) {
        params.restarts_schedule = make_unique<NoRestartsSchedule>();
    }
    params.restarts_schedule = make_unique<LubyRestartsSchedule>(LubyRestartsSchedule::default_multiplier);

    ifstream pattern_infile{ pattern_filename };
    if (! pattern_infile)
        throw GraphFileError{ pattern_filename, "unable to open pattern file", false };

    ifstream target_infile{ target_filename };
    if (! target_infile)
        throw GraphFileError{ target_filename, "unable to open target file", false };

    auto graphs = make_pair(
        read_pattern_bigraph(move(pattern_infile), pattern_filename),
        read_target_bigraph(move(target_infile), target_filename));

    if(all && params.bigraph) {
        params.enumerate_callback = std::bind(printBigraphMappingBigraphER, graphs, std::placeholders::_1);
    }

    /* Prepare and start timeout */
    params.timeout = make_shared<Timeout>(0s);

    auto result = solve_homomorphism_problem(graphs.first, graphs.second, params);

    if(! result.mapping.empty() && !all && params.bigraph) {
        printBigraphMappingBigraphER(graphs, result.mapping);
    }
}

auto main(int argc, char * argv[]) -> int
{
    try{
        string input;
        while (std::getline(std::cin, input)) {
            std::istringstream ss(input);
            string pf, tf, all;
            ss >> pf >> tf >> all;
            if (all == "all") {
                doSearch(pf,tf,true);
            } else if (all == "equal") {
                doEqual(pf,tf);
            } else {
                doSearch(pf,tf,false);
            }
            cout << "X" << std::endl;
        }
    }
    catch (const GraphFileError & e) {
        cerr << "Error: " << e.what() << endl;
        return EXIT_FAILURE;
    }
    catch (const po::error & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }
    catch (const exception & e) {
        cerr << "Error: " << e.what() << endl;
        return EXIT_FAILURE;
    }
}
