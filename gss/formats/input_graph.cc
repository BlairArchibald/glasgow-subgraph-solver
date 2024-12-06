#include <gss/formats/graph_file_error.hh>
#include <gss/formats/input_graph.hh>

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <iterator>
#include <limits>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <string_view>
#include <type_traits>
#include <vector>

#include <boost/format.hpp>
#include <boost/bimap.hpp>
#include <boost/bimap/unordered_set_of.hpp>
#include <boost/container/allocator.hpp>

using std::back_inserter;
using std::count_if;
using std::distance;
using std::find;
using std::function;
using std::isgraph;
using std::make_optional;
using std::make_pair;
using std::map;
using std::max;
using std::move;
using std::nullopt;
using std::numeric_limits;
using std::optional;
using std::pair;
using std::string;
using std::string_view;
using std::to_string;
using std::transform;
using std::vector;

using Names = boost::bimap<
    boost::bimaps::unordered_set_of<int>,
    boost::bimaps::unordered_set_of<string>,
    boost::container::allocator<pair<int, string>>>;

namespace
{
    auto sanity_check_name(string_view name, const char * const explanation) -> void
    {
        if (0 != count_if(name.begin(), name.end(), [](unsigned char c) { return ! isgraph(c); })) {
            string safe_name;
            transform(name.begin(), name.end(), back_inserter(safe_name), [](unsigned char c) { return isgraph(c) ? c : '?'; });
            throw GraphFileError("Suspicious input detected: " + string(explanation) + " '" + string(safe_name) + "' contains non-printable characters");
        }
    }
}

struct InputGraph::Imp
{
    int size = 0;
    bool has_vertex_labels, has_edge_labels;
    map<pair<int, int>, string> edges;
    vector<string> vertex_labels;
    Names vertex_names;
    bool loopy = false, directed = false;

    // Bigraphs
    int no_link_nodes = 0;

    vector<pair<int, int> > vertex_directed_degrees;
    vector<pair<bool, bool> > vertex_pattern_constraints;

    vector<pair<int, int> > pattern_site_edges;
    vector<pair<int, int> > pattern_root_edges;
};

InputGraph::InputGraph(int size, bool v, bool e) :
    _imp(new Imp{})
{
    _imp->has_vertex_labels = v;
    _imp->has_edge_labels = e;
    _imp->loopy = false;
    _imp->directed = false;

    if (0 != size)
        resize(size);
}

InputGraph::~InputGraph() = default;

InputGraph::InputGraph(InputGraph && other) = default;

auto InputGraph::resize(int size) -> void
{
    _imp->size = size;
    _imp->vertex_labels.resize(size);
    _imp->vertex_pattern_constraints.resize(size);
    _imp->vertex_directed_degrees.resize(size);
}

auto InputGraph::add_edge(int a, int b) -> void
{
    _imp->edges.emplace(make_pair(a, b), "");
    _imp->edges.emplace(make_pair(b, a), "");
    if (a == b)
        _imp->loopy = true;
}

auto InputGraph::add_directed_edge(int a, int b, std::string_view label) -> void
{
    sanity_check_name(label, "edge label");

    _imp->directed = true;

    _imp->edges.emplace(make_pair(a, b), label).first->second = label;

    if (a == b)
        _imp->loopy = true;

    // Bigraphs
    if(vertex_label(a) != "LINK" && vertex_label(b) != "LINK"){
        _imp->vertex_directed_degrees[b].first++;
        _imp->vertex_directed_degrees[a].second++;
    }

    if(vertex_label(a) == "LINK" && vertex_label(b) == "ANCHOR")
        _imp->vertex_directed_degrees[b].first++;
}

auto InputGraph::adjacent(int a, int b) const -> bool
{
    return _imp->edges.count({a, b});
}


auto InputGraph::size() const -> int
{
    return _imp->size;
}

auto InputGraph::number_of_directed_edges() const -> int
{
    return _imp->edges.size();
}

auto InputGraph::add_pattern_site_edge(int a, int b) -> void
{
    _imp->pattern_site_edges.push_back(make_pair(a, b));
}

auto InputGraph::get_pattern_site_edge(int s) const -> pair<int, int>
{
    return _imp->pattern_site_edges[s];
}

auto InputGraph::no_pattern_site_edges() const -> int
{
    return _imp->pattern_site_edges.size();
}


auto InputGraph::add_pattern_root_edge(int a, int b) -> void
{
    _imp->pattern_root_edges.push_back(make_pair(a, b));
}

auto InputGraph::get_pattern_root_edge(int r) const -> pair<int, int>
{
    return _imp->pattern_root_edges[r];
}

auto InputGraph::no_pattern_root_edges() const -> int
{
    return _imp->pattern_root_edges.size();
}

auto InputGraph::add_link_node() -> void
{
    resize(_imp->size+1);
    // set_vertex_label(_size-1, "LINK");
}

auto InputGraph::get_no_link_nodes() const -> int
{
    return _imp->no_link_nodes;
}

auto InputGraph::loopy() const -> bool
{
    return _imp->loopy;
}

auto InputGraph::degree(int a) const -> int
{
    auto lower = _imp->edges.lower_bound({a, 0});
    auto upper = _imp->edges.upper_bound({a, numeric_limits<int>::max()});
    return distance(lower, upper);
}

auto InputGraph::in_degree(int a) const -> int
{
    return _imp->vertex_directed_degrees[a].first;
}

auto InputGraph::out_degree(int a) const -> int
{
    return _imp->vertex_directed_degrees[a].second;
}

auto InputGraph::set_vertex_label(int v, string_view l) -> void
{
    sanity_check_name(l, "vertex label");
    if (l != "") {
        _imp->vertex_labels[v] = l;
    }
    // Bigraphs (TODO: Subclass)
    if (std::string_view(l) == "LINK") { _imp->no_link_nodes++; }
    else if (std::string_view(l) == "ANCHOR") { _imp->no_link_nodes++; }
}

auto InputGraph::vertex_label(int v) const -> string_view
{
    return _imp->vertex_labels[v];
}

auto InputGraph::set_vertex_name(int v, string_view l) -> void
{
    sanity_check_name(l, "vertex name");
    _imp->vertex_names.left.erase(v);
    if (l != "") {
        _imp->vertex_names.insert(Names::value_type{v, string{l}});
    }
}

auto InputGraph::set_child_of_root(int v) -> void
{
    _imp->vertex_pattern_constraints.at(v).first = true;
}

auto InputGraph::set_parent_of_site(int v) -> void
{
    _imp->vertex_pattern_constraints.at(v).second = true;
}

auto InputGraph::get_big_constraint(int v) const -> pair<bool, bool>
{
    return _imp->vertex_pattern_constraints.at(v);
}

auto InputGraph::vertex_name(int v) const -> string
{
    auto it = _imp->vertex_names.left.find(v);
    if (it == _imp->vertex_names.left.end())
        return to_string(v);
    else
        return it->second;
}

auto InputGraph::vertex_from_name(string_view n) const -> optional<int>
{
    auto it = _imp->vertex_names.right.find(string{n});
    if (it == _imp->vertex_names.right.end())
        return nullopt;
    else
        return make_optional(it->second);
}

auto InputGraph::edge_label(int a, int b) const -> string_view
{
    return _imp->edges.find({a, b})->second;
}

auto InputGraph::has_vertex_labels() const -> bool
{
    return _imp->has_vertex_labels;
}

auto InputGraph::has_edge_labels() const -> bool
{
    return _imp->has_edge_labels;
}

auto InputGraph::directed() const -> bool
{
    return _imp->directed;
}

auto InputGraph::for_each_edge(const function<auto(int, int, std::string_view)->void> & c) const -> void
{
    for (auto & [e, l] : _imp->edges)
        c(e.first, e.second, l);
}

auto InputGraph::toString() const -> std::string
{
    std::ostringstream ss;
    ss << (boost::format("Size: %d\n") % _imp->size);
    ss << (boost::format("Vertex Labels: %b\n") % _imp->has_vertex_labels);
    ss << (boost::format("Edge Labels: %b\n") % _imp->has_edge_labels);
    ss << (boost::format("Link nodes: %d\n") % _imp->no_link_nodes);
    ss << (boost::format("Loopy: %b\n") % _imp->loopy);
    ss << (boost::format("Directed: %b\n") % _imp->directed);
    ss << boost::format("Vertex Labels:\n");
    for (const auto & l : _imp->vertex_labels) {
        ss << l << ";";
    }
    ss << boost::format("\nVertex Names:\n");
    for (const auto & l : _imp->vertex_names) {
        ss << l.left << "->" << l.right << ";";
    }
    ss << boost::format("\nEdges: %d\n") % _imp->edges.size();
    for (const auto & l : _imp->edges) {
        auto p = l.first;
        ss << boost::format("[%d-[%s]->%d];") % p.first % l.second % p.second;
    }
    ss << boost::format("\nPattern Root Edges: %d\n") % _imp->pattern_root_edges.size();
    for (const auto & p : _imp->pattern_root_edges) {
        ss << boost::format("[%d-->%d];") % p.first % p.second;
    }
    ss << boost::format("\nPattern Site Edges: %d\n") % _imp->pattern_site_edges.size();
    for (const auto & p : _imp->pattern_site_edges) {
        ss << boost::format("[%d-->%d];") % p.first % p.second;
    }
    ss << boost::format("\nVertex Directed Degrees: %d\n") % _imp->vertex_directed_degrees.size();
    for (const auto & p : _imp->vertex_directed_degrees) {
        ss << boost::format("[%d-->%d];") % p.first % p.second;
    }
    ss << boost::format("\nVertex Pattern Constraints: %d\n") % _imp->vertex_pattern_constraints.size();
    for (const auto & p : _imp->vertex_pattern_constraints) {
        auto x = "F";
        auto y = "F";
        if (p.first) x = "T";
        if (p.second) x = "F";
        ss << boost::format("[%s-->%s];") % x % y;
    }
    ss << "\n";
    return ss.str();
}

/*
auto InputGraph::toDot() const -> std::string
{
    std::ostringstream ss;
    ss << "digraph {";
    for (auto i = 0; i < _imp->size; ++i) {
        ss << format("\n %d [label=\"%s | %s | %d | %d \"]")
            % i
            % _imp->vertex_labels[i]
            % _imp->vertex_names[i]
            % _imp->vertex_directed_degrees[i].first
            % _imp->vertex_directed_degrees[i].second;
    }
    for (const auto & l : _imp->edges) {
        auto p = l.first;
        ss << format("\n%d -> %d") % p.first % p.second;
    }
    ss << "\n}";
    return ss.str();
}
*/
