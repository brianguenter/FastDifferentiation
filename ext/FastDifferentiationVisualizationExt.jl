#*******************************
# To use this visualization software you must install graphviz: https://graphviz.org/.
# You probably don't need to visualize graphs. This is primarily for debugging the FD code.
#*******************************

module FastDifferentiationVisualizationExt
using FastDifferentiation
import FastDifferentiation: make_dot_file, draw_dot, write_dot
using FastDifferentiation: Node, PathEdge, nodes, postorder_number, is_root, is_variable, is_constant, value, unique_edges, top_vertex, bott_vertex, graph, subgraph_edges!, AutomaticDifferentiation, reachable_roots, reachable_variables, node, parent_edges, variable_postorder_to_index, root_postorder_to_index, DerivativeGraph, child_edges, reachability_string
using ElectronDisplay

function label_func(mask::BitVector, label_string::String)
    root_string = ""
    for (i, bvar) in pairs(mask)
        if bvar == 1
            root_string *= "$label_string$i,"
        end
    end
    return root_string
end

function edge_label(a::PathEdge)
    root_string = label_func(reachable_roots(a), "r")
    var_string = label_func(reachable_variables(a), "v")
    return ("$root_string : $var_string")
end


# function draw(unique_edges::AbstractVector{PathEdge{T}}, unique_nodes::AbstractVector{Node{T,N}}, post_order_numbers::AbstractVector{T}, root_test::Function) where {T,N}
# end

function edges_from_node(graph, start_node_number::AbstractVector{Int})
    result = Set{PathEdge}()
    work_queue = Int[]
    for node_num in start_node_number
        pedges = parent_edges(graph, node_num)
        if length(pedges) != 0
            push!(result, pedges...)
        end
    end
    append!(work_queue, start_node_number)
    while length(work_queue) != 0
        curr_node = pop!(work_queue)
        new_edges = child_edges(graph, curr_node)
        if length(new_edges) != 0
            push!(result, new_edges...)
        end
        for edge in new_edges
            if !in(bott_vertex(edge), work_queue)
                push!(work_queue, bott_vertex(edge))
            end
        end
    end
    return collect(result)
end

function make_dot_file(graph, start_nodes::Union{Nothing,AbstractVector{Int}}, label::String, reachability_labels=true, value_labels=false, no_path_edges=false, edge_predicate=(x) -> true)
    if start_nodes !== nothing
        edges_to_draw = edges_from_node(graph, start_nodes)
    else
        edges_to_draw = collect(FastDifferentiation.unique_edges(graph))
    end

    return make_dot_file(graph, edges_to_draw, label, reachability_labels, value_labels, no_path_edges, edge_predicate)

end

function make_dot_file(graph, edges_to_draw::AbstractVector{P}, label::String, reachability_labels=true, value_labels=false, no_path_edges=false, edge_predicate=(x) -> true) where {P<:PathEdge}
    if !no_path_edges #only draw edges on path from root to variable
        edges_to_draw = collect(filter((x) -> any(reachable_variables(x)) && any(reachable_roots(x)), edges_to_draw))
    end

    gr = "digraph{\nnode [style = filled]\n"
    if label != ""
        gr *= "label = \"$label\"\n"
    end
    gr *= "ratio=\"fill\"\n"
    # gr *= "size = 12 12\n"
    gr_copy = deepcopy(graph)

    nodes_to_draw = Set{Node}()
    for e in edges_to_draw
        if edge_predicate(e)
            roots, variables = reachability_string(e)

            edge_label = ""

            chars_to_display = 100
            if value_labels
                srep = "$(value(e)) "
                if length(srep) < chars_to_display
                    edge_label *= "$(value(e)) "
                else
                    edge_label *= srep[1:chars_to_display] * "..."
                end
            end
            if reachability_labels
                edge_label *= "  $roots  $variables"
            end

            if edge_label != ""
                edge_label = "[label = " * "\"" * edge_label * "\"] [color = purple]"
            end


            gr *= "$(top_vertex(e)) -> $(bott_vertex(e)) $edge_label\n"

            push!(nodes_to_draw, node(gr_copy, top_vertex(e)))
            push!(nodes_to_draw, node(gr_copy, bott_vertex(e)))
        end
    end

    for node in nodes_to_draw
        if !(!is_root(gr_copy, node) && length(parent_edges(gr_copy, node)) == 0 && length(child_edges(gr_copy, node)) == 0)
            num = postorder_number(gr_copy, node)
            if is_variable(gr_copy, num)
                gr *= "$num [color = green] [label = \"v$(variable_postorder_to_index(gr_copy,num)) $num $(value(node))\"] [fillcolor = \"#96ff96\"]\n"
            elseif is_root(gr_copy, num)
                gr *= "$num [color = red] [label = \"r$(root_postorder_to_index(gr_copy,num)) $num $(value(node))\"] [fillcolor = \"#ff9696\"]\n"
            elseif is_constant(gr_copy, num)
                gr *= "$num [color = \"#969600\"] [label = \"$num  $(value(node))\"] [fillcolor = \"#ffff00\"]\n"
            else
                gr *= "$num [label = \"$num $(value(node))\"]\n"
            end
        end
    end

    gr *= "\n}"
    return gr
end

function draw_dot(graph::FastDifferentiation.DerivativeGraph, edges_to_draw::AbstractVector{P}; graph_label::String="", reachability_labels=true, value_labels=false, edge_predicate=(x) -> true) where {P}
    gr = make_dot_file(graph, edges_to_draw, graph_label, reachability_labels, value_labels, false, edge_predicate)
    path, io = mktemp(cleanup=true)
    name, ext = splitext(path)
    write_dot(name * ".svg", gr)
    svg = read(name * ".svg", String)
    display("image/svg+xml", svg)
end

function draw_dot(graph::FastDifferentiation.DerivativeGraph; start_nodes::Union{Nothing,AbstractVector{Int}}=nothing, graph_label::String="", reachability_labels=true, value_labels=false, edge_predicate=(x) -> true)
    path, io = mktemp(cleanup=true)
    name, ext = splitext(path)
    write_dot(name * ".svg", graph;
        start_nodes=start_nodes,
        graph_label=graph_label,
        reachability_labels=reachability_labels,
        value_labels=value_labels,
        edge_predicate=edge_predicate)
    svg = read(name * ".svg", String)
    display("image/svg+xml", svg)
end

function draw_dot(subgraph::FastDifferentiation.FactorableSubgraph; graph_label::String="", reachability_labels=true, value_labels=false)
    println("in draw_dot")
    good_subgraph, edges = subgraph_edges(subgraph)
    @assert good_subgraph "subgraph did not have complete paths from dominated vertex to dominating vertex"
    subedges = collect(edges)

    copyedges = similar(subedges, eltype(subedges), 0)
    for edge in subedges
        append!(copyedges, parent_edges(graph(subgraph), edge))
        append!(copyedges, child_edges(graph(subgraph), edge))
    end

    copyedges = unique(copyedges)
    draw_dot(graph(subgraph), copyedges, graph_label=graph_label, reachability_labels=reachability_labels, value_labels=value_labels, edge_predicate=(x) -> true)
end

function write_dot(filename, graph::DerivativeGraph; start_nodes::Union{Nothing,AbstractVector{Int}}=nothing, graph_label::String="", reachability_labels=true, value_labels=false, no_path_edges=false, edge_predicate=(x) -> true)
    gr = make_dot_file(graph, start_nodes, graph_label, reachability_labels, value_labels, no_path_edges, edge_predicate)
    write_dot(filename, gr)
end

function write_dot(filename, graph::DerivativeGraph, edges_to_draw::Vector{PathEdge{T}}; start_nodes::Union{Nothing,AbstractVector{Int}}=nothing, graph_label::String="", reachability_labels=true, value_labels=false, no_path_edges=false, edge_predicate=(x) -> true) where {T}
    gr = make_dot_file(graph, edges_to_draw, graph_label, reachability_labels, value_labels, no_path_edges, edge_predicate)
    write_dot(filename, gr)
end
function write_dot(filename, dot_string::String)
    name, ext = splitext(filename)
    name = name * ".dot"
    ext = ext[2:end] #get rid of leading dot
    io = open(name, "w")
    write(io, dot_string)
    close(io)

    Base.run(`dot -T$ext $name -o $filename`)
end

end #module
